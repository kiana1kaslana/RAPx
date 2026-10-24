//! Apply contract facts and pointee invariants to symbolic state.

use rustc_middle::{mir::Local, ty::Ty};
use z3::ast::{Ast, Bool, Int};

use crate::{
    compat::FxHashSet,
    verify::contract::{
        ContractExpr, ContractKind, ContractPlace, ContractProjection, PlaceBase, Property,
        PropertyArg, PropertyKind,
    },
};

use super::state::{
    AllocId, ElementTy, ValueSource, OffsetKind, Provenance, ValueFacts, VmState,
    VmValue,
};

use crate::helpers::mir_utils;
use crate::other_api;

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    /// Assert a contract fact as VM state invariants.
    pub(crate) fn assert_contract_fact(&mut self, property: &Property<'tcx>) {
        // Record the allocations named by every `Alias` atom (hazard like
        // `Alias(self, ret)`, or a `Ptr2Ref` precondition like `Alias(self.0)`),
        // so the alias checker discharges only those — not every alias.
        let mut allocs = FxHashSet::default();
        self.collect_alias_hazard_allocs(property, &mut allocs);
        self.alias_hazard_allocs.extend(allocs);
        match property {
            Property::Atom(atom) => {
                if atom.contract_kind == ContractKind::Hazard {
                    return;
                }
                // Assert the atom's own effect, then each of its transitive
                // consequences exactly once (`subsumption_closure` is
                // deduplicated).
                self.assert_atom_direct(property);
                for sub in crate::verify::contract::compound::subsumption_closure(atom) {
                    self.assert_atom_direct(&Property::Atom(sub));
                }
            }
            Property::And(and) => {
                for conj in &and.conjuncts {
                    self.assert_contract_fact(conj);
                }
            }
            Property::Or(or) => {
                // Two guard patterns are materialized by asserting the
                // *non-guard* disjuncts (the guard is vacuous for the case the
                // deref actually runs in):
                //   `any(Null(p), (atoms…))`  — nullable pointer.
                //   `Size(T, 0) || Deref`     — ZST vs non-ZST (`ValidPtr`).
                // A general `Or` without such a guard disjunct is left to the
                // checker (only one disjunct holds, so no fact is sound to
                // assert unconditionally).
                let is_guard = |d: &Property<'tcx>| {
                    matches!(d, Property::Atom(a) if a.kind == PropertyKind::Null || a.kind == PropertyKind::Size)
                };
                if !or.disjuncts.iter().any(is_guard) {
                    return;
                }
                for disj in &or.disjuncts {
                    if is_guard(disj) {
                        continue;
                    }
                    self.assert_contract_fact(disj);
                }
            }
        }
    }

    fn collect_alias_hazard_allocs(
        &self,
        property: &Property<'tcx>,
        out: &mut FxHashSet<AllocId>,
    ) {
        match property {
            Property::Atom(atom) => {
                if atom.kind != PropertyKind::Alias {
                    return;
                }
                let Some(PropertyArg::Expr(ContractExpr::Place(cp))) = atom.args.first() else {
                    return;
                };
                if let Some(alloc_id) = self.place_root_alloc(cp) {
                    out.insert(alloc_id);
                }
            }
            Property::And(and) => {
                for conj in &and.conjuncts {
                    self.collect_alias_hazard_allocs(conj, out);
                }
            }
            Property::Or(or) => {
                for disj in &or.disjuncts {
                    self.collect_alias_hazard_allocs(disj, out);
                }
            }
        }
    }

    fn place_root_alloc(&self, cp: &ContractPlace<'tcx>) -> Option<AllocId> {
        let local = cp.base.to_local();
        let mut field_path: Vec<usize> = Vec::new();
        for proj in &cp.projections {
            match proj {
                ContractProjection::Field { index, .. } => field_path.push(*index),
                _ => return None,
            }
        }
        let val = if field_path.is_empty() {
            self.local_value(local).cloned()
        } else {
            self.field_value(local, &field_path).cloned()
        };
        val.and_then(|v| v.provenance_alloc_id())
            .map(|id| self.root_alloc(id))
    }

    /// Apply a single atom's direct effect (its `match kind` arm), without
    /// recursing into its subsumption consequences.
    fn assert_atom_direct(&mut self, property: &Property<'tcx>) {
        let Property::Atom(atom) = property else {
            return;
        };
        let kind = atom.kind;
        match kind {
            PropertyKind::NonNull => {
                if let Some(val) = self.contract_target_value(property) {
                    self.set_non_null_for_value(property, val);
                }
            }
            PropertyKind::Align => {
                if let Some(val) = self.contract_target_value(property) {
                    self.set_align_for_value(property, val);
                }
                self.record_for_each_align(property);
            }
            PropertyKind::Init => {
                if let Some(val) = self.contract_target_value(property) {
                    self.set_init_for_value(property, val);
                }
            }
            PropertyKind::Owning => {
                if let Some(val) = self.contract_target_value(property) {
                    self.set_owning_for_value(val);
                }
                self.record_for_each_owning(property);
            }
            PropertyKind::Alive => {
                if let Some(id) = self.contract_alloc_id_field_aware(property) {
                    // The region is bound at parse time (`bind_alive_regions`):
                    // struct invariants against the struct, function `requires`
                    // against the function.
                    if let Some(PropertyArg::Region(region)) = property.args().get(1) {
                        self.alloc_mut(id).facts.liveness = Some(*region);
                    }
                }
            }
            PropertyKind::InBound => {
                if let Some(val) = self.contract_target_value(property) {
                    self.set_in_bounds_for_value(property, val);
                }
                if let Some(fe_place) = property.for_each() {
                    self.assert_in_bound_for_each(property, fe_place);
                } else {
                    self.assert_in_bound_single(property);
                }
                // The pointer-and-count form `InBound(p, T, n)` also guarantees
                // the allocation backs `n` elements — materialize that size so a
                // downstream `ptr.add(n)`/`ptr.sub(n)` can discharge `InBound`
                // against a concrete (or `i64::MAX`) size rather than the coarse
                // `in_bounds` flag (which only covers `count == 1`).
                if property.args().len() >= 3 {
                    self.assert_allocated_fact(property);
                }
            }
            PropertyKind::Allocated => {
                self.assert_allocated_fact(property);
                self.record_for_each_allocated(property);
            }
            PropertyKind::Typed => {
                if let Some(val) = self.contract_target_value(property)
                    && let Some(alloc_id) = val.provenance_alloc_id()
                        && let Some(expected_ty) = Self::ty_arg(property, 1) {
                            // A `Typed(container.iter(), T)` *for_each* invariant
                            // declares that the container's pointer elements all
                            // point at valid `T`s. Record that target type so a
                            // single pointer loaded from the container can later
                            // discharge `Typed(ptr, T)` soundly (the fact comes
                            // from the invariant, not from the pointer type).
                            if property.for_each().is_some() {
                                self.alloc_mut(alloc_id).facts.for_each.target_ty = Some(expected_ty);
                            }
                            // Only record the type invariant when the allocation
                            // has no element type yet.  `Init ⇒ Typed` (and other
                            // typed preconditions) may re-assert `Typed` with a
                            // *re-numbered* instantiation of the same `T` (e.g.
                            // `T/#1` vs the `T/#0` used to size the allocation),
                            // which must not clobber the original element type —
                            // doing so makes `len()` fall back to the byte size.
                            if self.alloc(alloc_id).element_ty.is_generic() {
                                self.alloc_mut(alloc_id).element_ty = ElementTy::Typed(expected_ty);
                            }
                        }
            }
            PropertyKind::SplitTransmute => {
                // Anchor the license on the slice's data allocation: the
                // transmute re-interprets *that* allocation's bytes into the
                // destination element type, so `check_split_transmute` finds the
                // license through the receiver slice's provenance.
                let src = Self::ty_arg(property, 0);
                let dst = Self::ty_arg(property, 1);
                if let (Some(src), Some(dst)) = (src, dst) {
                    // `SplitTransmute([T], [U])` licenses re-interpretation into
                    // the *element* type `U` (the `[U]` slice wrapper unwraps).
                    let dst_elem = match dst.kind() {
                        rustc_middle::ty::TyKind::Slice(e) => *e,
                        _ => dst,
                    };
                    // Find the entry parameter whose pointee slice is `src`
                    // (e.g. `slice: &[T]` for `SplitTransmute([T], [U])`) and
                    // mark its data allocation.
                    let arg_count = self.body().arg_count;
                    for local_idx in 1..=arg_count {
                        let local = Local::from_usize(local_idx);
                        if let Some(val) = self.local_value(local).cloned() {
                            let is_match = match val.ty.kind() {
                                rustc_middle::ty::TyKind::Ref(_, inner, _) => *inner == src,
                                _ => false,
                            };
                            if is_match
                                && let Some(prov) = &val.provenance
                            {
                                self.content_mut(prov.alloc_id).facts.split_transmute_to =
                                    Some(dst_elem);
                            }
                        }
                    }
                }
            }
            PropertyKind::ValidCStr => {
                // A `ValidCStr(p, n)` fact guarantees `p` points to a live,
                // initialized, null-terminated byte buffer. Mark the target
                // allocation so the checker can treat it (and any of its
                // sub-slices) as a valid C string, and so pointer reads /
                // `from_raw_parts` over it see a live, initialized allocation.
                //
                // For a `&CStr`-style target the field projection (`inner`)
                // may not be materialised for a DST, so fall back to the base
                // local's own provenance (a `&CStr` reference points directly
                // at the byte buffer it owns).
                let id = self.contract_alloc_id_field_aware(property).or_else(|| {
                    let local = self.contract_target_local(property)?;
                    self.local_value(local)?.provenance_alloc_id()
                });
                if let Some(id) = id {
                    self.alloc_mut(id).facts.dead = false;
                    self.alloc_mut(id).facts.liveness = Some(self.tcx.lifetimes.re_static);
                    self.content_mut(id).facts.initialized = true;
                    self.content_mut(id).facts.cstr_trusted = true;
                    // `ValidCStr(p, n)` carries the byte length of the
                    // nul-terminated buffer.  Assert the allocation covers `n`
                    // bytes so downstream `from_raw_parts(p, n)` / InBound
                    // obligations can be discharged from the exact length
                    // (rather than a conservative `1` placeholder), and
                    // materialize the terminal NUL as a byte-level fact
                    // (`byte[n] == 0`).  A `Const` length (`from_ptr`'s `1`
                    // placeholder) is ignored — the true length is
                    // `strlen(ptr) + 1`.
                    if let Some(n) = property
                        .args()
                        .get(1)
                        .and_then(|a| match a {
                            PropertyArg::Expr(ContractExpr::Const(_)) => None,
                            a => self.resolve_contract_count(a),
                        })
                    {
                        self.constraints.assertions.push(self.alloc(id).size.ge(&n));
                        let zero = Int::from_u64(self.z3_ctx, 0);
                        self.byte_write(id, &n, &zero);
                    }
                }
            }
            PropertyKind::ValidString => {
                // A `ValidString` fact guarantees the target's bytes form a
                // valid UTF-8 sequence.  Mark the backing allocation so the
                // checker can trust it instead of re-running the byte-level
                // DFA.  Unlike `ValidCStr`, UTF-8 validity is a content
                // property, so only content facts are set.
                let id = self.contract_alloc_id_field_aware(property).or_else(|| {
                    // Iterator form (`ValidString(bytes)` with `bytes: &mut I`):
                    // trace the iterator to its backing byte buffer.
                    let local = self.contract_target_local(property)?;
                    let val = self.local_value(local)?.clone();
                    let iter_local = self.find_local_by_address(&val.z3_term)?;
                    self.iter_utf8_buffer(iter_local).map(|(id, _)| id)
                });
                if let Some(id) = id {
                    self.content_mut(id).facts.initialized = true;
                    self.content_mut(id).facts.utf8_trusted = true;
                }
            }
            PropertyKind::ValidNum => {
                if let Some(PropertyArg::Predicates(predicates)) = property.args().first() {
                    for pred in predicates {
                        if let Some(condition) = self.eval_predicate_as_bool(pred) {
                            self.constraints.assertions.push(condition);
                            // For !self.is_empty() → self.len() != 0 on
                            // Iter/IterMut: also assert len >= 1 to help
                            // Z3 with integer division reasoning.
                            if let Some(len_term) = self.try_simple_iter_len_from_pred(pred) {
                                let one = Int::from_u64(self.z3_ctx, 1);
                                self.constraints.assertions.push(len_term.ge(&one));
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }

    /// The `Ty` in a property's `idx`-th `PropertyArg::Ty` argument.
    fn ty_arg(property: &Property<'tcx>, idx: usize) -> Option<Ty<'tcx>> {
        match property.args().get(idx) {
            Some(PropertyArg::Ty(ty)) => Some(*ty),
            _ => None,
        }
    }

    /// Get the local referenced by a contract property's target.
    fn contract_target_local(&self, property: &Property<'tcx>) -> Option<Local> {
        let cp = property.target_place()?;
        Some(cp.base.to_local())
    }

    /// Materialize a fresh external allocation for an `Allocated` contract
    /// fact, returning a value carrying the allocation's provenance.
    /// Mark the target pointer's existing allocation as live (and record its
    /// element type for downstream `Typed` checks).  Returns `true` when the
    /// pointer already carried an allocation, so a fresh external allocation
    /// should *not* be materialized (which would loosen bound checks).
    fn mark_alloc_live_keep(&mut self, val: &VmValue<'z3, 'tcx>, elem_ty: Ty<'tcx>) -> bool {
        let Some(alloc_id) = val.provenance_alloc_id() else {
            return false;
        };
        self.alloc_mut(alloc_id).facts.dead = false;
        // An `Allocated(p, T, n)` contract on a raw-pointer parameter means the
        // caller guarantees the memory is allocated and outlives the call, so
        // it is alive for the function's execution region.
        if self.alloc(alloc_id).is_external() {
            self.alloc_mut(alloc_id).facts.liveness = Some(self.tcx.lifetimes.re_static);
        }
        if self.alloc(alloc_id).element_ty.is_generic() {
            self.alloc_mut(alloc_id).element_ty = ElementTy::Typed(elem_ty);
        }
        true
    }

    fn materialize_external_alloc(
        &mut self,
        elem_ty: Ty<'tcx>,
        count_term: Option<Int<'z3>>,
        val_ty: Ty<'tcx>,
        huge: bool,
    ) -> VmValue<'z3, 'tcx> {
        let elem_sz_raw = self.size_of_ty(elem_ty);
        let heap_align = self.align_sym(elem_ty);
        let heap_align_n = Self::non_trivial_align(heap_align.clone());
        let (heap_id, heap_base) = if huge || elem_sz_raw == 0 {
            // Struct-field targets (and generic element types): use an
            // unbounded external allocation so `Allocated`/`InBound` checks
            // auto-pass regardless of the symbolic element size.
            let max_size = Int::from_u64(self.z3_ctx, i64::MAX as u64);
            self.allocate_external(max_size, heap_align.clone(), Some(elem_ty))
        } else {
            let elem_sz = Int::from_u64(self.z3_ctx, elem_sz_raw);
            let count = count_term.unwrap_or_else(|| Int::from_u64(self.z3_ctx, 1));
            let total = Int::mul(self.z3_ctx, &[&count, &elem_sz]);
            self.allocate_external(total, heap_align, Some(elem_ty))
        };
        self.content_mut(heap_id).facts.initialized = true;
        VmValue {
            z3_term: heap_base,
            ty: val_ty,
            provenance: Some(Provenance {
                alloc_id: heap_id,
                offset: Int::from_u64(self.z3_ctx, 0),
                offset_kind: None,
            }),
            facts: ValueFacts {
                non_null: true,
                init: true,
                in_bounds: true,
                align_n: heap_align_n,
            },
            source: ValueSource::None,
        }
    }

    /// Assert an `Allocated(p, T, n)` contract fact by materializing a fresh
    /// external allocation for the pointer-typed target.
    ///
    /// - For a whole pointer parameter (`src`), the allocation is sized
    ///   `n * sizeof(T)` so downstream pointer arithmetic stays in bounds.
    /// - For a plain pointer *field* (e.g. `RawVecInner::ptr`), the allocation
    ///   is written back to the field via `set_contract_target_value`, and is
    ///   unbounded so field-subrange `InBound` checks auto-pass.
    /// - For `ForEach`/`Downcast` targets (e.g. `buckets.iter()`), the
    ///   container itself is not a pointer — keep the legacy whole-local
    ///   behaviour.
    fn assert_allocated_fact(&mut self, property: &Property<'tcx>) {
        let elem_ty = Self::ty_arg(property, 1);
        let count_term = property
            .args()
            .get(2)
            .and_then(|a| self.resolve_contract_count(a));
        let Some(elem_ty) = elem_ty else { return };

        let has_nonfield = property
            .target_place()
            .map(|cp| {
                cp.projections.iter().any(|p| {
                    !matches!(p, crate::verify::contract::ContractProjection::Field { .. })
                })
            })
            .unwrap_or(false);

        if has_nonfield {
            let Some(local) = self.contract_target_local(property) else {
                return;
            };
            let Some(val) = self.local_value(local).cloned() else {
                return;
            };
            if let Some(alloc_id) = val.provenance_alloc_id() {
                self.alloc_mut(alloc_id).facts.dead = false;
            }
            let v = self.materialize_external_alloc(elem_ty, count_term, val.ty, false);
            self.set_local(local, v);
        } else {
            let Some((local, field_path)) = self.contract_field_path(property) else {
                return;
            };
            if field_path.is_empty() {
                // Whole pointer parameter: exact size.
                let Some(val) = self.local_value(local).cloned() else {
                    return;
                };
                if self.mark_alloc_live_keep(&val, elem_ty) {
                    return;
                }
                let v = self.materialize_external_alloc(elem_ty, count_term, val.ty, false);
                self.set_local(local, v);
            } else {
                // Field target. Only a *direct* pointer field (`NonNull<T>` /
                // `*mut T` / `*const T`) to a *simple* element type (primitive or
                // generic param, e.g. `NonNull<u8>`) carries the allocation
                // itself without a nested field decomposition; a wrapped field
                // (`Option<NonNull>`, `Box`) or a pointer-to-ADT (`NonNull<LeafNode>`,
                // whose fields were decomposed by param init) is handled via the
                // legacy whole-local path to avoid losing those relationships.
                let is_direct_simple_ptr = self.field_value(local, &field_path)
                    .map(|val| {
                        (matches!(val.ty.kind(), rustc_middle::ty::TyKind::RawPtr(..))
                            || matches!(val.ty.kind(), rustc_middle::ty::TyKind::Adt(adt, _)
                                if other_api::is_std_nonnull(adt.did())
                                    || mir_utils::is_raw_ptr_wrapper(self.tcx, adt.did())))
                            && (elem_ty.is_primitive()
                                || matches!(elem_ty.kind(), rustc_middle::ty::TyKind::Param(_)))
                    })
                    .unwrap_or(false);
                let Some(val) = self.field_value(local, &field_path).cloned() else {
                    return;
                };
                if let Some(alloc_id) = val.provenance_alloc_id() {
                    self.alloc_mut(alloc_id).facts.dead = false;
                    if self.alloc(alloc_id).size.as_u64().is_some() {
                        return;
                    }
                }
                // A direct simple pointer field carries the allocation itself; a
                // wrapped field / pointer-to-ADT materializes the *field* target
                // (unbounded via `huge`) so a downstream `Allocated` sees the
                // freshly-sized allocation.
                let mut v =
                    self.materialize_external_alloc(elem_ty, count_term, val.ty, is_direct_simple_ptr);
                // The size materialization must not clobber a *stronger*
                // alignment fact already on the field (e.g. `Align(ptr, usize)`
                // set `align_n = 8`, but `Allocated(ptr, u8, n)` re-materializes
                // with `u8`'s align of 1 → `align_n = None`).
                if v.facts.align_n.is_none() {
                    v.facts.align_n = val.facts.align_n.clone();
                }
                self.set_field_value(local, field_path, v);
            }
        }
    }

    /// Resolve a contract place to `(local, field_path)`. Field projections
    /// are accumulated into `field_path`; `Downcast`/`ForEach` terminate
    /// the path (they unwrap the value in place).
    fn contract_field_path(&self, property: &Property<'tcx>) -> Option<(Local, Vec<usize>)> {
        let cp = property.target_place()?;
        let local = cp.base.to_local();
        let mut path = Vec::new();
        for proj in &cp.projections {
            match proj {
                crate::verify::contract::ContractProjection::Field { index, .. } => {
                    path.push(*index);
                }
                _ => break,
            }
        }
        Some((local, path))
    }

    /// Get the VmValue for a contract property's target, following field
    /// projections so that `Align(self.heap, T)` resolves to the `heap` field
    /// value rather than the whole `self` reference.
    fn contract_target_value(&mut self, property: &Property<'tcx>) -> Option<VmValue<'z3, 'tcx>> {
        let (local, path) = self.contract_field_path(property)?;
        if path.is_empty() {
            self.local_value(local).cloned()
        } else {
            self.field_value(local, &path).cloned()
        }
    }

    /// Write a contract target value back to its (possibly field) location.
    fn set_contract_target_value(&mut self, property: &Property<'tcx>, val: VmValue<'z3, 'tcx>) {
        if let Some((local, path)) = self.contract_field_path(property) {
            if path.is_empty() {
                self.set_local(local, val);
            } else {
                self.set_field_value(local, path, val);
            }
        }
    }

    /// Resolve the alloc_id for a contract property target, following
    /// field projections to locate the actual field value's provenance.
    fn contract_alloc_id_field_aware(&mut self, property: &Property<'tcx>) -> Option<AllocId> {
        let cp = match property.args().first()? {
            PropertyArg::Expr(ContractExpr::Place(cp)) => cp.clone(),
            _ => return None,
        };
        let local = cp.base.to_local();
        let mut field_path: Vec<usize> = Vec::new();
        for proj in &cp.projections {
            match proj {
                crate::verify::contract::ContractProjection::Field { index, .. } => {
                    field_path.push(*index);
                }
                _ => return None,
            }
        }
        if field_path.is_empty() {
            self.local_value(local)?.provenance_alloc_id()
        } else {
            self.field_value(local, &field_path)?.provenance_alloc_id()
        }
    }

    /// Resolve a contract count argument to a Z3 term by looking up
    /// the corresponding function parameter in the VM state.
    fn resolve_contract_count(&self, arg: &PropertyArg<'tcx>) -> Option<Int<'z3>> {
        match arg {
            PropertyArg::Expr(ContractExpr::Const(n)) => Some(Int::from_u64(self.z3_ctx, *n as u64)),
            // Delegate field-projected places and arithmetic (e.g. `cap * elem_size`)
            // to the general simple evaluator.
            PropertyArg::Expr(expr) => self.eval_contract_expr_simple(expr),
            _ => None,
        }
    }

    /// Evaluate a numeric predicate to a Z3 Bool for path-condition assertion.
    fn relop_to_bool(
        &self,
        op: crate::verify::contract::RelOp,
        lhs: &Int<'z3>,
        rhs: &Int<'z3>,
    ) -> Bool<'z3> {
        use crate::verify::contract::RelOp;
        match op {
            RelOp::Eq => lhs._eq(rhs),
            RelOp::Ne => lhs._eq(rhs).not(),
            RelOp::Le => lhs.le(rhs),
            RelOp::Lt => lhs.lt(rhs),
            RelOp::Ge => lhs.ge(rhs),
            RelOp::Gt => lhs.gt(rhs),
        }
    }

    fn eval_predicate_as_bool(
        &self,
        pred: &crate::verify::contract::NumericPredicate<'tcx>,
    ) -> Option<Bool<'z3>> {
        use crate::verify::contract::ContractExpr;
        let lhs = self.eval_contract_expr_simple(&pred.lhs)?;
        let rhs = match &pred.rhs {
            ContractExpr::Const(v) => Int::from_u64(self.z3_ctx, *v as u64),
            _ => self.eval_contract_expr_simple(&pred.rhs)?,
        };
        Some(self.relop_to_bool(pred.op, &lhs, &rhs))
    }

    /// Evaluate a numeric binary operation over two symbolic terms.
    fn eval_numeric_binary(
        &self,
        l: &Int<'z3>,
        r: &Int<'z3>,
        op: crate::verify::contract::NumericBinOp,
    ) -> Option<Int<'z3>> {
        use crate::verify::contract::NumericBinOp;
        Some(match op {
            NumericBinOp::Add => Int::add(self.z3_ctx, &[l, r]),
            NumericBinOp::Sub => Int::sub(self.z3_ctx, &[l, r]),
            NumericBinOp::Mul => Int::mul(self.z3_ctx, &[l, r]),
            NumericBinOp::Div => l.div(r),
            NumericBinOp::Rem => l.rem(r),
            _ => return None,
        })
    }

    fn eval_contract_expr_simple(
        &self,
        expr: &crate::verify::contract::ContractExpr<'tcx>,
    ) -> Option<Int<'z3>> {
        use crate::verify::contract::ContractExpr;
        match expr {
            ContractExpr::SizeOf(ty) => {
                // Symbolic-aware: a generic `T` yields the shared `sizeof_T`
                // (≥ 1) instead of the concrete `1` placeholder, so bounds like
                // `size_of(T) * len <= isize::MAX` match the data allocation's
                // `len·sizeof_T` byte size.  Concrete types still return their
                // real size.
                Some(self.size_sym_read(*ty))
            }
            ContractExpr::Place(cp) => {
                let local = cp.base.to_local();
                let mut path: Vec<usize> = Vec::new();
                for proj in &cp.projections {
                    match proj {
                        crate::verify::contract::ContractProjection::Field { index, .. } => {
                            path.push(*index);
                        }
                        // Downcast / ForEach are not scalar numeric values.
                        _ => return None,
                    }
                }
                if path.is_empty() {
                    self.local_value(local).map(|v| v.z3_term.clone())
                } else {
                    self.field_value(local, &path)
                        .map(|v| v.z3_term.clone())
                        .or_else(|| {
                            // Deref+Field: the base local is a reference whose pointee
                            // fields live in the per-allocation map (e.g. the
                            // `ValidNum(len <= CAPACITY)` invariant on `&LeafNode`
                            // reads `(*leaf).len` through `MemoryContent::values`).
                            let base_val = self.local_value(local)?;
                            let alloc_id = base_val.provenance_alloc_id()?;
                            let view_ty = mir_utils::pointee_ty(base_val.ty)
                                .unwrap_or(base_val.ty);
                            self.units[alloc_id.0].content.values
                                .get(&(view_ty, path.clone()))
                                .map(|v| v.z3_term.clone())
                        })
                }
            }
            ContractExpr::Len(inner) => {
                if let Some(val) = self.eval_contract_expr_simple_value(inner)
                    && let Some(term) = self.try_simple_iter_len(&val) {
                        return Some(term);
                    }
                // A struct (e.g. `NodeRef`) whose `len()` reads `(*x.field).len`
                // through a `NonNull` field.
                if let ContractExpr::Place(cp) = &**inner
                    && let Some(path) = cp.plain_field_path() {
                        let local = cp.base.to_local();
                        if let Some(ty) = self.field_type_at(local, &path)
                            && let Some(term) = self.try_struct_nn_len_field(local, &path, ty) {
                                return Some(term);
                            }
                    }
                let val = self.eval_contract_expr_simple_value(inner)?;
                self.len_from_value(&val)
            }
            ContractExpr::Binary { op, lhs, rhs } => {
                let l = self.eval_contract_expr_simple(lhs)?;
                let r = self.eval_contract_expr_simple(rhs)?;
                self.eval_numeric_binary(&l, &r, *op)
            }
            ContractExpr::Unary { op, expr } => {
                let v = self.eval_contract_expr_simple(expr)?;
                match op {
                    crate::verify::contract::NumericUnaryOp::Neg => {
                        let zero = Int::from_u64(self.z3_ctx, 0);
                        Some(Int::sub(self.z3_ctx, &[&zero, &v]))
                    }
                    crate::verify::contract::NumericUnaryOp::Not => {
                        let zero = Int::from_u64(self.z3_ctx, 0);
                        let one = Int::from_u64(self.z3_ctx, 1);
                        Some(v._eq(&zero).ite(&one, &zero))
                    }
                }
            }
            ContractExpr::Const(n) => Some(Int::from_u64(self.z3_ctx, *n as u64)),
            _ => None,
        }
    }

    fn eval_contract_expr_simple_value(
        &self,
        expr: &crate::verify::contract::ContractExpr<'tcx>,
    ) -> Option<VmValue<'z3, 'tcx>> {
        match expr {
            ContractExpr::Place(cp) => match cp.base {
                PlaceBase::Local(n) => self.local_value(Local::from_usize(n)).cloned(),
                _ => None,
            },
            _ => None,
        }
    }

    /// Try field-based len for Iter/IterMut references (same logic as
    /// `interpreter_iter_len` in call.rs). Used by `eval_contract_expr_simple`
    /// so that ContractFact assertions use the same symbolic term as the
    /// VM execution path.
    fn is_iter_ref(&self, val: &VmValue<'z3, 'tcx>) -> bool {
        use rustc_middle::ty::TyKind;
        match val.ty.kind() {
            TyKind::Ref(_, pointee, _) => match pointee.kind() {
                TyKind::Adt(adt_def, _) => other_api::is_std_iter_or_itermut(adt_def.did()),
                _ => false,
            },
            _ => false,
        }
    }

    /// When `lhs op rhs` compares an iterator's `ptr` and `end_or_len` pointers
    /// (the inlined form of `is_empty`: `ptr == end`), express the comparison
    /// element-wise as `iter_ptr_offset == base_len`. The operands may be plain
    /// temporaries (from the `as_ptr`/cast/field-read lowering), so the iterator
    /// is located via the shared buffer allocation (the `end` field's provenance
    /// alloc id). Returns `None` when this is not an iterator emptiness
    /// comparison.
    pub(crate) fn iter_ptr_comparison(
        &self,
        op: rustc_middle::mir::BinOp,
        lhs: &VmValue<'z3, 'tcx>,
        rhs: &VmValue<'z3, 'tcx>,
    ) -> Option<z3::ast::Bool<'z3>> {
        if !matches!(op, rustc_middle::mir::BinOp::Eq | rustc_middle::mir::BinOp::Ne) {
            return None;
        }
        let lp = lhs.provenance.as_ref()?;
        let rp = rhs.provenance.as_ref()?;
        if lp.alloc_id != rp.alloc_id {
            return None;
        }
        let mut candidates = self
            .constraints
            .term_caches
            .iter_ptr_offset
            .values()
            .filter(|(buffer, _, _)| *buffer == lp.alloc_id);
        let (_, offset, base_len) = candidates.next()?;
        if candidates.next().is_some() {
            return None;
        }
        let is_iter_comparison = self.current_frame.local_alloc.keys().any(|local| {
            let Some((ptr, end)) = self.iter_ptr_end(*local) else {
                return false;
            };
            (ptr.z3_term.simplify() == lhs.z3_term.simplify()
                && end.z3_term.simplify() == rhs.z3_term.simplify())
                || (ptr.z3_term.simplify() == rhs.z3_term.simplify()
                    && end.z3_term.simplify() == lhs.z3_term.simplify())
        });
        if !is_iter_comparison {
            return None;
        }
        let eq = offset._eq(base_len.as_ref()?);
        Some(if matches!(op, rustc_middle::mir::BinOp::Eq) {
            eq
        } else {
            eq.not()
        })
    }

    fn try_simple_iter_len(&self, arg_val: &VmValue<'z3, 'tcx>) -> Option<Int<'z3>> {
        if !self.is_iter_ref(arg_val) {
            return None;
        }
        let local = Local::from_usize(1);
        let ptr = self.field_value(local, &[0])?;
        let end = self.field_value(local, &[1])?;
        self.iter_len_from_ptrs(ptr, end)
    }

    /// For a predicate of the form `self.len() != 0` (i.e. `!self.is_empty()`),
    /// if the self is an Iter/IterMut reference, return the field-based len term
    /// so that a `len >= 1` constraint can be added.
    fn try_simple_iter_len_from_pred(
        &self,
        pred: &crate::verify::contract::NumericPredicate<'tcx>,
    ) -> Option<Int<'z3>> {
        use crate::verify::contract::{ContractExpr, RelOp};
        if !matches!(pred.op, RelOp::Ne) {
            return None;
        }
        if !matches!(&pred.rhs, ContractExpr::Const(0)) {
            return None;
        }
        let ContractExpr::Len(inner) = &pred.lhs else {
            return None;
        };
        let val = self.eval_contract_expr_simple_value(inner)?;
        self.try_simple_iter_len(&val)
    }

    /// If `local` is a reference to Iter/IterMut and field 0 (ptr)
    /// is updated, increment the cumulative ptr offset so that
    /// `interpreter_iter_len` can express `len = initial_len - offset`
    /// instead of nested `(end - (ptr + sz + sz + ...)) / sz`.
    pub(crate) fn track_iter_ptr_update(&mut self, local: Local) {
        let local_val = match self.local_value(local) {
            Some(v) => v,
            None => return,
        };
        if !self.is_iter_ref(local_val) {
            return;
        }
        let Some(iter_local) = self.find_local_by_address(&local_val.z3_term) else {
            return;
        };
        let Some(iter_prov) = local_val.provenance.as_ref() else {
            return;
        };
        let iter_key = (iter_prov.alloc_id, iter_prov.offset.simplify());
        let Some(buffer) = self.iter_buffer(iter_local) else {
            return;
        };
        let one = Int::from_u64(self.z3_ctx, 1);
        let (new_offset, base_len) = match self.constraints.term_caches.iter_ptr_offset.get(&iter_key) {
            Some((_, prev, base)) => (Int::add(self.z3_ctx, &[prev, &one]), base.clone()),
            None => {
                let base = self
                    .field_value(iter_local, &[1])
                    .and_then(|end| end.provenance.as_ref())
                    .and_then(|ep| match &ep.offset_kind {
                        Some(OffsetKind::Element(e)) => Some(e.clone()),
                        _ => None,
                    });
                (one.clone(), base)
            }
        };
        // Mirror `try_iter_next`: the tracked offset must never exceed the
        // iterator's length (the inlined `post_inc_start` body itself only
        // mutates `ptr` and does not assert `offset <= len`).
        if let Some(e) = &base_len {
            self.constraints.assertions.push(new_offset.le(e));
        }
        self.constraints.term_caches.iter_ptr_offset.insert(iter_key, (buffer, new_offset, base_len));
    }

    /// Set non_null invariant on the target value.
    fn set_non_null_for_value(&mut self, property: &Property<'tcx>, mut val: VmValue<'z3, 'tcx>) {
        val.facts.non_null = true;
        self.set_contract_target_value(property, val);
    }

    fn set_in_bounds_for_value(&mut self, property: &Property<'tcx>, mut val: VmValue<'z3, 'tcx>) {
        val.facts.in_bounds = true;
        self.set_contract_target_value(property, val);
    }

    fn assert_in_bound_for_each(
        &mut self,
        property: &Property<'tcx>,
        fe_place: &crate::verify::contract::ContractPlace<'tcx>,
    ) {
        let Some(fe_local) = fe_place.base.try_to_local() else {
            return;
        };
        let fe_val = match self.local_value(fe_local).cloned() {
            Some(v) => v,
            None => return,
        };
        let fe_alloc_id = match fe_val.provenance_alloc_id() {
            Some(id) => id,
            None => return,
        };
        let byte_vals: Vec<(usize, Int<'z3>)> = self.alloc_byte_values(fe_alloc_id);
        if byte_vals.is_empty() {
            return;
        }
        let slice_local = match property.args().first() {
            Some(PropertyArg::Expr(ContractExpr::IndexAccess { slice, .. })) => {
                match slice.as_ref() {
                    ContractExpr::Place(cp) => cp.base.try_to_local(),
                    _ => None,
                }
            }
            Some(PropertyArg::Expr(ContractExpr::Place(cp))) => cp.base.try_to_local(),
            _ => None,
        };
        let slice_val = slice_local.and_then(|loc| self.local_value(loc));
        let slice_alloc_id = slice_val.and_then(|sl_val| sl_val.provenance_alloc_id());
        let data_size = slice_alloc_id.map(|da_id| self.alloc(da_id).size.clone());
        let elem_sz = slice_alloc_id
            .and_then(|da_id| self.alloc(da_id).element_ty.as_ty())
            .map(|ty| self.size_of_ty(ty))
            .unwrap_or(1)
            .max(1);
        let Some(data_size) = data_size else { return };
        let elem_sz_term = Int::from_u64(self.z3_ctx, elem_sz);
        let len = slice_val
            .and_then(|sl_val| self.slice_len_from_value(sl_val))
            .unwrap_or_else(|| data_size.div(&elem_sz_term));
        let zero = Int::from_u64(self.z3_ctx, 0);
        for (_, term) in &byte_vals {
            self.constraints.assertions.push(term.ge(&zero));
            self.constraints.assertions.push(term.lt(&len));
        }
    }

    /// Record the numeric `index < len` bound for a single-index
    /// `InBound(slice, index)`, so a derived index (e.g. `index - 1` guarded by
    /// `index >= 1`) can be discharged by SMT rather than only via the coarse
    /// `in_bounds` flag. Range indices (`start..end`) are left to the checker's
    /// `extract_range_end` (`end <= len`).
    fn assert_in_bound_single(&mut self, property: &Property<'tcx>) {
        let Some(PropertyArg::Expr(ContractExpr::IndexAccess { slice, index })) =
            property.args().first()
        else {
            return;
        };
        if let ContractExpr::Place(index_place) = index.as_ref() {
            let index_local = index_place.base.to_local();
            if let rustc_middle::ty::TyKind::Adt(adt_def, _) =
                self.body().local_decls[index_local].ty.kind()
                && mir_utils::is_range_type(self.tcx, adt_def.did()) {
                    return;
                }
        }
        let slice_local = match slice.as_ref() {
            ContractExpr::Place(cp) => cp.base.try_to_local(),
            _ => None,
        };
        let Some(slice_local) = slice_local else {
            return;
        };
        let Some(da_id) = self
            .local_value(slice_local)
            .and_then(|v| v.provenance_alloc_id())
        else {
            return;
        };
        // Prefer the materialized slice length; fall back to `size / elem_size`
        // for allocations that never got a materialized `slice_len`.
        let len = self
            .slice_len_of_alloc(da_id)
            .unwrap_or_else(|| self.alloc(da_id).size.clone());
        let Some(index_term) = self.eval_contract_expr_simple(index) else {
            return;
        };
        self.constraints.assertions.push(index_term.lt(&len));
    }

    /// When a `&T`/`&mut T` reference is created (e.g. via `&*NonNull<T>`), assume
    /// `T`'s `#[rapx::invariant]`s on the new reference local, rebinding the
    /// invariant's `self` place to that reference. This is what lets a struct's
    /// invariants flow through pointer dereferences into the caller's state.
    pub(crate) fn assert_pointee_struct_invariants(&mut self, dest_ty: Ty<'tcx>, dest_local: Local) {
        let pointee = match dest_ty.kind() {
            rustc_middle::ty::TyKind::Ref(_, inner, _) => *inner,
            _ => return,
        };
        let adt_def = match pointee.kind() {
            rustc_middle::ty::TyKind::Adt(adt_def, _) => *adt_def,
            _ => return,
        };
        let invariants = crate::verify::target::get_struct_invariants_from_annotation(
            self.tcx,
            adt_def.did(),
            adt_def.did(),
        );
        for inv in &invariants {
            let mut rebound = inv.clone();
            rebind_property_place(&mut rebound, dest_local);
            self.assert_contract_fact(&rebound);
        }
    }

    /// Assert a pointee ADT's `#[rapx::invariant]` struct invariants directly
    /// against its materialized per-allocation field values.  This is the
    /// pointer-field analogue of [`assert_pointee_struct_invariants`](Self::
    /// assert_pointee_struct_invariants): that helper covers `&T` references,
    /// while this one covers `NonNull<T>` / `Box<T>` pointer *fields* whose
    /// pointee is decomposed by `init_ptr_field` (e.g. `NodeRef.node:
    /// NonNull<LeafNode>` must satisfy `LeafNode`'s `len <= CAPACITY`).
    pub(crate) fn assert_alloc_pointee_invariants(&mut self, alloc_id: AllocId, pointee_ty: Ty<'tcx>) {
        let rustc_middle::ty::TyKind::Adt(adt_def, _) = pointee_ty.kind() else {
            return;
        };
        let invariants = crate::verify::target::get_struct_invariants_from_annotation(
            self.tcx,
            adt_def.did(),
            adt_def.did(),
        );
        for inv in &invariants {
            let Property::Atom(atom) = inv else {
                continue;
            };
            if atom.kind != PropertyKind::ValidNum {
                continue;
            }
            let Some(PropertyArg::Predicates(preds)) = atom.args.first() else {
                continue;
            };
            for pred in preds {
                if let Some(cond) = self.eval_pointee_predicate_as_bool(alloc_id, pointee_ty, pred)
                {
                    self.constraints.assertions.push(cond);
                }
            }
        }
    }

    /// Evaluate a `ValidNum` predicate against a pointee allocation (not a MIR
    /// local): field places resolve through `MemoryContent::values` keyed by the
    /// pointee type.
    fn eval_pointee_predicate_as_bool(
        &self,
        alloc_id: AllocId,
        view_ty: Ty<'tcx>,
        pred: &crate::verify::contract::NumericPredicate<'tcx>,
    ) -> Option<Bool<'z3>> {
        let lhs = self.eval_pointee_expr(alloc_id, view_ty, &pred.lhs)?;
        let rhs = self.eval_pointee_expr(alloc_id, view_ty, &pred.rhs)?;
        Some(self.relop_to_bool(pred.op, &lhs, &rhs))
    }

    /// Evaluate a numeric `ContractExpr` against a pointee allocation.
    fn eval_pointee_expr(
        &self,
        alloc_id: AllocId,
        view_ty: Ty<'tcx>,
        expr: &ContractExpr<'tcx>,
    ) -> Option<Int<'z3>> {
        match expr {
            ContractExpr::Const(v) => Some(Int::from_u64(self.z3_ctx, *v as u64)),
            ContractExpr::SizeOf(ty) => Some(self.size_sym_read(*ty)),
            ContractExpr::AlignOf(ty) => Some(self.align_sym_read(*ty)),
            ContractExpr::Place(cp) => {
                let path = cp.plain_field_path()?;
                self.units[alloc_id.0].content.values
                    .get(&(view_ty, path))
                    .map(|v| v.z3_term.clone())
            }
            ContractExpr::Binary { op, lhs, rhs } => {
                let l = self.eval_pointee_expr(alloc_id, view_ty, lhs)?;
                let r = self.eval_pointee_expr(alloc_id, view_ty, rhs)?;
                self.eval_numeric_binary(&l, &r, *op)
            }
            ContractExpr::Len(inner) => {
                let val = self.eval_pointee_expr_value(alloc_id, view_ty, inner)?;
                self.slice_len_from_value(&val)
            }
            _ => None,
        }
    }

    /// Resolve a `Place` (or `Len` inner) against a pointee allocation, returning
    /// the materialized `VmValue` so slice-length fallbacks can read provenance.
    fn eval_pointee_expr_value(
        &self,
        alloc_id: AllocId,
        view_ty: Ty<'tcx>,
        expr: &ContractExpr<'tcx>,
    ) -> Option<VmValue<'z3, 'tcx>> {
        let ContractExpr::Place(cp) = expr else {
            return None;
        };
        let path = cp.plain_field_path()?;
        self.units[alloc_id.0].content.values
            .get(&(view_ty, path))
            .cloned()
    }

    /// Set align invariant on the target value.
    fn set_align_for_value(&mut self, property: &Property<'tcx>, mut val: VmValue<'z3, 'tcx>) {
        if let Some(PropertyArg::Ty(ty)) = property.args().get(1) {
            let align = self.align_sym(*ty);
            let align_u64 = align.simplify().as_u64();
            if align_u64 != Some(1) {
                val.facts.align_n = Some(align.clone());
                // For a *concrete* alignment, also record `term % align == 0` as a
                // path condition.  `align_n` is a value invariant that pointer
                // arithmetic (`ptr.add(n)`) drops, but the alignment fact itself
                // persists: a downstream `Align(p, T)` on `p = ptr.add(n)` can then
                // combine `term % align == 0` with the `n % align == 0` mask fact to
                // prove `p % align == 0`.  (A symbolic `align_T` is skipped — the
                // non-linear `% align_T` is not decidable, so `align_n` alone is
                // used for that case.)
                if align_u64.is_some() {
                    self.constraints.assertions.push(
                        val.z3_term
                            .rem(&align)
                            ._eq(&Int::from_u64(self.z3_ctx, 0)),
                    );
                }
            }
        }
        self.set_contract_target_value(property, val);
    }

    /// Set init invariant on the target value and its allocation.
    fn set_init_for_value(&mut self, property: &Property<'tcx>, val: VmValue<'z3, 'tcx>) {
        // `Init(p, MaybeUninit<T>, n)` reduces to `Typed(p, MaybeUninit<T>)`: the
        // content carries no validity invariant, so there is nothing to mark
        // initialized — the `Init ⇒ Typed` subsumption records the element type.
        let is_maybe_uninit = Self::ty_arg(property, 1)
            .map(other_api::is_maybe_uninit_ty)
            .unwrap_or(false);
        if is_maybe_uninit {
            return;
        }
        if let Some(prov) = &val.provenance {
            self.content_mut(prov.alloc_id).facts.initialized = true;
        }
        if let Some((local, path)) = self.contract_field_path(property) {
            let existing = if path.is_empty() {
                self.local_value(local).cloned()
            } else {
                self.field_value(local, &path).cloned()
            };
            if let Some(mut existing) = existing {
                self.mark_initialized(&mut existing);
                if path.is_empty() {
                    self.set_local(local, existing);
                } else {
                    self.set_field_value(local, path, existing);
                }
            }
        }
    }

    /// Set owning invariant on the target value.
    fn set_owning_for_value(&mut self, val: VmValue<'z3, 'tcx>) {
        if let Some(prov) = &val.provenance {
            self.content_mut(prov.alloc_id).facts.initialized = true;
        }
    }

    /// Record the `Align(container.iter(), T)` for_each fact: every element
    /// pointer is aligned to `align_of(T)`.  Anchored to the container
    /// allocation so a pointer loaded from it can discharge `Align(cur, T)`.
    fn record_for_each_align(&mut self, property: &Property<'tcx>) {
        if property.for_each().is_none() {
            return;
        }
        let Some(ty) = property.args().get(1).and_then(|a| match a {
            PropertyArg::Ty(ty) => Some(*ty),
            _ => None,
        }) else {
            return;
        };
        let Some(alloc_id) = self.contract_target_value(property).and_then(|v| v.provenance_alloc_id())
        else {
            return;
        };
        self.alloc_mut(alloc_id).facts.for_each.aligned_ty = Some(ty);
    }

    /// Record the `Allocated(container.iter(), T, n)` for_each fact: every
    /// element pointer backs `>= n` `T` elements (`n` may be symbolic).
    fn record_for_each_allocated(&mut self, property: &Property<'tcx>) {
        if property.for_each().is_none() {
            return;
        }
        let Some(ty) = property.args().get(1).and_then(|a| match a {
            PropertyArg::Ty(ty) => Some(*ty),
            _ => None,
        }) else {
            return;
        };
        let count = property
            .args()
            .get(2)
            .and_then(|a| self.resolve_contract_count(a))
            .unwrap_or_else(|| Int::from_u64(self.z3_ctx, 1));
        let Some(alloc_id) = self.contract_target_value(property).and_then(|v| v.provenance_alloc_id())
        else {
            return;
        };
        self.alloc_mut(alloc_id).facts.for_each.allocated = Some((ty, count));
    }

    /// Record the `Owning(container.iter())` for_each fact: every element
    /// pointer is the sole owner of its pointee.  Anchored to the container
    /// allocation so a pointer loaded from it can discharge `Owning(cur)`.
    fn record_for_each_owning(&mut self, property: &Property<'tcx>) {
        if property.for_each().is_none() {
            return;
        }
        let Some(alloc_id) = self.contract_target_value(property).and_then(|v| v.provenance_alloc_id())
        else {
            return;
        };
        self.alloc_mut(alloc_id).facts.for_each.owning = true;
    }

}

/// Rebind every `self` place in a struct invariant to the given MIR local, so
/// an invariant parsed against the struct's own `self` can be asserted on a
/// freshly-created reference (`&*NonNull<T>` → `&T`).
fn rebind_property_place<'tcx>(property: &mut Property<'tcx>, local: Local) {
    match property {
        Property::Atom(atom) => {
            for arg in &mut atom.args {
                match arg {
                    PropertyArg::Expr(expr) => rebind_expr_place(expr, local),
                    PropertyArg::Predicates(preds) => {
                        for pred in preds {
                            rebind_expr_place(&mut pred.lhs, local);
                            rebind_expr_place(&mut pred.rhs, local);
                        }
                    }
                    _ => {}
                }
            }
        }
        Property::And(and) => {
            for c in &mut and.conjuncts {
                rebind_property_place(c, local);
            }
        }
        Property::Or(or) => {
            for d in &mut or.disjuncts {
                rebind_property_place(d, local);
            }
        }
    }
}

fn rebind_expr_place<'tcx>(expr: &mut ContractExpr<'tcx>, local: Local) {
    match expr {
        ContractExpr::Place(cp) => {
            cp.base = PlaceBase::Local(local.as_usize());
        }
        ContractExpr::Len(inner) => rebind_expr_place(inner, local),
        ContractExpr::IndexAccess { slice, index } => {
            rebind_expr_place(slice, local);
            rebind_expr_place(index, local);
        }
        ContractExpr::Binary { lhs, rhs, .. } => {
            rebind_expr_place(lhs, local);
            rebind_expr_place(rhs, local);
        }
        ContractExpr::Unary { expr: inner, .. } => rebind_expr_place(inner, local),
        ContractExpr::If {
            cond,
            then_expr,
            else_expr,
        } => {
            rebind_expr_place(&mut cond.lhs, local);
            rebind_expr_place(&mut cond.rhs, local);
            rebind_expr_place(then_expr, local);
            rebind_expr_place(else_expr, local);
        }
        _ => {}
    }
}
