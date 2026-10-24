//! Execute retained path items in the symbolic VM.

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        Local, Operand, Place, Rvalue, StatementKind,
    },
    ty::Ty,
};
use z3::ast::{Ast, Int};

use crate::{
    compat::FxHashSet,
    verify::slicer::RelevantItem,
};

use super::state::{
    AllocId, ValueSource, Provenance, ValueFacts, VmState,
    VmValue,
};

use crate::helpers::mir_utils;
use crate::other_api;

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    /// Execute all retained MIR items in path order.
    pub(crate) fn execute_items(&mut self, items: &[RelevantItem<'tcx>]) {
        // Initialize function parameters as fresh symbolic values.
        // Parameters are _1.._N (excluding _0 return value).
        self.init_parameters();

        for item in items {
            match item {
                RelevantItem::Statement {
                    def_id,
                    block,
                    statement_index,
                } => {
                    let body = self.tcx.optimized_mir(*def_id);
                    let statement = &body.basic_blocks[*block].statements[*statement_index];
                    crate::verify::vm::rules::exec_statement(self, statement);
                }
                RelevantItem::Terminator { def_id, block, switch_succ } => {
                    let body = self.tcx.optimized_mir(*def_id);
                    let terminator = body.basic_blocks[*block].terminator();
                    crate::verify::vm::rules::exec_terminator(self, terminator, *switch_succ);
                }
                RelevantItem::CalleeEntry { callee, args, consts, field_offsets } => {
                    self.handle_callee_entry(*callee, args, consts, field_offsets);
                }
                RelevantItem::CalleeExit { dest } => {
                    self.handle_callee_exit(*dest);
                }
                RelevantItem::ContractFact { property } => {
                    self.assert_contract_fact(property);
                }
            }
        }
    }

    /// Enter an inlined callee during path execution: save the caller context,
    /// switch to the callee body, and bind the caller's argument locals to the
    /// callee's parameters.
    fn handle_callee_entry(&mut self, callee: DefId, arg_locals: &[usize], arg_consts: &[(usize, u64)], arg_field_offsets: &[usize]) {
        let arg_referents: Vec<Option<Local>> = arg_locals
            .iter()
            .map(|arg| {
                self.local_value(Local::from_usize(*arg))
                    .and_then(|value| self.find_local_by_address(&value.z3_term))
            })
            .collect();
        let saved_referents = std::mem::replace(&mut self.inline.arg_referents, arg_referents);
        self.inline.path_saved_arg_referents.push(saved_referents);
        let saved_writes = std::mem::take(&mut self.inline.deferred_field_writes);
        self.inline.path_saved_deferred_writes.push(saved_writes);
        let frame = self.save_frame();

        // Collect the caller argument fields from the saved map, so the callee's
        // parameters inherit them (e.g. NonZero's non-zero inner value, and an
        // iterator's `ptr`/`end_or_len`). A whole-place reborrow
        // (`_7 = &mut (*_1)`) carries its referent's fields, so resolve it too;
        // likewise a whole-place copy temporary (`_2 = copy _1`) that the
        // optimizer inserted between the caller's argument and the inlined
        // callee's parameter — follow both chains so the local that actually
        // materialized the fields is found.
        let mut arg_fields: Vec<(usize, Vec<usize>, VmValue<'z3, 'tcx>)> = Vec::new();
        for (i, arg) in arg_locals.iter().enumerate() {
            let caller_local = Local::from_usize(*arg);
            let mut source_locals: Vec<(Local, Vec<usize>)> = Vec::new();
            let mut seen: FxHashSet<(Local, Vec<usize>)> = FxHashSet::default();
            let mut stack = vec![(caller_local, Vec::new())];
            while let Some((cur, prefix)) = stack.pop() {
                if !seen.insert((cur, prefix.clone())) {
                    continue;
                }
                source_locals.push((cur, prefix.clone()));
                if let Some(r) = self.find_whole_reborrow_referent(cur) {
                    stack.push((r, prefix.clone()));
                }
                if let Some((r, fields)) = self.find_field_reborrow_referent(cur) {
                    let mut new_prefix = prefix.clone();
                    new_prefix.extend(fields);
                    stack.push((r, new_prefix));
                }
                if let Some(c) = self.find_copy_root(cur) {
                    stack.push((c, prefix.clone()));
                }
            }
            for (src, prefix) in source_locals {
                let keys: Vec<Vec<usize>> = self
                    .frame_field_paths(&frame, src)
                    .into_iter()
                    .filter(|f| {
                        prefix.is_empty()
                            || (f.len() >= prefix.len() && f[..prefix.len()] == prefix[..])
                    })
                    .collect();
                for fields in keys {
                    if let Some(fv) = self.frame_field_value(&frame, src, &fields).cloned() {
                        let stripped = if prefix.is_empty() {
                            fields
                        } else {
                            fields[prefix.len()..].to_vec()
                        };
                        arg_fields.push((i + 1, stripped, fv));
                    }
                }
            }
        }

        self.current_frame.current_def_id = callee;

        for (i, arg) in arg_locals.iter().enumerate() {
            if let Some(v) = self.frame_local_value(&frame, Local::from_usize(*arg)).cloned() {
                self.set_local(Local::from_usize(i + 1), v);
            }
        }

        // Bind `Const` arguments (which have no local) to their literal value,
        // so a fresh symbolic param does not leak into pointer arithmetic (e.g.
        // `ptr.add(1)`'s `count == 1` must stay concrete for `InBound`).
        for &(param, val) in arg_consts {
            let local = Local::from_usize(param);
            let ty = self.body().local_decls[local].ty;
            self.set_local(local, VmValue::new(Int::from_u64(self.z3_ctx, val), ty));
        }

        // Bind `offset_of!` const arguments as a symbolic `FieldOffset` value,
        // preserving the field-offset marker so pointer arithmetic keeps
        // `offset_kind == Field` and downstream `Align` stays dischargeable.
        for &param in arg_field_offsets {
            let local = Local::from_usize(param);
            let ty = self.body().local_decls[local].ty;
            self.set_local(
                local,
                VmValue {
                    z3_term: self.fresh_int("field_offset"),
                    ty,
                    provenance: None,
                    facts: ValueFacts::default(),
                    source: ValueSource::FieldOffset,
                },
            );
        }

        for (callee_param, fields, fv) in arg_fields {
            self.set_field_value(Local::from_usize(callee_param), fields, fv);
        }

        self.caller_frames.push(frame);
    }

     /// Exit an inlined callee: capture the callee's return value, restore the
     /// caller context, and write the return value to the caller's destination.
    fn handle_callee_exit(&mut self, dest: usize) {
        let ret = self.local_value(Local::from_usize(0)).cloned();
        let ret_fields: Vec<(Vec<usize>, VmValue<'z3, 'tcx>)> = self
            .field_paths(Local::from_usize(0))
            .into_iter()
            .filter_map(|f| {
                self.field_value(Local::from_usize(0), &f)
                    .cloned()
                    .map(|v| (f, v))
            })
            .collect();
        if let Some(frame) = self.caller_frames.pop() {
            self.restore_frame(frame);
        }
        let writes = std::mem::take(&mut self.inline.deferred_field_writes);
        self.inline.arg_referents = self.inline.path_saved_arg_referents.pop().unwrap_or_default();
        self.inline.deferred_field_writes = self
            .inline
            .path_saved_deferred_writes
            .pop()
            .unwrap_or_default();
        self.replay_deferred_writes(writes);
        if let Some(mut v) = ret {
            let dest_ty = self.body().local_decls[Local::from_usize(dest)].ty;
            v.ty = dest_ty;
            // Infer facts: a non-null provenance with offset 0 means the
            // return value is valid and initialized.
            let at_base = v
                .provenance
                .as_ref()
                .is_some_and(|p| p.offset.as_u64() == Some(0));
            if at_base {
                v.facts.non_null = true;
                self.mark_initialized(&mut v);
            }
            self.set_local(Local::from_usize(dest), v);
            // The callee returned a fully-constructed value, so the caller's
            // destination stack slot is initialized.
            if let Some(dest_alloc_id) = self.current_frame.local_alloc.get(&Local::from_usize(dest)).copied()
            {
                self.content_mut(dest_alloc_id).facts.initialized = true;
            }
        }
        for (fields, fv) in ret_fields {
            self.set_field_value(Local::from_usize(dest), fields, fv);
        }
    }

    /// The slice/array element count for an allocation: the materialized
    /// `slice_len`, or `size / elem_size` as a fallback for allocations created
    /// before materialization (e.g. some call effects).  Uses the symbolic
    /// element size (`size_sym_read`) so `len = (len·S) / S` cancels to `len`
    /// for a generic element type — mirroring `set_len_from_alloc`.  Returns
    /// `None` when the element type is unknown.
    pub(crate) fn slice_len_of_alloc(&self, alloc_id: AllocId) -> Option<Int<'z3>> {
        let alloc = self.alloc(alloc_id);
        if let Some(len) = alloc.slice_len() {
            return Some(len.clone());
        }
        let elem_ty = alloc.element_ty.as_ty()?;
        let elem_term = self.size_sym_read(elem_ty);
        if elem_term.simplify().as_u64() == Some(1) {
            return Some(alloc.size.clone());
        }
        Some(alloc.size.div(&elem_term))
    }

    /// The slice length of a `&[T]` / `&mut [T]` value, resolved through its
    /// provenance allocation (see [`Self::slice_len_of_alloc`]).
    pub(crate) fn slice_len_from_value(&self, val: &VmValue<'z3, 'tcx>) -> Option<Int<'z3>> {
        self.slice_len_of_alloc(val.provenance_alloc_id()?)
    }

    /// Resolve `x.len()` for a pointer whose pointee ADT carries a `len` field
    /// (e.g. `NodeRef<LeafNode>`: `len()` reads `(*ptr).len`).  Returns the
    /// pointee's `len` field term, or `None` when the pointee has no such field.
    pub(crate) fn try_adt_len_field(&self, val: &VmValue<'z3, 'tcx>) -> Option<Int<'z3>> {
        let alloc_id = val.provenance_alloc_id()?;
        let elem_ty = self.alloc(alloc_id).element_ty.as_ty()?;
        self.try_adt_len_field_at(alloc_id, elem_ty, elem_ty, &[])
    }

    /// Resolve a `len` field on `ty`, recursing into ADT sub-fields when there is
    /// no direct `len` (e.g. `String { vec: Vec { ptr, len, cap } }` resolves
    /// `String.len()` to `vec.len`).  `root_ty` stays fixed as the allocation's
    /// element type, which is how `decompose_pointee_fields` keys `MemoryContent::values`.
    fn try_adt_len_field_at(
        &self,
        alloc_id: AllocId,
        ty: Ty<'tcx>,
        root_ty: Ty<'tcx>,
        prefix: &[usize],
    ) -> Option<Int<'z3>> {
        let rustc_middle::ty::TyKind::Adt(adt_def, substs) = ty.kind() else {
            return None;
        };
        if !adt_def.is_struct() {
            return None;
        }
        let variant = adt_def.non_enum_variant();
        if let Some(len_idx) = variant
            .fields
            .iter()
            .position(|f| f.ident(self.tcx).name.to_string() == "len")
        {
            let mut path = prefix.to_vec();
            path.push(len_idx);
            return self.units[alloc_id.0].content.values
                .get(&(root_ty, path))
                .map(|v| v.z3_term.clone());
        }
        for (idx, field_def) in variant.fields.iter().enumerate() {
            let field_ty = mir_utils::field_ty(self.tcx, field_def, substs);
            if matches!(field_ty.kind(), rustc_middle::ty::TyKind::Adt(_, _)) {
                let mut path = prefix.to_vec();
                path.push(idx);
                if let Some(len) = self.try_adt_len_field_at(alloc_id, field_ty, root_ty, &path) {
                    return Some(len);
                }
            }
        }
        None
    }

    /// Resolve `len()` for `core::ops::IndexRange` (a private `{ start, end }`
    /// struct): `len() = end - start`.  The `len` field lookup above misses it
    /// because `IndexRange` has no `len` field — its `len()` computes the
    /// difference of its two private fields.
    pub(crate) fn try_index_range_len(&self, val: &VmValue<'z3, 'tcx>) -> Option<Int<'z3>> {
        let rustc_middle::ty::TyKind::Adt(adt_def, _) = val.ty.kind() else {
            return None;
        };
        if !other_api::is_index_range(adt_def.did()) {
            return None;
        }
        let alloc_id = val.provenance_alloc_id()?;
        let view_ty = mir_utils::pointee_ty(val.ty).unwrap_or(val.ty);
        let start = self
            .units[alloc_id.0].content.values
            .get(&(view_ty, vec![0]))?
            .z3_term
            .clone();
        let end = self
            .units[alloc_id.0].content.values
            .get(&(view_ty, vec![1]))?
            .z3_term
            .clone();
        Some(Int::sub(self.z3_ctx, &[&end, &start]))
    }

    /// Resolve `len()` of a slice/ADT value: the pointee ADT's `len` field, then
    /// the materialized slice length, then `size / elem_size`.  Shared by the
    /// exec- and checker-side `Len` evaluators so the fallback chain is defined
    /// once.
    pub(crate) fn len_from_value(&self, val: &VmValue<'z3, 'tcx>) -> Option<Int<'z3>> {
        if let Some(len) = self.try_adt_len_field(val) {
            return Some(len);
        }
        if let Some(len) = self.try_index_range_len(val) {
            return Some(len);
        }
        self.slice_len_from_value(val)
    }

    /// Resolve `x.len()` for a struct `x` (e.g. `NodeRef`) whose `len()` method
    /// reads `(*x.field).len` through a `NonNull`/raw-pointer field.  Follows
    /// that field to its pointee allocation and reads the pointee's `len` field.
    pub(crate) fn try_struct_nn_len_field(
        &self,
        local: Local,
        field_path: &[usize],
        ty: Ty<'tcx>,
    ) -> Option<Int<'z3>> {
        let rustc_middle::ty::TyKind::Adt(adt_def, substs) = ty.kind() else {
            return None;
        };
        if !adt_def.is_struct() {
            return None;
        }
        let variant = adt_def.non_enum_variant();
        let mut found: Option<(usize, Ty<'tcx>)> = None;
        for (idx, field_def) in variant.fields.iter().enumerate() {
            let fty = mir_utils::field_ty(self.tcx, field_def, substs);
            if let Some(pointee) = self.find_nn_pointee(fty) {
                found = Some((idx, pointee));
                break;
            }
        }
        let (nn_idx, pointee) = found?;
        let mut path = field_path.to_vec();
        path.push(nn_idx);
        let nn_val = self.field_value(local, &path)?;
        let alloc_id = nn_val.provenance_alloc_id()?;
        let rustc_middle::ty::TyKind::Adt(pointee_adt, _) = pointee.kind() else {
            return None;
        };
        let pvariant = pointee_adt.non_enum_variant();
        let len_idx = pvariant
            .fields
            .iter()
            .position(|f| f.ident(self.tcx).name.to_string() == "len")?;
        self.units[alloc_id.0].content.values
            .get(&(pointee, vec![len_idx]))
            .map(|v| v.z3_term.clone())
    }

    /// Resolve the type of a place (`local` + field path) by walking the ADT
    /// field definitions.
    pub(crate) fn field_type_at(&self, local: Local, field_path: &[usize]) -> Option<Ty<'tcx>> {
        let mut ty = self.body().local_decls[local].ty;
        for &idx in field_path {
            let rustc_middle::ty::TyKind::Adt(adt_def, substs) = ty.kind() else {
                return None;
            };
            let variant = adt_def.non_enum_variant();
            let field_def = variant.fields.get(rustc_abi::FieldIdx::from_usize(idx))?;
            ty = mir_utils::field_ty(self.tcx, field_def, substs);
        }
        Some(ty)
    }

    /// Extract the pointee type if `ty` is a `#[repr(transparent)]`
    /// single-field raw-pointer wrapper (`NonNull<P>`) or wrapped in
    /// `Option<NonNull<P>>`. Returns `Some(P)`.
    ///
    /// Detected structurally (via `#[repr(transparent)]` + a raw-pointer field)
    /// rather than by name, so re-implemented std types in the challenge
    /// suites are modelled identically to their std counterparts.
    pub(crate) fn find_nn_pointee(&self, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
        use rustc_middle::ty::TyKind;
        match ty.kind() {
            TyKind::Adt(adt_def, substs) => {
                if let Some(pointee) = self.transparent_ptr_pointee(adt_def, substs) {
                    return Some(pointee);
                }
                if self
                    .tcx
                    .is_diagnostic_item(rustc_span::sym::Option, adt_def.did())
                    && let Some(inner) = substs.first().and_then(|s| s.as_type())
                        && let TyKind::Adt(ia, is_) = inner.kind() {
                            return self.transparent_ptr_pointee(ia, is_);
                        }
                None
            }
            _ => None,
        }
    }

    /// Pointee type of a `#[repr(transparent)]` single-field raw-pointer
    /// wrapper such as `NonNull<T>` (`struct NonNull<T> { pointer: *const T }`).
    fn transparent_ptr_pointee(
        &self,
        adt_def: &rustc_middle::ty::AdtDef,
        substs: rustc_middle::ty::GenericArgsRef<'tcx>,
    ) -> Option<Ty<'tcx>> {
        if !adt_def.repr().transparent() {
            return None;
        }
        let field = adt_def.non_enum_variant().fields.iter().next()?;
        let field_ty = mir_utils::field_ty(self.tcx, field, substs);
        match field_ty.kind() {
            rustc_middle::ty::TyKind::RawPtr(pointee, _) => Some(*pointee),
            // NonNull's field is a pattern type `*const T is !null` on newer
            // toolchains; unwrap it to the underlying raw pointer.
            rustc_middle::ty::TyKind::Pat(inner, _) => match inner.kind() {
                rustc_middle::ty::TyKind::RawPtr(pointee, _) => Some(*pointee),
                _ => None,
            },
            _ => None,
        }
    }

    /// Whether `ty` is a `#[repr(transparent)]` newtype (a single non-zero-sized
    /// field whose value *is* that field, e.g. `MaybeUninit<T>`, `ManuallyDrop<T>`,
    /// `Wrapping<T>`, `NonNull<T>`).  Construction and field reads are modelled
    /// transparently: the wrapper value is the field value itself.
    pub(crate) fn is_transparent_newtype(&self, ty: Ty<'tcx>) -> bool {
        match ty.kind() {
            rustc_middle::ty::TyKind::Adt(adt_def, _) => adt_def.repr().transparent(),
            _ => false,
        }
    }

    pub(crate) fn container_ptr_field(&self, ty: Ty<'tcx>) -> Option<Vec<usize>> {
        self.container_ptr_field_inner(ty, Vec::new(), 0)
    }

    fn container_ptr_field_inner(
        &self,
        ty: Ty<'tcx>,
        prefix: Vec<usize>,
        depth: usize,
    ) -> Option<Vec<usize>> {
        use rustc_middle::ty::TyKind;
        if depth > 4 {
            return None;
        }
        match ty.kind() {
            TyKind::Adt(adt, substs) => {
                if adt.is_enum() {
                    return None;
                }
                for (idx, field_def) in adt.non_enum_variant().fields.iter().enumerate() {
                    let field_ty =
                        mir_utils::field_ty(self.tcx, field_def, substs);
                    let mut path = prefix.clone();
                    path.push(idx);
                    if let TyKind::RawPtr(..) = field_ty.kind() {
                        return Some(path);
                    }
                    if self.find_nn_pointee(field_ty).is_some() {
                        return Some(path);
                    }
                    if let Some(found) =
                        self.container_ptr_field_inner(field_ty, path, depth + 1)
                    {
                        return Some(found);
                    }
                }
                None
            }
            _ => None,
        }
    }

    pub(crate) fn container_data_alloc(
        &self,
        header: AllocId,
        ty: Ty<'tcx>,
    ) -> Option<AllocId> {
        use rustc_middle::ty::TyKind;
        let mut view_ty = ty;
        while let TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) = view_ty.kind() {
            view_ty = *inner;
        }
        if !matches!(view_ty.kind(), TyKind::Adt(..)) {
            return None;
        }
        let path = self.container_ptr_field(view_ty)?;
        self.load_value(header, view_ty, &path)?.provenance_alloc_id()
    }

    /// The data allocation behind a container header or a slice view's header.
    /// Tries the type-driven owning field first, then falls back to scanning the
    /// header's materialized fields for the first owning pointer (covers slice
    /// views whose header `AllocId` no longer carries a type key).
    pub(crate) fn data_alloc_of(&self, header: AllocId, ty: Ty<'tcx>) -> Option<AllocId> {
        self.container_data_alloc(header, ty).or_else(|| {
            // The header → data fallback is only for local (non-external) slice
            // views. An external parameter's header carries an `i64::MAX`
            // "unbounded" size that already discharges `Allocated`, so do not
            // redirect it to the (symbolic-sized) pointee.
            if self.alloc(header).is_external() {
                None
            } else {
                self.header_data_alloc(header)
            }
        })
    }

    /// Scan a header allocation's materialized fields for the owning pointer
    /// (its provenance names the data allocation). This is the header → data
    /// fallback for slice views (whose provenance names the container header,
    /// not the data), replacing the old `slice_data` edge.
    ///
    /// Returns the provenance only when the header has *exactly one* owning
    /// pointer field. A multi-owning-pointer header (e.g. a linked list's
    /// `head`/`tail`) is ambiguous, so fall back to `None` rather than guess.
    fn header_data_alloc(&self, header: AllocId) -> Option<AllocId> {
        let mut result = None;
        for ((_, p), v) in self.units[header.0].content.values.iter() {
            if p.is_empty() {
                continue;
            }
            let Some(prov) = v.provenance_alloc_id() else {
                continue;
            };
            if result.is_some() {
                return None;
            }
            result = Some(prov);
        }
        result
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn set_container_data_field(
        &mut self,
        header: AllocId,
        ty: Ty<'tcx>,
        data_alloc: AllocId,
        base: Int<'z3>,
        elem_ty: Ty<'tcx>,
    ) -> bool {
        use rustc_middle::ty::TyKind;
        let mut view_ty = ty;
        while let TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) = view_ty.kind() {
            view_ty = *inner;
        }
        if !matches!(view_ty.kind(), TyKind::Adt(..)) {
            return false;
        }
        let Some(path) = self.container_ptr_field(view_ty) else {
            return false;
        };
        let ptr_field = VmValue {
            z3_term: base,
            ty: elem_ty,
            provenance: Some(Provenance {
                alloc_id: data_alloc,
                offset: Int::from_u64(self.z3_ctx, 0),
                offset_kind: None,
            }),
            facts: ValueFacts {
                non_null: true,
                init: true,
                in_bounds: true,
                ..ValueFacts::default()
            },
            source: ValueSource::None,
        };
        self.store_value(header, view_ty, path, ptr_field);
        true
    }

    /// If `operand` is a constant reference to a byte array (e.g. `b"hello\0"`),
    /// extract the raw bytes and create a tracked allocation. Updates `val`
    /// in-place with the proper provenance and invariants.
    pub(crate) fn try_materialize_const_bytes(
        &mut self,
        val: &mut VmValue<'z3, 'tcx>,
        operand: &Operand<'tcx>,
    ) {
        // Use the operand's type (before any pointer cast) to check for byte arrays.
        let operand_val = self.value_of_operand(operand);
        let op_ty = operand_val.ty;
        let (pointee_ty, _is_ref) = match op_ty.kind() {
            rustc_middle::ty::TyKind::Ref(_, inner_ty, _) => (*inner_ty, true),
            rustc_middle::ty::TyKind::RawPtr(inner_ty, _) => (*inner_ty, false),
            _ => {
                // Fallback: use val's type
                let val_ty = val.ty;
                match val_ty.kind() {
                    rustc_middle::ty::TyKind::Ref(_, inner_ty, _) => (*inner_ty, true),
                    rustc_middle::ty::TyKind::RawPtr(inner_ty, _) => (*inner_ty, false),
                    _ => return,
                }
            }
        };
        match pointee_ty.kind() {
            rustc_middle::ty::TyKind::Array(elem_ty, _)
            | rustc_middle::ty::TyKind::Slice(elem_ty) => {
                let is_byte = matches!(
                    elem_ty.kind(),
                    rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::U8)
                        | rustc_middle::ty::TyKind::Int(rustc_middle::ty::IntTy::I8)
                );
                if is_byte {
                    let bytes_opt =
                        mir_utils::const_operand_bytes(self.tcx, operand)
                            .or_else(|| self.trace_to_const_bytes(operand));
                    if let Some(bytes) = bytes_opt {
                        let size = z3::ast::Int::from_u64(self.z3_ctx, bytes.len() as u64);
                        let align = self.align_sym(pointee_ty);
                        let (alloc_id, base) = self.allocate(size, align, Some(pointee_ty));
                        self.content_mut(alloc_id).facts.initialized = true;
                        // A const/static byte materialization lives for the
                        // whole program (`'static`), so it is always alive.
                        self.alloc_mut(alloc_id).facts.liveness =
                            Some(self.tcx.lifetimes.re_static);
                        for (i, &b) in bytes.iter().enumerate() {
                            self.record_byte_value(
                                alloc_id,
                                i,
                                z3::ast::Int::from_u64(self.z3_ctx, b as u64),
                            );
                        }
                        val.z3_term = base;
                        val.provenance = Some(super::state::Provenance {
                            alloc_id,
                            offset: z3::ast::Int::from_u64(self.z3_ctx, 0),
                            offset_kind: None,
                        });
                        val.facts = ValueFacts {
                            non_null: true,
                            init: true,
                            in_bounds: false,
                            align_n: None,
                        };
                    }
                }
            }
            _ => {}
        }
    }

    pub(crate) fn trace_to_const_bytes(&self, operand: &Operand<'tcx>) -> Option<Vec<u8>> {
        let place = match operand {
            Operand::Copy(p) | Operand::Move(p) => p,
            _ => return None,
        };
        let base_local = if place.projection.is_empty()
            || (place.projection.len() == 1
                && matches!(
                    place.projection.first().map(|p| p.kind()),
                    Some(rustc_middle::mir::ProjectionElem::Deref)
                ))
        {
            place.local
        } else {
            return None;
        };
        for block in self.body().basic_blocks.iter() {
            for stmt in &block.statements {
                if let StatementKind::Assign(assign) = &stmt.kind {
                    let (dest, rvalue) = &**assign;
                    if dest.local != base_local || !dest.projection.is_empty() {
                        continue;
                    }
                    match rvalue {
                        Rvalue::Use(op, ..) => {
                            return mir_utils::const_operand_bytes(self.tcx, op)
                                .or_else(|| self.trace_to_const_bytes(op));
                        }
                        Rvalue::Ref(_, _, p) => {
                            let op = Operand::Copy(*p);
                            return self.trace_to_const_bytes(&op);
                        }
                        _ => return None,
                    }
                }
            }
        }
        None
    }

    /// Propagate byte values from a source place's allocation to the
    /// provenance allocation of a reference. This ensures that when we
    /// create `&bytes` from an aggregate, the byte-level tracking follows.
    /// Propagate a source place's per-field values to a reference destination,
    /// shifting the field path by the source place's `Field` projection prefix.
    /// E.g. for `_3 = &(_1.0)` where `_1` is a `Handle { node: NodeRef { node:
    /// NonNull<..>, .. }, .. }`, the nested `NonNull`'s field value stored at
    /// path `[0, 1]` becomes available at `_3`'s path `[1]`, so an inlined
    /// callee that dereferences `_3` and reads its `node` field sees the
    /// provenance of the underlying allocation.
    pub(crate) fn propagate_field_values_to_ref(&mut self, source_place: &Place<'tcx>, dest: Local) {
        // Support both `&(local.field...)` (Field projection prefix) and
        // `&(*local)` (reborrow of a reference, pure Deref).  In the latter
        // case the reference's own per-field values already describe the
        // pointee, so they are copied unchanged.
        let only_field_deref = source_place.projection.iter().all(|p| {
            matches!(
                p.kind(),
                rustc_middle::mir::ProjectionElem::Field(..)
                    | rustc_middle::mir::ProjectionElem::Deref
            )
        });
        if !only_field_deref {
            return;
        }
        let field_prefix: Vec<usize> = source_place
            .projection
            .iter()
            .filter_map(|p| match p.kind() {
                rustc_middle::mir::ProjectionElem::Field(fi, _) => Some(fi.as_usize()),
                _ => None,
            })
            .collect();
        // A bare `&local` (no projection) exposes the pointee's whole field
        // map. Only propagate fields that carry provenance (pointer leaves);
        // plain scalar fields (e.g. array elements) must not leak into the
        // reference or they can corrupt downstream InBound reasoning.
        let empty_proj = source_place.projection.is_empty();
        let keys: Vec<Vec<usize>> = self.field_paths(source_place.local);
        for path in keys {
            let matches_prefix = field_prefix.is_empty()
                || (path.len() >= field_prefix.len()
                    && path[..field_prefix.len()] == field_prefix[..]);
            if matches_prefix {
                let rest = if field_prefix.is_empty() {
                    path.clone()
                } else {
                    path[field_prefix.len()..].to_vec()
                };
                // `rest == []` means the pointee *is* `source_place` itself
                // (e.g. `&mut self.v`).  Do not mirror it into the reference's
                // `path == []`: that slot now holds the reference's whole value
                // (see M2), so writing the pointee there would clobber it.  The
                // pointee value stays on the *source* field and is recovered by
                // `ReturnDerefArg`'s field-map fallback instead.
                if rest.is_empty() {
                    continue;
                }
                if let Some(v) = self.field_value(source_place.local, &path).cloned() {
                    if empty_proj && v.provenance.is_none() {
                        continue;
                    }
                    self.set_field_value(dest, rest, v);
                }
            }
        }
    }

    pub(crate) fn propagate_byte_values_to_ref(
        &mut self,
        source_place: &Place<'tcx>,
        ref_val: &VmValue<'z3, 'tcx>,
    ) {
        let Some(src_alloc_id) = self.current_frame.local_alloc.get(&source_place.local).copied() else {
            return;
        };
        let Some(ref_alloc_id) = ref_val.provenance_alloc_id() else {
            return;
        };
        if src_alloc_id == ref_alloc_id {
            return; // same allocation, bytes already there
        }
        // Copy per-byte tracking from source alloc to ref's alloc (offset 0:
        // the reference points at the source place's start).
        self.copy_byte_tracking(src_alloc_id, 0, ref_alloc_id);
    }

    /// Return the per-field types for an aggregate's operands.
    pub(crate) fn aggregate_field_tys(&self, ty: Ty<'tcx>) -> Vec<Ty<'tcx>> {
        match ty.kind() {
            rustc_middle::ty::TyKind::Array(elem_ty, _len) => {
                vec![*elem_ty]
            }
            rustc_middle::ty::TyKind::Tuple(elems) => elems.iter().collect(),
            rustc_middle::ty::TyKind::Adt(adt_def, substs) => {
                if adt_def.is_enum() {
                    return vec![];
                }
                let variant = adt_def.non_enum_variant();
                variant
                    .fields
                    .iter()
                    .map(|f| mir_utils::field_ty(self.tcx, f, substs))
                    .collect()
            }
            _ => vec![],
        }
    }
}
