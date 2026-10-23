//! Call handling for the symbolic VM.
//!
//! Bridges the existing call summary infrastructure (`call_summary`)
//! with the new symbolic VM state. The `exec_call` method is called
//! from `exec.rs` when a `Call` terminator is encountered.
//!
//! When the callee has MIR available, the VM recursively inlines the
//! callee's body to achieve context-sensitive precision, unless a
//! effects summary provides more precise hand-crafted invariants.
//! Otherwise it falls back to the summary-based approach.

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Local, Operand, Terminator, TerminatorKind};
use rustc_middle::ty::{Ty, TyKind};
use z3::ast::{Ast, Int};
use z3::{SatResult, Solver};

use crate::compat::{FxHashSet, Spanned};
use crate::helpers::mir_utils;
use crate::limit::MAX_INLINE_DEPTH;
use crate::verify::api_classify;
use crate::verify::call_summary;
use super::state::{AllocId, MemoryContent, OffsetKind, Provenance, ValueFacts, ValueSource, VmState, VmValue};

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    /// Execute a call terminator, dispatching by precision:
    ///
    ///  1. pre-inline side effect (`Eq` const-byte propagation) — always runs
    ///     and falls through;
    ///  2. a registry / transparent-deref summary effect;
    ///  3. inline of the callee's MIR when there is no summary.
    ///
    /// A call with neither a summary nor inlinable MIR leaves `destination`
    /// unset.
    pub(crate) fn exec_call(
        &mut self,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        destination: Local,
        caller_def_id: DefId,
    ) {
        let arg_values: Vec<VmValue<'z3, 'tcx>> = args
            .iter()
            .map(|arg| self.value_of_operand(&arg.node))
            .collect();
        let caller_arg_locals: Vec<Option<Local>> = args
            .iter()
            .map(|a| a.node.place().map(|p| p.local))
            .collect();
        let callee = mir_utils::dep_callee_resolved_def_id(self.tcx, caller_def_id, func);

        if api_classify::is_eq_call(callee) {
            self.propagate_const_bytes_to_tracked(args);
        }

        // `assert_unsafe_precondition!` gates are disabled under release
        // semantics; bind them to `false` so their branchy panic bodies are not
        // inlined (which would otherwise recurse to the depth limit).
        if let Some(c) = callee
            && api_classify::is_ub_check(self.tcx, c)
        {
            let dest_ty = self.body().local_decls[destination].ty;
            self.set_local(
                destination,
                VmValue::new(Int::from_u64(self.z3_ctx, 0), dest_ty),
            );
            return;
        }

        // `intrinsics::arith_offset` is the wrapping element-strided offset that
        // stays a `Call` in MIR (it is not lowered to `BinOp::Offset`).  Model it
        // with the same stride/provenance precision as `Offset`, deriving the
        // stride from the base operand's (monomorphized) pointee type.
        if api_classify::is_intrinsic_arith_offset(callee) {
            if let (Some(base), Some(count)) = (args.first(), args.get(1)) {
                let base_val = self.value_of_operand(&base.node);
                let count_val = self.value_of_operand(&count.node);
                let pointee = mir_utils::pointee_ty(base_val.ty);
                let stride = pointee.and_then(|p| {
                    let (_, s) = mir_utils::type_layout(
                        self.tcx,
                        self.current_frame.current_def_id,
                        p,
                    )?;
                    if s == 0 && mir_utils::ty_has_type_param(p) {
                        None
                    } else {
                        Some(s)
                    }
                });
                self.apply_pointer_add(destination, &base_val, &count_val, stride, false);
            }
            return;
        }

        // Registry summary, else the transparent-deref / unknown fallback.
        let summary = crate::verify::call_summary::effects::lookup_effect(
            self.tcx,
            caller_def_id,
            callee,
            func,
            destination,
        ).or_else(|| call_summary::effects::effect_summary(self.tcx, func));

        if let Some(effects) = summary {
            for effect in &effects {
                self.apply_call_effect(effect, &arg_values, &caller_arg_locals, destination, callee, func);
            }
        } else if let Some(c) = callee && self.tcx.is_mir_available(c) {
            self.exec_inline_call(c, &arg_values, &caller_arg_locals, destination);
        }
    }

    /// Recursively execute a callee's MIR body inline.
    ///
    /// Binds the caller's argument values to the callee's parameters,
    /// executes the callee's MIR, and writes the return value to
    /// the caller's destination local. Returns `false` if inline
    /// is not possible (e.g., recursion limit reached, callee has
    /// branches, or the callee is too large).
    fn exec_inline_call(
        &mut self,
        callee_def_id: DefId,
        arg_values: &[VmValue<'z3, 'tcx>],
        caller_arg_locals: &[Option<Local>],
        dest: Local,
    ) -> bool {
        if self.inline.inline_depth >= MAX_INLINE_DEPTH {
            // Leave a distinguishable symbolic value in `dest` so the checker
            // can detect that this result depends on a truncated inline and
            // report `Unknown` instead of failing on an unconstrained term.
            let dest_ty = self.body().local_decls[dest].ty;
            let truncated_term = self.fresh_int("inline_truncated");
            self.inline.inline_truncated_terms.insert(truncated_term.clone());
            self.set_local(dest, VmValue::new(truncated_term, dest_ty));
            return false;
        }
        let before_inline = self.clone();
        self.inline.inline_depth += 1;

        // ── Save caller context ──
        // Resolve each arg's referent local (for `&self`/`&mut self` reborrow
        // temps) *before* the caller's address map is saved away, so that
        // `exec_assign` can resolve `(*self).field = val` writes back to the
        // caller's referent while the callee executes.
        let inline_arg_referents: Vec<Option<Local>> = arg_values
            .iter()
            .map(|v| self.find_local_by_address(&v.z3_term))
            .collect();
        let caller_referents = inline_arg_referents.clone();
        // Whole-place reborrow referents, resolved from the *caller's* MIR
        // before the body is switched to the callee (used to propagate the
        // referent's struct fields into the callee for `old = self.ptr`).
        let reborrow_referents: Vec<Option<Local>> = caller_arg_locals
            .iter()
            .map(|arg_opt| arg_opt.and_then(|a| self.find_whole_reborrow_referent(a)))
            .collect();
        let frame = self.save_frame();
        let saved_inline_arg_referents =
            std::mem::replace(&mut self.inline.arg_referents, inline_arg_referents);
        let saved_deferred_field_writes = std::mem::take(&mut self.inline.deferred_field_writes);

        // ── Switch to callee context ──
        self.current_frame.current_def_id = callee_def_id;

        // Bind args to callee locals (local_1..local_N are function params)
        for (i, arg_val) in arg_values.iter().enumerate() {
            let callee_local = Local::from_usize(i + 1);
            self.ensure_local_allocation(callee_local);
            self.set_local(callee_local, arg_val.clone());
        }

        // Propagate the caller arg locals' field values into the callee context
        // so that the inline body can access struct fields (e.g. Iter::ptr /
        // end_or_len for len/is_empty computations).
        for (i, caller_arg_opt) in caller_arg_locals.iter().enumerate() {
            let callee_param = Local::from_usize(i + 1);
            let Some(caller_arg) = caller_arg_opt else {
                continue;
            };
            // A whole-place reborrow (`_7 = &mut (*_1)`) shares the referent's
            // struct fields; when the reborrow temp's own assignment was pruned,
            // propagate the referent's fields so `self.ptr` resolves in the
            // callee (Iter::next).  Excludes field reborrows.
            let mut source_locals = vec![*caller_arg];
            if let Some(r) = reborrow_referents.get(i).copied().flatten()
                && r != *caller_arg {
                    source_locals.push(r);
                }
            for src in source_locals {
                let caller_field_keys: Vec<Vec<usize>> = self.frame_field_paths(&frame, src);
                for fields in caller_field_keys {
                    if let Some(fv) = self.frame_field_value(&frame, src, &fields).cloned() {
                        self.set_field_value(callee_param, fields, fv);
                    }
                }
            }
        }

        // ── Execute callee MIR ──
        let pre_uninit: Vec<AllocId> = caller_referents.iter()
            .flatten()
            .filter(|local| api_classify::is_maybe_uninit_ty(before_inline.body().local_decls[**local].ty))
            .filter_map(|local| before_inline.current_frame.local_alloc.get(local).copied())
            .filter(|id| !before_inline.content(*id).facts.initialized)
            .collect();
        let may_recurse = self.body().basic_blocks.iter().any(|block| {
            let TerminatorKind::Call { func, .. } = &block.terminator().kind else {
                return false;
            };
            mir_utils::dep_callee_resolved_def_id(self.tcx, callee_def_id, func)
                == Some(callee_def_id)
        });
        if !self.inline_execute_body(&pre_uninit) {
            let witnessed = self.possible_uninit_allocs.clone();
            *self = before_inline;
            self.possible_uninit_allocs.extend(witnessed);
            self.incomplete_inline_branch = true;
            let dest_ty = self.body().local_decls[dest].ty;
            let unknown_term = self.fresh_int("inline_branch_unknown");
            self.inline.inline_branch_terms.insert(unknown_term.clone());
            if may_recurse {
                self.inline.inline_truncated_terms.insert(unknown_term.clone());
            }
            self.set_local(dest, VmValue::new(unknown_term, dest_ty));
            let mut unknown_effect =
                self.tcx.fn_sig(callee_def_id).skip_binder().safety() == rustc_hir::Safety::Unsafe;
            for (arg, referent) in arg_values.iter().zip(&caller_referents) {
                match arg.ty.kind() {
                    TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_)
                    | TyKind::Float(_) => {}
                    TyKind::Ref(..) | TyKind::RawPtr(..) => {
                        if let Some(local) = referent {
                            self.forget_inline_referent(*local);
                        } else {
                            unknown_effect = true;
                        }
                    }
                    _ => unknown_effect = true,
                }
            }
            self.unsupported_mir |= unknown_effect;
            return false;
        }

        // ── Capture return value and its per-field values ──
        let return_val = self.local_value(Local::from_usize(0)).cloned();
        crate::rap_debug!(
            "exec_inline_call: callee={:?} return_val={:?}",
            callee_def_id,
            return_val
                .as_ref()
                .map(|v| (v.z3_term.to_string(), v.facts.non_null))
        );
        let return_fields: Vec<(Vec<usize>, VmValue<'z3, 'tcx>)> = self
            .field_paths(Local::from_usize(0))
            .into_iter()
            .filter_map(|path| {
                self.field_value(Local::from_usize(0), &path)
                    .cloned()
                    .map(|val| (path, val))
            })
            .collect();

        // ── Restore caller context ──
        self.restore_frame(frame);

        // Apply deferred field writes (`(*self).field = val` through a
        // `&mut self` reborrow) collected during the callee's execution, now
        // that the caller's frame (and its address map) is live again.
        let writes = std::mem::take(&mut self.inline.deferred_field_writes);
        self.inline.arg_referents = saved_inline_arg_referents;
        self.inline.deferred_field_writes = saved_deferred_field_writes;
        self.replay_deferred_writes(writes);

        // ── Write return value to caller destination ──
        let dest_ty = self.body().local_decls[dest].ty;
        match return_val {
            Some(mut val) => {
                val.ty = dest_ty;
                // Infer facts: a non-null provenance with offset=0
                // means the return value is valid and initialized.
                let at_base = val
                    .provenance
                    .as_ref()
                    .is_some_and(|p| p.offset.as_u64() == Some(0));
                if at_base {
                    val.facts.non_null = true;
                    self.mark_initialized(&mut val);
                }
                self.set_local(dest, val);
                // Propagate the callee's per-field return values (e.g. a
                // tuple `(NonNull<T>, A)`'s field 0) to the caller's
                // destination so subsequent field projections resolve.
                for (path, fv) in return_fields {
                    self.set_field_value(dest, path, fv);
                }
                // The callee returned a fully-constructed value, so the
                // caller's destination stack slot is initialized.  This matters
                // for ADT returns (struct/enum) whose aggregate value carries
                // no provenance: a later `&raw const (*&field)` + `ptr::read`
                // must be able to discharge `Init` against the field.
                if let Some(dest_alloc_id) = self.current_frame.local_alloc.get(&dest).copied() {
                    self.content_mut(dest_alloc_id).facts.initialized = true;
                }
            }
            None => {
                self.inline.inline_depth -= 1;
                return false;
            }
        }

        self.inline.inline_depth -= 1;
        true
    }

    fn forget_inline_referent(&mut self, local: Local) {
        let Some(alloc_id) = self.current_frame.local_alloc.get(&local).copied() else {
            self.unsupported_mir = true;
            return;
        };
        if self.possible_uninit_allocs.contains(&alloc_id) {
            return;
        }
        let prior = self.local_value(local).cloned();
        *self.content_mut(alloc_id) = MemoryContent::default();
        let ty = self.body().local_decls[local].ty;
        let unknown_term = self.fresh_int("inline_write_unknown");
        self.inline.inline_branch_terms.insert(unknown_term.clone());
        let mut unknown = VmValue::new(unknown_term, ty);
        if let Some(prior) = prior
            && prior.provenance_alloc_id() == Some(alloc_id)
        {
            unknown.provenance = prior.provenance;
        }
        self.set_local(local, unknown);
    }

    /// Resolve a `SwitchInt` discriminant to a constant `u64`, following a
    /// single local-assignment chain (a `cfg!`-style runtime-check flag) or a
    /// call to an `assert_unsafe_precondition!` gate (`check_language_ub`),
    /// which is disabled under release semantics.
    fn switch_discr_const(
        &self,
        body: &rustc_middle::mir::Body<'tcx>,
        discr: &Operand<'tcx>,
    ) -> Option<u64> {
        if let Some(v) = mir_utils::operand_const_u64(discr) {
            return Some(v);
        }
        // A `UbChecks`/`ContractChecks`/`OverflowChecks` discriminant folds to
        // the no-check edge (`0` = false), mirroring release-mode const-folding.
        #[cfg(rapx_ge_95)]
        if let Operand::RuntimeChecks(_) = discr {
            return Some(0);
        }
        // `T::IS_ZST` for a generic `T` is unevaluated; fold it to `false`
        // (non-ZST).  The `IS_ZST` guard in pointer arithmetic (`add`/`sub`/
        // `offset`) only skips redundant arithmetic: `offset` on a ZST pointee
        // is a no-op (stride 0), so the non-ZST path is correct for ZST too and
        // avoids the ZST branch returning `self` with a stale element offset.
        if let Operand::Constant(constant) = discr
            && let rustc_middle::mir::Const::Unevaluated(uneval, _) = constant.const_
            && mir_utils::is_sized_type_property(self.tcx, uneval.def, "IS_ZST")
        {
            return Some(0);
        }
        let (Operand::Copy(p) | Operand::Move(p)) = discr else {
            return None;
        };
        for bbd in body.basic_blocks.iter() {
            for stmt in bbd.statements.iter() {
                let rustc_middle::mir::StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let (dest, rvalue) = &**assign;
                if dest != p {
                    continue;
                }
                if let Some(v) = mir_utils::rvalue_runtime_checks_value(rvalue) {
                    return Some(v);
                }
                // `_4 = const <T as SizedTypeProperties>::IS_ZST` (generic `T`):
                // fold to non-ZST, mirroring the direct-const case above.
                if let rustc_middle::mir::Rvalue::Use(operand, ..) = rvalue
                    && let Operand::Constant(constant) = operand
                    && let rustc_middle::mir::Const::Unevaluated(uneval, _) = constant.const_
                    && mir_utils::is_sized_type_property(self.tcx, uneval.def, "IS_ZST")
                {
                    return Some(0);
                }
            }
        }
        // `check_language_ub` is a function *call* (not an assignment), whose
        // destination is the discriminant.  It gates the precondition check
        // behind `debug_assertions`/`ub_checks` and is `false` under the release
        // semantics the VM models.
        for bbd in body.basic_blocks.iter() {
            let terminator = bbd.terminator();
            if let TerminatorKind::Call {
                func, destination, ..
            } = &terminator.kind
                && destination.local == p.local
                && destination.projection.is_empty()
                && let Some(callee) = mir_utils::dep_callee_def_id(func)
                && api_classify::is_ub_check(self.tcx, callee)
            {
                return Some(0);
            }
        }
        None
    }

    /// Execute the callee's MIR body.
    fn inline_execute_body(&mut self, pre_uninit: &[AllocId]) -> bool {
        let mut visited = FxHashSet::default();
        let mut queue: Vec<BasicBlock> = Vec::new();
        queue.push(BasicBlock::from_usize(0));

        while let Some(block) = queue.pop() {
            if !visited.insert(block) {
                continue;
            }

            let bb_data = &self.body().basic_blocks[block];

            // Execute statements
            for stmt in bb_data.statements.iter() {
                crate::verify::vm::rules::exec_statement(self, stmt);
            }

            // Process terminator
            let terminator = bb_data.terminator();

            match &terminator.kind {
                TerminatorKind::Goto { target, .. } => {
                    queue.push(*target);
                }
                TerminatorKind::Return => {
                    // Return value captured in local_0
                }
                TerminatorKind::Assert {
                    target,
                    ..
                } => {
                    crate::verify::vm::rules::exec_terminator(self, terminator, None);
                    queue.push(*target);
                }
                TerminatorKind::SwitchInt { discr, targets } => {
                    // A constant discriminant folds to a single live edge.
                    if let Some(v) = self.switch_discr_const(self.body(), discr) {
                        let t = targets
                            .iter()
                            .find(|(val, _)| *val == v as u128)
                            .map(|(_, t)| t)
                            .unwrap_or_else(|| targets.otherwise());
                        queue.push(t);
                        continue;
                    }
                    // A `debug_assert!`/`assert!` switch or a drop-flag dispatch
                    // has its non-otherwise edges dead on the normal path, so
                    // follow only `otherwise`.
                    let trivial = mir_utils::switch_targets_unreachable(
                        self.tcx,
                        self.body(),
                        targets,
                    );
                    if trivial {
                        queue.push(targets.otherwise());
                        continue;
                    }
                    self.possible_uninit_allocs.extend(
                        self.find_uninit_witness(terminator, pre_uninit)
                    );
                    return false;
                }
                TerminatorKind::Call {
                    target,
                    ..
                } => {
                    crate::verify::vm::rules::exec_terminator(self, terminator, None);
                    if let Some(t) = target {
                        queue.push(*t);
                    }
                }
                TerminatorKind::Drop { target, .. } => {
                    crate::verify::vm::rules::exec_terminator(self, terminator, None);
                    queue.push(*target);
                }
                _ => {
                    crate::verify::vm::rules::exec_terminator(self, terminator, None);
                }
            }
        }
        true
    }

    fn find_uninit_witness(
        &self,
        switch: &Terminator<'tcx>,
        candidates: &[AllocId],
    ) -> FxHashSet<AllocId> {
        let TerminatorKind::SwitchInt { targets, .. } = &switch.kind else {
            return FxHashSet::default();
        };
        if candidates.is_empty() {
            return FxHashSet::default();
        }
        let mut found = FxHashSet::default();
        let mut stack = Vec::new();
        for target in targets.all_targets().iter().copied() {
            let mut state = self.clone();
            crate::verify::vm::rules::exec_terminator(&mut state, switch, Some(target));
            stack.push((state, target, FxHashSet::default()));
        }
        let mut explored = 0;
        while let Some((mut state, block, mut visited)) = stack.pop() {
            if explored >= 512 || !visited.insert(block) {
                continue;
            }
            explored += 1;
            let data = &state.body().basic_blocks[block];
            for statement in &data.statements {
                crate::verify::vm::rules::exec_statement(&mut state, statement);
            }
            let terminator = data.terminator();
            match &terminator.kind {
                TerminatorKind::Return => {
                    let solver = Solver::new(state.z3_ctx);
                    state.assert_all(&solver);
                    if solver.check() == SatResult::Sat {
                        for id in candidates {
                            if !state.content(*id).facts.initialized {
                                found.insert(*id);
                            }
                        }
                    }
                    if found.len() == candidates.len() {
                        break;
                    }
                }
                TerminatorKind::Goto { target, .. } => stack.push((state, *target, visited)),
                TerminatorKind::SwitchInt { targets, .. } => {
                    for target in targets.all_targets().iter().copied() {
                        let mut branch = state.clone();
                        crate::verify::vm::rules::exec_terminator(
                            &mut branch, terminator, Some(target)
                        );
                        stack.push((branch, target, visited.clone()));
                    }
                }
                TerminatorKind::Assert { target, .. } => {
                    crate::verify::vm::rules::exec_terminator(&mut state, terminator, None);
                    stack.push((state, *target, visited));
                }
                TerminatorKind::Call { func, target: Some(target), .. } => {
                    let callee = mir_utils::dep_callee_resolved_def_id(
                        state.tcx,
                        state.current_frame.current_def_id,
                        func,
                    );
                    if callee.is_some_and(|def_id| state.tcx.is_mir_available(def_id)) {
                        let incomplete = state.incomplete_inline_branch;
                        let truncated = state.inline.inline_truncated_terms.len();
                        crate::verify::vm::rules::exec_terminator(&mut state, terminator, None);
                        if !state.unsupported_mir
                            && state.incomplete_inline_branch == incomplete
                            && state.inline.inline_truncated_terms.len() == truncated
                        {
                            stack.push((state, *target, visited));
                        }
                    }
                }
                _ => {}
            }
        }
        found
    }

    /// Clone `arg_val`, retype it to `dest`'s type, mark it as a non-null,
    /// aligned, initialized pointer, and bind it to `dest`.
    pub(crate) fn set_dest_as_heap_ptr(&mut self, arg_val: &VmValue<'z3, 'tcx>, dest: Local) {
        let mut val = arg_val.clone();
        val.ty = self.body().local_decls[dest].ty;
        val.facts.non_null = true;
        val.facts.init = true;
        self.set_local(dest, val);
    }

    /// Apply a binary numeric effect: compute `f(lhs.z3_term, rhs.z3_term)` and store
    /// it as the destination's fresh scalar value.
    pub(crate) fn apply_binary_num(
        &mut self,
        dest: Local,
        args: &[VmValue<'z3, 'tcx>],
        lhs_arg: usize,
        rhs_arg: usize,
        f: impl Fn(&Int<'z3>, &Int<'z3>) -> Int<'z3>,
    ) {
        if let (Some(lhs), Some(rhs)) = (args.get(lhs_arg), args.get(rhs_arg)) {
            let dest_ty = self.body().local_decls[dest].ty;
            self.set_local(dest, VmValue::new(f(&lhs.z3_term, &rhs.z3_term), dest_ty));
        }
    }

    pub(crate) fn integer_limits(&self, ty: Ty<'tcx>) -> Option<(Int<'z3>, Int<'z3>, Int<'z3>, bool)> {
        let signed = match ty.kind() {
            TyKind::Int(_) => true,
            TyKind::Uint(_) => false,
            _ => return None,
        };
        let (_, bytes) = mir_utils::type_layout(self.tcx, self.current_frame.current_def_id, ty)?;
        let bits = bytes.checked_mul(8)?;
        if bits == 0 || bits > 128 {
            return None;
        }
        let unsigned_max = if bits == 128 { u128::MAX } else { (1u128 << bits) - 1 };
        let modulus = Int::add(self.z3_ctx, &[
            &Int::from_str(self.z3_ctx, &unsigned_max.to_string())?,
            &Int::from_u64(self.z3_ctx, 1),
        ]);
        let (min, max) = if signed {
            let signed_max = if bits == 128 {
                i128::MAX
            } else {
                (1i128 << (bits - 1)) - 1
            };
            let signed_min = if bits == 128 {
                i128::MIN
            } else {
                -(1i128 << (bits - 1))
            };
            (signed_min.to_string(), signed_max.to_string())
        } else {
            ("0".to_string(), unsigned_max.to_string())
        };
        Some((
            Int::from_str(self.z3_ctx, &min)?,
            Int::from_str(self.z3_ctx, &max)?,
            modulus,
            signed,
        ))
    }

    /// Compute the preserved alignment when doing `base + offset * stride`.
    /// Pointer arithmetic only ever *preserves* the base's alignment; it never
    /// creates it. When the base's alignment is unknown, we cannot conclude
    /// anything about the result (a `wrapping_add` over misaligned storage does
    /// not become aligned just because the stride is a power of two).
    fn compute_pointer_add_align(
        &self,
        base: &VmValue<'z3, 'tcx>,
        stride_bytes: u64,
    ) -> Option<Int<'z3>> {
        let base_align = base.facts.align_n.as_ref()?;
        // Concrete alignment: the result stays n-aligned only if the stride is
        // a multiple of n.  A symbolic alignment can't be decided against a
        // concrete stride, so drop it here (the `check_align` SMT query
        // re-derives alignment from the allocation's align and the
        // `sizeof_T % align_T == 0` layout constraint).
        let n = base_align.simplify().as_u64()?;
        if stride_bytes > 0 && stride_bytes.is_multiple_of(n) {
            return Some(base_align.clone());
        }
        None
    }

    /// The byte stride for a pointer add/sub: the fixed `stride`, or the pointee's
    /// symbolic size when the stride is element-sized (a generic `T`).
    fn pointer_stride_term(&mut self, dest: Local, stride: Option<u64>) -> Int<'z3> {
        match stride {
            Some(s) => Int::from_u64(self.z3_ctx, s),
            None => {
                let dest_ty = self.body().local_decls[dest].ty;
                let pointee = mir_utils::pointee_ty(dest_ty).unwrap_or(dest_ty);
                self.size_sym(pointee)
            }
        }
    }

    /// Model `dest = base.offset(offset)` with element/byte stride and tracked
    /// provenance (`offset_kind`), shared by the `ReturnPointerAdd` call effect
    /// and the inlined `Offset` MIR statement.
    pub(crate) fn apply_pointer_add(
        &mut self,
        dest: Local,
        base: &VmValue<'z3, 'tcx>,
        offset: &VmValue<'z3, 'tcx>,
        stride: Option<u64>,
        dereferenceable: bool,
    ) {
        // `sub` lowers `intrinsics::unchecked_sub(0, n)` to a unary negation `-n`
        // (`eval_binary_op` folds `0 - x` to `-x`).  Recover the positive count
        // and model the result as `base - count*stride` (a negated product) so a
        // later `+ count*stride` in `Allocated`'s byte-coverage query cancels
        // linearly, instead of `base + (-count)*stride` whose `(-count)*stride`
        // product Z3's nonlinear solver cannot factor out.
        let (offset_term, subtract) = if offset.z3_term.num_children() == 1
            && let Some(positive) = offset.z3_term.nth_child(0).and_then(|c| c.as_int())
        {
            (positive, true)
        } else {
            (offset.z3_term.clone(), false)
        };
        let stride_term = self.pointer_stride_term(dest, stride);
        let adjusted_offset = if stride == Some(1) {
            offset_term.clone()
        } else {
            Int::mul(self.z3_ctx, &[&offset_term, &stride_term])
        };
        let combine = |l: &Int<'z3>, r: &Int<'z3>| {
            if subtract {
                Int::sub(self.z3_ctx, &[l, r])
            } else {
                Int::add(self.z3_ctx, &[l, r])
            }
        };
        let new_term = combine(&base.z3_term, &adjusted_offset);
        let is_field_offset = offset.is_field_offset()
            && base
                .provenance
                .as_ref()
                .is_some_and(|p| p.offset.as_u64() == Some(0));
        let element_offset = if stride == Some(1) {
            None
        } else {
            match base.provenance.as_ref().and_then(|p| match &p.offset_kind {
                Some(OffsetKind::Element(e)) => Some(e.clone()),
                _ => None,
            }) {
                Some(e) => Some(combine(&e, &offset_term)),
                None if base
                    .provenance
                    .as_ref()
                    .is_some_and(|p| p.offset.as_u64() == Some(0)) =>
                {
                    Some(if subtract {
                        -offset_term.clone()
                    } else {
                        offset_term.clone()
                    })
                }
                None => None,
            }
        };
        let offset_kind = if is_field_offset {
            Some(OffsetKind::Field)
        } else if let Some(e) = element_offset {
            Some(OffsetKind::Element(e))
        } else {
            Some(OffsetKind::Byte)
        };
        let adjusted_provenance = base.provenance.as_ref().map(|prov| Provenance {
            alloc_id: prov.alloc_id,
            offset: combine(&prov.offset, &adjusted_offset),
            offset_kind,
        });
        let align_n = match stride {
            Some(s) => self.compute_pointer_add_align(base, s),
            None => base.facts.align_n.clone(),
        };
        let val = VmValue {
            z3_term: new_term,
            ty: self.body().local_decls[dest].ty,
            provenance: adjusted_provenance,
            facts: ValueFacts {
                non_null: base.facts.non_null,
                in_bounds: dereferenceable,
                align_n,
                init: base.facts.init,
            },
            source: ValueSource::None,
        };
        self.set_local(dest, val);
    }

    pub(crate) fn propagate_const_bytes_to_tracked(&mut self, args: &[Spanned<Operand<'tcx>>]) {
        let mut const_bytes: Option<(Vec<u8>, usize)> = None;
        let mut tracked_alloc: Option<AllocId> = None;
        let mut tracked_offset: usize = 0;

        for (i, arg) in args.iter().enumerate() {
            let arg_val = self.value_of_operand(&arg.node);
            if const_bytes.is_none() {
                let bytes_opt = mir_utils::const_operand_bytes(self.tcx, &arg.node)
                    .or_else(|| self.trace_to_const_bytes(&arg.node));
                if let Some(bytes) = bytes_opt {
                    const_bytes = Some((bytes, i));
                }
            }
            if tracked_alloc.is_none()
                && let Some(alloc_id) = arg_val.provenance_alloc_id() {
                    tracked_alloc = Some(alloc_id);
                    if let Some(ref prov) = arg_val.provenance {
                        tracked_offset = prov.offset.as_u64().map(|v| v as usize).unwrap_or(0);
                    }
                }
        }

        if let (Some((bytes, _)), Some(alloc_id)) = (const_bytes, tracked_alloc) {
            for (j, &b) in bytes.iter().enumerate() {
                let off = tracked_offset + j;
                self.record_byte_value(alloc_id, off, Int::from_u64(self.z3_ctx, b as u64));
            }
            self.content_mut(alloc_id).facts.initialized = true;
        }
    }

    /// The two pointer fields of an Iter/IterMut local (`[0]` = ptr, `[1]` =
    /// end_or_len), which share the same allocation.  Returns `None` when
    /// either field is missing or the two point into different allocations.
    pub(crate) fn iter_ptr_end(&self, local: Local) -> Option<(VmValue<'z3, 'tcx>, VmValue<'z3, 'tcx>)> {
        for (ptr_path, end_path) in [(&[0][..], &[1][..]), (&[0, 0][..], &[0, 1][..])] {
            let (Some(ptr), Some(end)) =
                (self.field_value(local, ptr_path), self.field_value(local, end_path))
            else {
                continue;
            };
            if ptr
                .provenance
                .as_ref()
                .zip(end.provenance.as_ref())
                .is_some_and(|(pp, ep)| pp.alloc_id == ep.alloc_id)
            {
                return Some((ptr.clone(), end.clone()));
            }
        }
        None
    }

    /// Element size of the type iterated by an Iter/IterMut pointer, symbolic
    /// (`sizeof_T`) for a generic element type so `size / elem_size` cancels.
    pub(crate) fn iter_elem_size(&self, ptr: &VmValue<'z3, 'tcx>) -> Int<'z3> {
        let elem_ty = match ptr.ty.kind() {
            TyKind::Adt(_, substs) => substs.first().and_then(|s| s.as_type()),
            TyKind::RawPtr(ty, _) | TyKind::Ref(_, ty, _) => Some(*ty),
            _ => None,
        };
        if elem_ty.is_some_and(|ty| matches!(ty.kind(), TyKind::Param(_)))
            && let Some(alloc_id) = ptr.provenance_alloc_id()
            && let Some(concrete) = self.alloc(alloc_id).element_ty.as_ty()
            && !matches!(concrete.kind(), TyKind::Param(_))
        {
            return self.size_sym_read(concrete);
        }
        match elem_ty {
            Some(t) => self.size_sym_read(t),
            None => Int::from_u64(self.z3_ctx, 1),
        }
    }

    /// Element count from two pointer fields sharing the same allocation:
    /// `(end.offset - ptr.offset) / elem_size`. When both pointers carry an
    /// element-structured offset (`OffsetKind::Element`, or the base), the
    /// count is computed element-wise (`end_elem - ptr_elem`) so the
    /// `(end·S - ptr·S)/S` division is avoided for a generic element size `S`.
    pub(crate) fn iter_len_from_ptrs(
        &self,
        ptr: &VmValue<'z3, 'tcx>,
        end: &VmValue<'z3, 'tcx>,
    ) -> Option<Int<'z3>> {
        let pp = ptr.provenance.as_ref()?;
        let ep = end.provenance.as_ref()?;
        if pp.alloc_id != ep.alloc_id {
            return None;
        }
        let elem_of = |p: &Provenance<'z3>| -> Option<Int<'z3>> {
            match &p.offset_kind {
                Some(OffsetKind::Element(e)) => Some(e.clone()),
                Some(OffsetKind::Field) | None => Some(Int::from_u64(self.z3_ctx, 0)),
                _ => None,
            }
        };
        if let (Some(pe), Some(ee)) = (elem_of(pp), elem_of(ep)) {
            return Some(Int::sub(self.z3_ctx, &[&ee, &pe]));
        }
        let sz = self.iter_elem_size(ptr);
        let diff = Int::sub(self.z3_ctx, &[&ep.offset, &pp.offset]);
        Some(diff.div(&sz))
    }

    /// Remaining element count of an Iter/IterMut from its two pointer fields.
    /// When a tracked pointer offset exists (`iter_ptr_offset`), prefers the
    /// compact `base_len - offset` form; otherwise falls back to
    /// `(end.offset - ptr.offset) / elem_size`.
    pub(crate) fn iter_remaining_len_from_ptrs(
        &self,
        ptr: &VmValue<'z3, 'tcx>,
        end: &VmValue<'z3, 'tcx>,
        iter_owner: Option<&(AllocId, Int<'z3>)>,
    ) -> Option<Int<'z3>> {
        let ep = end.provenance.as_ref()?;
        let sz = self.iter_elem_size(ptr);
        if let Some((_, offset, base_len_elem)) = iter_owner
            .and_then(|id| self.constraints.term_caches.iter_ptr_offset.get(id))
        {
            let base_len = base_len_elem.clone().unwrap_or_else(|| ep.offset.div(&sz));
            let zero = Int::from_u64(self.z3_ctx, 0);
            Some(
                offset
                    .gt(&base_len)
                    .ite(&zero, &Int::sub(self.z3_ctx, &[&base_len, offset])),
            )
        } else {
            self.iter_len_from_ptrs(ptr, end)
        }
    }

    /// Find the local whose symbolic address matches `term` (the address a
    /// reference value points at). Used to resolve a `&self`/`&mut self`
    /// receiver (often a reborrow temp) back to the referent local that carries
    /// the materialized field values.
    pub(crate) fn find_local_by_address(&self, term: &Int<'z3>) -> Option<Local> {
        for (local, id) in &self.current_frame.local_alloc {
            if self.units[id.0].allocation.base == *term {
                return Some(*local);
            }
        }
        None
    }

    pub(crate) fn write_through_pointer(
        &mut self,
        pointer: &VmValue<'z3, 'tcx>,
        path: Vec<usize>,
        value: VmValue<'z3, 'tcx>,
    ) {
        let caller_referent = self.inline.arg_referents.iter().enumerate().find_map(|(i, referent)| {
            let param = Local::from_usize(i + 1);
            self.local_value(param)
                .filter(|arg| arg.z3_term == pointer.z3_term)
                .and_then(|_| *referent)
        });
        if let Some(local) = caller_referent {
            self.inline.deferred_field_writes.push((local, path, value));
        } else if let Some(local) = self.find_local_by_address(&pointer.z3_term) {
            if path.is_empty() {
                self.set_local(local, value);
            } else {
                self.set_field_value(local, path, value);
            }
        }
    }

    pub(crate) fn replay_deferred_writes(
        &mut self,
        writes: Vec<(Local, Vec<usize>, VmValue<'z3, 'tcx>)>,
    ) {
        for (local, path, value) in writes {
            let arg_idx = local.as_usize().checked_sub(1);
            let outer_referent = arg_idx
                .and_then(|i| self.inline.arg_referents.get(i).copied().flatten())
                .filter(|_| matches!(self.body().local_decls[local].ty.kind(), TyKind::Ref(..) | TyKind::RawPtr(..)));
            if let Some(referent) = outer_referent {
                self.inline.deferred_field_writes.push((referent, path, value));
            } else if path.is_empty() {
                self.set_local(local, value);
            } else {
                self.set_field_value(local, path, value);
            }
        }
    }

    /// Resolve a *whole-place* reborrow (`_7 = &mut (*_1)` / `_7 = &(*_1)`,
    /// projection exactly `[Deref]`) back to its referent local.  Used to
    /// propagate the referent's materialized field values into an inlined
    /// callee when the reborrow temp's own forward assignment was pruned from
    /// the slice (so its value is still the stack-address default and
    /// `find_local_by_address` can only self-match).  Deliberately excludes
    /// field reborrows (`&mut (*_x).field`) — those address a subfield, whose
    /// value is tracked separately, so propagating the whole struct's fields
    /// would be wrong (BTreeMap's `NodeRef` handles).
    pub(crate) fn find_whole_reborrow_referent(&self, local: Local) -> Option<Local> {
        use rustc_middle::mir::{ProjectionElem, Rvalue, StatementKind};
        for bb in self.body().basic_blocks.iter() {
            for stmt in &bb.statements {
                if let StatementKind::Assign(assign) = &stmt.kind {
                    let (dest, rvalue) = &**assign;
                    if dest.local == local && dest.projection.is_empty()
                        && let Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) = rvalue
                            && place.projection.len() == 1
                                && matches!(place.projection[0].kind(), ProjectionElem::Deref)
                            {
                                return Some(place.local);
                            }
                }
            }
        }
        None
    }

    /// Resolve a *field* reborrow (`_7 = &mut (*_x).field`, projection
    /// `[Deref, Field(..)*]`) back to its referent local plus the field path.
    pub(crate) fn find_field_reborrow_referent(
        &self,
        local: Local,
    ) -> Option<(Local, Vec<usize>)> {
        use rustc_middle::mir::{ProjectionElem, Rvalue, StatementKind};
        for bb in self.body().basic_blocks.iter() {
            for stmt in &bb.statements {
                if let StatementKind::Assign(assign) = &stmt.kind {
                    let (dest, rvalue) = &**assign;
                    if dest.local == local && dest.projection.is_empty()
                        && let Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) = rvalue {
                            let mut proj = place.projection.iter();
                            if !matches!(proj.next().map(|p| p.kind()), Some(ProjectionElem::Deref))
                            {
                                continue;
                            }
                            let mut fields = Vec::new();
                            for p in proj {
                                if let ProjectionElem::Field(f, _) = p.kind() {
                                    fields.push(f.as_usize());
                                } else {
                                    fields.clear();
                                    break;
                                }
                            }
                            if !fields.is_empty() {
                                return Some((place.local, fields));
                            }
                        }
                }
            }
        }
        None
    }

    /// Resolve a whole-place copy root: `_x = copy _y` / `_x = move _y` (no
    /// projection) traces `_x` back to `_y`. Used to recover a value parameter's
    /// materialized fields when the optimizer inserted a copy temporary between
    /// the caller's argument and the inlined callee's parameter (e.g.
    /// `get_ext`'s `_2 = copy _1` before `NonZero::get(move _2)`), so that
    /// `handle_callee_entry`'s field collection can follow the copy chain to the
    /// local that actually carries the fields.
    pub(crate) fn find_copy_root(&self, local: Local) -> Option<Local> {
        use rustc_middle::mir::{Rvalue, StatementKind};
        for bb in self.body().basic_blocks.iter() {
            for stmt in &bb.statements {
                if let StatementKind::Assign(assign) = &stmt.kind {
                    let (dest, rvalue) = &**assign;
                    if dest.local == local && dest.projection.is_empty() {
                        let op = match rvalue {
                            Rvalue::Use(op, ..) => Some(op),
                            _ => None,
                        };
                        if let Some(Operand::Copy(p) | Operand::Move(p)) = op
                            && p.projection.is_empty()
                        {
                            return Some(p.local);
                        }
                    }
                }
            }
        }
        None
    }

    /// If arg_val is a reference to an Iter or IterMut struct, return the
    /// local index of the referent (so field values can be looked up).
    /// Since len()/is_empty() always take &self, local 1 is the receiver.
    pub(crate) fn find_iter_self_local(&self, arg_val: &VmValue<'z3, 'tcx>) -> Option<Local> {
        match arg_val.ty.kind() {
            TyKind::Ref(_, pointee, _) => match pointee.kind() {
                TyKind::Adt(adt_def, _) => {
                    if api_classify::is_std_iter_or_itermut(adt_def.did()) {
                        // Find the local holding the iterator by matching the
                        // reference's address term against known local addresses
                        // (`&mut _iter` has term `addr__iter`).  A hardcoded
                        // `Local(1)` only holds for inlined `next` bodies where
                        // the iterator is the first argument; direct trait
                        // `Iterator::next` calls keep the iterator at an
                        // arbitrary local.
                        if let Some(local) = self.find_local_by_address(&arg_val.z3_term) {
                            return Some(local);
                        }
                        // Fallback for inlined `next` bodies (iter bound to arg 1).
                        return Some(Local::from_usize(1));
                    }
                    None
                }
                TyKind::Param(_) => self.find_local_by_address(&arg_val.z3_term).or_else(|| {
                    let receiver = Local::from_usize(1);
                    self.iter_ptr_end(receiver).map(|_| receiver)
                }),
                _ => None,
            },
            _ => None,
        }
    }

    /// Apply a `ReturnRange` effect: model `slice::range(range, bounds)`
    /// returning `Range { start, end }` with `0 <= start <= end <= bounds.end`.
    /// The `bounds` argument is a `RangeTo<usize>` whose field 0 carries the
    /// slice length; the returned `Range<usize>` fields are fresh symbols bound
    /// by the range invariant.
    pub(crate) fn apply_range_effect(
        &mut self,
        bounds_arg: usize,
        args: &[VmValue<'z3, 'tcx>],
        caller_arg_locals: &[Option<Local>],
        dest: Local,
    ) {
        let dest_ty = self.body().local_decls[dest].ty;
        let TyKind::Adt(adt, substs) = dest_ty.kind() else {
            return;
        };
        let variant = adt.non_enum_variant();
        let field_ty = |idx: usize| -> Ty<'tcx> {
            variant
                .fields
                .iter()
                .nth(idx)
                .map(|f| mir_utils::field_ty(self.tcx, f, substs))
                .unwrap_or(dest_ty)
        };

        // Resolve `bounds.end` (the slice length): prefer the materialized
        // field 0 of the `RangeTo<usize>` argument, falling back to the
        // argument's own term.
        let mut len_term = None;
        if let Some(l) = caller_arg_locals.get(bounds_arg).copied().flatten()
            && let Some(fv) = self.field_value(l, &[0]) {
                len_term = Some(fv.z3_term.clone());
            }
        let len_term = len_term.or_else(|| args.get(bounds_arg).map(|v| v.z3_term.clone()));
        let Some(len_term) = len_term else {
            return;
        };

        let start = self.fresh_int(&format!("range_start_{}", dest.as_usize()));
        let end = self.fresh_int(&format!("range_end_{}", dest.as_usize()));
        let zero = Int::from_u64(self.z3_ctx, 0);
        self.constraints.assertions.push(start.ge(&zero));
        self.constraints.assertions.push(start.le(&end));
        self.constraints.assertions.push(end.le(&len_term));

        let start_val = VmValue::new(start, field_ty(0));
        let end_val = VmValue::new(end, field_ty(1));
        self.set_field_value(dest, vec![0], start_val);
        self.set_field_value(dest, vec![1], end_val);
    }

    /// Compute the `(ptr, cap, len)` field paths of a `Vec`-shaped local, handling
    /// both the std `Vec<T>` layout `{ buf: RawVec { ptr, cap }, len }` and the
    /// flat local re-implementation `{ ptr: NonNull, len, cap }` used by the
    /// std-challenge suites.
    /// Materialize the `{ptr, cap, len}` field values of a `Vec<T>` aggregate
    /// at `local`. The backing-buffer pointer is written to the owning raw
    /// pointer field (located generically via [`Self::container_ptr_field`]);
    /// the `len`/`cap` are no longer materialized as fields — they are asserted
    /// as path conditions and tracked by the backing allocation's slice length.
    ///
    /// The symbolic invariant `0 <= len <= cap` and `cap * elem_size <=
    /// isize::MAX` is asserted as a path condition so downstream `len()` /
    /// `capacity()` / `InBound` / `ValidNum` queries agree.
    pub(crate) fn materialize_vec_fields(
        &mut self,
        local: Local,
        ptr: VmValue<'z3, 'tcx>,
        cap: Int<'z3>,
        len: Int<'z3>,
    ) {
        let elem_size = self.size_of_ty(ptr.ty).max(1);
        let ty = self.body().local_decls[local].ty;
        let ptr_path = self
            .container_ptr_field(ty)
            .expect("materialize_vec_fields: container has no owning pointer field");
        self.set_field_value(local, ptr_path, ptr);
        self.materialize_vec_len_cap(cap, len, elem_size);
    }

    /// Assert the Vec length/capacity invariants `0 <= len <= cap` and
    /// `cap * elem_size <= isize::MAX` as path conditions.
    pub(crate) fn materialize_vec_len_cap(
        &mut self,
        cap: Int<'z3>,
        len: Int<'z3>,
        elem_size: u64,
    ) {
        let zero = Int::from_u64(self.z3_ctx, 0);
        self.constraints.assertions.push(len.ge(&zero));
        self.constraints.assertions.push(len.le(&cap));
        self.constraints.assertions.push(cap.ge(&zero));
        // Language invariant: a Vec's byte length fits in `isize::MAX`, so the
        // `from_raw_parts`/`from_raw_parts_mut` precondition
        // `size_of(T) * len <= isize::MAX` is provable from the materialized
        // fields (`len <= cap` and `cap * elem_size <= isize::MAX`).
        let isize_max = Int::from_u64(self.z3_ctx, isize::MAX as u64);
        let elem_term = Int::from_u64(self.z3_ctx, elem_size.max(1));
        self.constraints.assertions
            .push(Int::mul(self.z3_ctx, &[&cap, &elem_term]).le(&isize_max));
    }
}
