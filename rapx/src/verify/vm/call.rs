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
use z3::ast::{Ast, Bool, Int};
use z3::{SatResult, Solver};

use crate::compat::{FxHashSet, Spanned};
use crate::helpers::mir_utils;
use crate::limit::MAX_INLINE_DEPTH;
use crate::verify::api_classify;
use crate::verify::call_summary::{self, BoundedArithmeticOp, CallEffect, OverflowOp};
use super::state::{AllocId, AllocKind, ElementTy, MemoryContent, OffsetKind, Provenance, ValueFacts, ValueSource, VmState, VmValue};

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
                TerminatorKind::Goto { target } => stack.push((state, *target, visited)),
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
    fn set_dest_as_heap_ptr(&mut self, arg_val: &VmValue<'z3, 'tcx>, dest: Local) {
        let mut val = arg_val.clone();
        val.ty = self.body().local_decls[dest].ty;
        val.facts.non_null = true;
        val.facts.init = true;
        self.set_local(dest, val);
    }

    /// Apply a binary numeric effect: compute `f(lhs.z3_term, rhs.z3_term)` and store
    /// it as the destination's fresh scalar value.
    fn apply_binary_num(
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

    /// Apply a unary numeric effect: compute `f(a.z3_term)` and store it as the
    /// destination's fresh scalar value.
    /// Apply a single call effect to the VM state.
    pub(crate) fn apply_call_effect(
        &mut self,
        effect: &CallEffect,
        args: &[VmValue<'z3, 'tcx>],
        caller_arg_locals: &[Option<Local>],
        dest: Local,
        callee: Option<DefId>,
        func: &Operand<'tcx>,
    ) {
        match effect {
            CallEffect::ReturnLayoutSymbolic { is_size } => {
                let ty = mir_utils::fn_def_first_type_arg(func)
                    .expect("layout effect built from a FnDef");
                let term = if *is_size {
                    self.size_sym(ty)
                } else {
                    self.align_sym(ty)
                };
                let dest_ty = self.body().local_decls[dest].ty;
                self.set_local(dest, VmValue::new(term, dest_ty));
            }
            CallEffect::ReturnAliasArg { arg } => {
                if let Some(arg_val) = args.get(*arg) {
                    self.set_dest_as_heap_ptr(arg_val, dest);
                }
            }
            CallEffect::ReturnArgValue { arg } => {
                if let Some(arg_val) = args.get(*arg) {
                    let mut val = arg_val.clone();
                    val.ty = self.body().local_decls[dest].ty;
                    val.facts.init = true;
                    self.set_local(dest, val);
                }
            }
            CallEffect::SelectUnpredictable => {
                if args.len() >= 3 {
                    let term = self.fresh_int(&format!("selunpred_{}", dest.as_usize()));
                    let dest_ty = self.body().local_decls[dest].ty;
                    let eq1 = term._eq(&args[1].z3_term);
                    let eq2 = term._eq(&args[2].z3_term);
                    self.constraints.assertions.push(Bool::or(self.z3_ctx, &[&eq1, &eq2]));
                    let prov = args[1]
                        .provenance
                        .clone()
                        .or_else(|| args[2].provenance.clone());
                    self.set_local(
                        dest,
                        VmValue {
                            z3_term: term,
                            ty: dest_ty,
                            provenance: prov,
                            facts: ValueFacts::default(),
                            source: ValueSource::None,
                        },
                    );
                }
            }
            CallEffect::ReturnDerefArg { arg } => {
                // `mem::replace(dest, src)` returns `*dest`: the pointee value,
                // not the `&mut` reference. Prefer the materialized pointee
                // (the empty-path field value, set by
                // `propagate_field_values_to_ref` for `&mut self.field`); then
                // recover the old field value from the materialized field maps;
                // finally, when the borrow chain was dropped by the slicer and no
                // field value is recoverable, model the returned slice as a fresh
                // external allocation so a downstream `Allocated`/`InBound` can
                // still match `[T]` vs `T`.
                let dest_ty = self.body().local_decls[dest].ty;
                let mut val = args.get(*arg).cloned().unwrap_or_else(|| VmValue::new(self.fresh_int("replaced"), dest_ty));
                // `mem::replace(&mut dest, src)` returns `*dest`: the pointee
                // value, not the `&mut` reference.  With M2 the reference's
                // `path == []` holds its *address* (whole value), so the pointee
                // is recovered from the materialized field maps by type +
                // provenance (e.g. `self.v: *mut [T]`), or — when the borrow
                // chain was dropped by the slicer and no field value is
                // recoverable — modeled as a fresh external allocation so a
                // downstream `Allocated`/`InBound` can still match `[T]` vs `T`.
                if let Some(search) = self
                    .units
                    .iter()
                    .flat_map(|u| u.content.values.values())
                    .find(|v| v.ty == dest_ty && v.is_pointer())
                    .cloned()
                {
                    val = search;
                } else if let Some(elem) = mir_utils::pointee_ty(dest_ty) {
                    let is_slice = matches!(elem.kind(), rustc_middle::ty::TyKind::Slice(_));
                    if is_slice {
                        let elem_align = self.align_sym(elem);
                        let (alloc_id, base) = self.allocate_external(
                            Int::from_u64(self.z3_ctx, i64::MAX as u64),
                            elem_align,
                            Some(elem),
                        );
                        val = VmValue {
                            z3_term: base,
                            ty: dest_ty,
                            provenance: Some(Provenance {
                                alloc_id,
                                offset: Int::from_u64(self.z3_ctx, 0),
                                offset_kind: None,
                            }),
                            facts: ValueFacts::default(),
                            source: ValueSource::None,
                        };
                    }
                }
                val.ty = dest_ty;
                self.set_local(dest, val);
            }
            CallEffect::ReturnTransparentDeref { arg, peel } => {
                if let Some(arg_val) = args.get(*arg) {
                    self.set_dest_as_heap_ptr(arg_val, dest);
                    // Peel `peel` leading field-0 hops off the argument's
                    // pointee field values (ManuallyDrop.value → MaybeDangling.0)
                    // and expose them as the deref result's pointee fields.
                    if let Some(arg_local) = caller_arg_locals.get(*arg).copied().flatten() {
                        let keys: Vec<Vec<usize>> = self.field_paths(arg_local);
                        for path in keys {
                            if path.len() > *peel && path[..*peel].iter().all(|&f| f == 0)
                                && let Some(v) = self.field_value(arg_local, &path).cloned() {
                                    self.set_field_value(dest, path[*peel..].to_vec(), v);
                                }
                        }
                    }
                }
            }
            CallEffect::ReturnTupleFieldLength {
                field: _field,
                from_arg: _from_arg,
            } => {
                if args.len() < 2 {
                    return;
                }
                let self_val = &args[0]; // &[T]
                let mid_val = &args[1]; // usize

                let dest_ty = self.body().local_decls[dest].ty;
                if let TyKind::Tuple(elem_tys) = dest_ty.kind() {
                    // Look up the source allocation from self's provenance.
                    let src_alloc_id = self_val.provenance.as_ref().map(|p| p.alloc_id);

                    let (elem_ty, elem_sz_term, alloc_size) = src_alloc_id
                        .map(|id| self.alloc(id))
                        .map(|a| {
                            let ty = a.element_ty.as_ty();
                            let sz_term = self.size_sym_read(ty.unwrap_or(self_val.ty));
                            (ty, sz_term, a.size.clone())
                        })
                        .unwrap_or_else(|| {
                            // Provenance lost (e.g. `mem::replace` on a raw field
                            // whose borrow the slicer dropped): fall back to the
                            // slice pointee type so `InBound`/`Allocated` can
                            // still match `[T]` against the element `T`.
                            let pointee = mir_utils::pointee_ty(self_val.ty);
                            let sz = self.size_sym_read(pointee.unwrap_or(self_val.ty));
                            (pointee, sz, Int::from_u64(self.z3_ctx, 1))
                        });

                    let total_len = self
                        .slice_len_from_value(self_val)
                        .unwrap_or_else(|| alloc_size.div(&elem_sz_term)); // self.len()

                    let zero = Int::from_u64(self.z3_ctx, 0);
                    self.constraints.assertions.push(mid_val.z3_term.ge(&zero));
                    self.constraints.assertions.push(mid_val.z3_term.le(&total_len));

                    // mid (field 0 length)
                    let mid = mid_val.z3_term.clone();
                    // self.len() - mid (field 1 length)
                    let rest_len = Int::sub(self.z3_ctx, &[&total_len, &mid]);

                    // mid byte offset for field 1 pointer
                    let mid_bytes = Int::mul(self.z3_ctx, &[&mid, &elem_sz_term]);
                    let ptr1 = Int::add(self.z3_ctx, &[&self_val.z3_term, &mid_bytes]);

                    for f in 0..elem_tys.len() {
                        let field_ty = elem_tys[f];
                        let (field_len, field_ptr) = if f == 0 {
                            (mid.clone(), self_val.z3_term.clone())
                        } else {
                            (rest_len.clone(), ptr1.clone())
                        };
                        let field_size = Int::mul(self.z3_ctx, &[&field_len, &elem_sz_term]);
                        let field_alloc_align = self_val
                            .provenance
                            .as_ref()
                            .map(|p| self.alloc(p.alloc_id).align.clone())
                            .unwrap_or_else(|| Int::from_u64(self.z3_ctx, 1));

                        let (alloc_id, _base) = self.allocate_slice(
                            field_len.clone(),
                            elem_sz_term.clone(),
                            field_alloc_align.clone(),
                            elem_ty,
                        );
                        let src_bytes = Int::mul(self.z3_ctx, &[&total_len, &elem_sz_term]);
                        if f == 0 {
                            self.constraints.assertions.push(field_size._eq(&mid_bytes));
                        } else {
                            let remaining = Int::sub(self.z3_ctx, &[&src_bytes, &mid_bytes]);
                            self.constraints.assertions.push(field_size._eq(&remaining));
                        }
                        self.content_mut(alloc_id).facts.initialized = true;
                        if let Some(ref source_prov) = self_val.provenance {
                            self.alloc_mut(alloc_id).parent = Some(source_prov.alloc_id);
                        }

                        let field_offset = Int::from_u64(self.z3_ctx, 0);

                        let field_prov = Provenance {
                            alloc_id,
                            offset: field_offset,
                            offset_kind: None,
                        };

                        let field_val = VmValue {
                            z3_term: field_ptr,
                            ty: field_ty,
                            provenance: Some(field_prov),
                            facts: ValueFacts {
                                init: true,
                                non_null: true,
                                in_bounds: true,
                                align_n: Some(field_alloc_align),
                            },
                            source: ValueSource::None,
                        };
                        self.set_field_value(dest, vec![f], field_val);
                    }
                }
            }
            CallEffect::ReturnRange { bounds_arg } => {
                self.apply_range_effect(*bounds_arg, args, caller_arg_locals, dest);
            }
            CallEffect::ReturnAlignTo { receiver_arg } => {
                let Some(self_val) = args.get(*receiver_arg).cloned() else {
                    return;
                };
                let dest_ty = self.body().local_decls[dest].ty;
                let TyKind::Tuple(elem_tys) = dest_ty.kind() else {
                    return;
                };
                if elem_tys.len() < 3 {
                    return;
                }

                // Body element type U is the pointee of field 1 (`&[U]`).
                let body_elem_ty = match elem_tys[1].kind() {
                    TyKind::Ref(_, inner, _) => match inner.kind() {
                        TyKind::Slice(u) => *u,
                        _ => return,
                    },
                    _ => return,
                };
                let size_u = self.size_of_ty(body_elem_ty).max(1);
                let align_u = self.align_sym(body_elem_ty);

                let Some(src_prov) = self_val.provenance.clone() else {
                    return;
                };
                let alloc = self.alloc(src_prov.alloc_id);
                let (elem_ty, elem_sz, len_bytes) = {
                    let ty = alloc.element_ty.as_ty();
                    let sz = self.size_of_ty(ty.unwrap_or(self_val.ty)).max(1);
                    (ty, sz, alloc.size.clone())
                };

                let elem_sz_term = Int::from_u64(self.z3_ctx, elem_sz);
                let size_u_term = Int::from_u64(self.z3_ctx, size_u);

                // Fresh aligned offset: (ptr + offset) % align_u == 0 and
                // 0 <= offset < align_u.
                let offset = self.fresh_int(&format!("align_to_offset_{}", dest.as_usize()));
                let zero = Int::from_u64(self.z3_ctx, 0);
                let ptr_plus_offset = Int::add(self.z3_ctx, &[&self_val.z3_term, &offset]);
                self.constraints.assertions
                    .push(ptr_plus_offset.rem(&align_u)._eq(&zero));
                self.constraints.assertions.push(offset.ge(&zero));
                self.constraints.assertions.push(offset.lt(&align_u));

                // body = len_bytes - offset bytes split into size_u chunks; the
                // remainder is the suffix. Record the Euclidean identity so that
                // `len - offset - suffix = body_len * size_u` (a multiple of
                // align_u) is derivable downstream.
                let body_bytes = Int::sub(self.z3_ctx, &[&len_bytes, &offset]);
                let body_len = body_bytes.div(&size_u_term);
                let suffix_bytes = body_bytes.rem(&size_u_term);
                let mul_term = Int::mul(self.z3_ctx, &[&body_len, &size_u_term]);
                let sum_term = Int::add(self.z3_ctx, &[&mul_term, &suffix_bytes]);
                self.constraints.assertions.push(body_bytes._eq(&sum_term));
                self.constraints.assertions.push(suffix_bytes.ge(&zero));
                self.constraints.assertions.push(suffix_bytes.lt(&size_u_term));

                // Field lengths in elements.
                let prefix_len = offset.div(&elem_sz_term);
                let suffix_len = suffix_bytes.div(&elem_sz_term);

                let body_byte_len = Int::mul(self.z3_ctx, &[&body_len, &size_u_term]);
                let suffix_ptr = Int::add(self.z3_ctx, &[&ptr_plus_offset, &body_byte_len]);

                let base_align = self.alloc(src_prov.alloc_id).align.clone();

                let fields: Vec<(Int<'z3>, Int<'z3>, Ty<'tcx>, u64, Int<'z3>)> = vec![
                    (
                        prefix_len,
                        self_val.z3_term.clone(),
                        elem_tys[0],
                        elem_sz,
                        base_align.clone(),
                    ),
                    (body_len, ptr_plus_offset, elem_tys[1], size_u, align_u),
                    (suffix_len, suffix_ptr, elem_tys[2], elem_sz, base_align),
                ];

                for (f, (f_len, f_ptr, f_ty, f_elem_sz, f_align)) in fields.into_iter().enumerate()
                {
                    let f_elem_ty = if f == 1 { Some(body_elem_ty) } else { elem_ty };
                    let (alloc_id, _) = self.allocate_slice(
                        f_len.clone(),
                        Int::from_u64(self.z3_ctx, f_elem_sz),
                        f_align.clone(),
                        f_elem_ty,
                    );
                    self.content_mut(alloc_id).facts.initialized = true;
                    self.alloc_mut(alloc_id).parent = Some(src_prov.alloc_id);
                    let field_val = VmValue {
                        z3_term: f_ptr,
                        ty: f_ty,
                        provenance: Some(Provenance {
                            alloc_id,
                            offset: Int::from_u64(self.z3_ctx, 0),
                            offset_kind: None,
                        }),
                        facts: ValueFacts {
                            init: true,
                            non_null: true,
                            in_bounds: true,
                            align_n: if f_align.simplify().as_u64() != Some(1) {
                                Some(f_align)
                            } else {
                                None
                            },
                        },
                        source: ValueSource::None,
                    };
                    self.set_field_value(dest, vec![f], field_val);
                }
            }
            CallEffect::ReturnPointerFromArg { arg } => {
                if let Some(arg_val) = args.get(*arg) {
                    let mut val = arg_val.clone();
                    let dest_ty = self.body().local_decls[dest].ty;
                    val.ty = dest_ty;
                    // The returned pointer aliases `arg`, so it is non-null
                    // exactly when the source is. The source is non-null either
                    // because its value already carries the fact, or by its
                    // *type*: a reference (`&`/`&mut`) is never null, and
                    // `NonNull` is non-null by invariant.
                    let src_non_null = arg_val.facts.non_null
                        || matches!(arg_val.ty.kind(), rustc_middle::ty::TyKind::Ref(..))
                        || matches!(
                            arg_val.ty.kind(),
                            rustc_middle::ty::TyKind::Adt(adt, _)
                                if api_classify::is_std_nonnull(adt.did())
                        );
                    val.facts.non_null = src_non_null;
                    // Preserve the tracked alignment so `as_ptr().deref()` can
                    // discharge the `raw-ptr-deref` `Align` check (Iter::next).
                    val.facts.align_n = arg_val.facts.align_n.clone();
                    // Pointer-returning APIs expose the backing allocation;
                    // mark it init-accessible for raw pointer types.
                    if matches!(dest_ty.kind(), rustc_middle::ty::TyKind::RawPtr(..)) {
                        val.facts.init = true;
                    }
                    // For heap-backed containers (Vec/CString/String) and slice
                    // views: redirect as_ptr() from the struct/slice allocation
                    // to the heap data allocation.
                    if let Some(ref prov) = val.provenance
                        && let Some(data_alloc) = self.data_alloc_of(prov.alloc_id, arg_val.ty) {
                            val.z3_term = self.allocation_base(data_alloc).clone();
                            val.provenance = Some(Provenance {
                                alloc_id: data_alloc,
                                offset: Int::from_u64(self.z3_ctx, 0),
                                offset_kind: None,
                            });
                        }
                    if src_non_null {
                        let zero = Int::from_u64(self.z3_ctx, 0);
                        self.constraints.assertions.push(val.z3_term._eq(&zero).not());
                    }
                    self.set_local(dest, val);
                }
            }
            CallEffect::ReturnPointerAdd {
                base_arg,
                offset_arg,
                stride,
                dereferenceable,
            } => {
                if let (Some(base), Some(offset)) = (args.get(*base_arg), args.get(*offset_arg)) {
                    self.apply_pointer_add(dest, base, offset, *stride, *dereferenceable);
                }
            }
            CallEffect::ReturnPtrOffsetFrom { ptr_arg, base_arg } => {
                let dest_ty = self.body().local_decls[dest].ty;
                let ptr = args.get(*ptr_arg).cloned();
                let base = args.get(*base_arg).cloned();
                let count = match (ptr.as_ref(), base.as_ref()) {
                    (Some(p), Some(b)) => self.iter_remaining_len_from_ptrs(b, p, None).unwrap_or_else(
                        || self.fresh_int(&format!("ptr_offset_from_{}", dest.as_usize())),
                    ),
                    _ => self.fresh_int(&format!("ptr_offset_from_{}", dest.as_usize())),
                };
                self.set_local(
                    dest,
                    VmValue {
                        z3_term: count,
                        ty: dest_ty,
                        provenance: None,
                        facts: ValueFacts::default(),
                        source: ValueSource::None,
                    },
                );
            }
            CallEffect::ReturnNonZero => {
                let zero = Int::from_u64(self.z3_ctx, 0);
                if let Some(mut existing) = self.local_value(dest).cloned() {
                    existing.facts.non_null = true;
                    // Record the non-zero fact as a path condition so that a
                    // downstream `ValidNum(result != 0)` obligation (e.g.
                    // `NonZero::new_unchecked` after a bit-preserving operation)
                    // discharges against it.
                    self.constraints.assertions.push(existing.z3_term._eq(&zero).not());
                    self.set_local(dest, existing);
                } else {
                    let dest_ty = self.body().local_decls[dest].ty;
                    let term = self.fresh_int(&format!("ret_nz_{}", dest.as_usize()));
                    self.constraints.assertions.push(term._eq(&zero).not());
                    self.set_local(
                        dest,
                        VmValue {
                            z3_term: term,
                            ty: dest_ty,
                            provenance: None,
                            facts: ValueFacts {
                                non_null: true,
                                ..Default::default()
                            },
                            source: ValueSource::None,
                        },
                    );
                }
            }
            CallEffect::ReturnAligned => {
                if let Some(mut existing) = self.local_value(dest).cloned() {
                    // `as_ptr`/`as_mut_ptr`/`into_raw` expose a pointer aligned to
                    // the *pointee* type, so record the symbolic alignment for the
                    // downstream `raw-ptr-deref`/`from_raw_parts` `Align` check.
                    if existing.facts.align_n.is_none() {
                        let dest_ty = self.body().local_decls[dest].ty;
                        if let Some(pointee) = mir_utils::pointee_ty(dest_ty) {
                            let a = self.align_sym(pointee);
                            if a.simplify().as_u64() != Some(1) {
                                existing.facts.align_n = Some(a);
                            }
                        }
                    }
                    self.set_local(dest, existing);
                } else {
                    let dest_ty = self.body().local_decls[dest].ty;
                    let term = self.fresh_int(&format!("ret_align_{}", dest.as_usize()));
                    self.set_local(
                        dest,
                        VmValue {
                            z3_term: term,
                            ty: dest_ty,
                            provenance: None,
                            facts: ValueFacts {
                                ..Default::default()
                            },
                            source: ValueSource::None,
                        },
                    );
                }
            }
            CallEffect::ReturnConst { value } => {
                let dest_ty = self.body().local_decls[dest].ty;
                let term = Int::from_u64(self.z3_ctx, *value);
                let val = VmValue::new(term, dest_ty);
                self.set_local(dest, val);
            }
            CallEffect::ReturnAlignOffset { ptr_arg, align_arg } => {
                let dest_ty = self.body().local_decls[dest].ty;
                let offset = self.fresh_int(&format!("align_offset_{}", dest.as_usize()));
                if let (Some(ptr_val), Some(align_val)) = (args.get(*ptr_arg), args.get(*align_arg))
                {
                    // `ptr.align_offset(align)` returns the offset in *elements* of
                    // the pointee type (not bytes), so the aligned address is
                    // `ptr + offset * size_of::<pointee>()`.  Record that
                    // `(ptr + offset*elem) % align == 0` with `0 <= offset < align`
                    // so a downstream `*(ptr.add(offset) as *const U)` can
                    // discharge `Align`.
                    let elem = mir_utils::pointee_ty(ptr_val.ty)
                        .map(|pointee| self.size_sym(pointee))
                        .unwrap_or_else(|| Int::from_u64(self.z3_ctx, 1));
                    let byte_off = Int::mul(self.z3_ctx, &[&offset, &elem]);
                    let ptr_plus_off = Int::add(self.z3_ctx, &[&ptr_val.z3_term, &byte_off]);
                    let zero = Int::from_u64(self.z3_ctx, 0);
                    self.constraints.assertions
                        .push(ptr_plus_off.rem(&align_val.z3_term)._eq(&zero));
                    self.constraints.assertions.push(offset.ge(&zero));
                    self.constraints.assertions.push(offset.lt(&align_val.z3_term));
                }
                let val = VmValue::new(offset, dest_ty);
                self.set_local(dest, val);
            }
            CallEffect::ReturnMin { lhs_arg, rhs_arg } => {
                // Build the min as a first-class `ite(lhs <= rhs, lhs, rhs)`
                // term rather than a fresh variable plus disjunction facts.
                // A fresh variable breaks downstream alignment/bounds
                // reasoning: e.g. `ptr.align_offset(8)` guarantees
                // `(ptr + offset) % 8 == 0`, but `offset.min(len)` would
                // then become an unrelated symbol and the `Align`/`InBound`
                // checks on `*(ptr.add(offset) as *const usize)` could no
                // longer discharge.  With an `ite`, the path conditions
                // (`offset < 8`, `len >= 16`) let the solver reduce
                // `ite(offset <= len, offset, len)` back to `offset`.
                self.apply_binary_num(dest, args, *lhs_arg, *rhs_arg, |lhs, rhs| {
                    lhs.le(rhs).ite(lhs, rhs)
                });
            }
            CallEffect::ReturnMax { lhs_arg, rhs_arg } => {
                self.apply_binary_num(dest, args, *lhs_arg, *rhs_arg, |lhs, rhs| {
                    lhs.ge(rhs).ite(lhs, rhs)
                });
            }
            CallEffect::ReturnAdd { lhs_arg, rhs_arg } => {
                self.apply_binary_num(dest, args, *lhs_arg, *rhs_arg, |lhs, rhs| {
                    Int::add(self.z3_ctx, &[lhs, rhs])
                });
            }
            CallEffect::ReturnMul { lhs_arg, rhs_arg } => {
                self.apply_binary_num(dest, args, *lhs_arg, *rhs_arg, |lhs, rhs| {
                    Int::mul(self.z3_ctx, &[lhs, rhs])
                });
            }
            CallEffect::ReturnBoundedArithmetic { lhs_arg, rhs_arg, op } => {
                if let (Some(lhs), Some(rhs)) = (args.get(*lhs_arg), args.get(*rhs_arg)) {
                    let dest_ty = self.body().local_decls[dest].ty;
                    let Some((min, max, modulus, signed)) = self.integer_limits(dest_ty)
                        .or_else(|| self.integer_limits(lhs.ty))
                    else {
                        return;
                    };
                    let raw = match op {
                        BoundedArithmeticOp::SaturatingAdd =>
                            Int::add(self.z3_ctx, &[&lhs.z3_term, &rhs.z3_term]),
                        BoundedArithmeticOp::SaturatingSub | BoundedArithmeticOp::WrappingSub =>
                            Int::sub(self.z3_ctx, &[&lhs.z3_term, &rhs.z3_term]),
                    };
                    let term = match op {
                        BoundedArithmeticOp::SaturatingAdd | BoundedArithmeticOp::SaturatingSub => {
                            raw.lt(&min).ite(&min, &raw.gt(&max).ite(&max, &raw))
                        }
                        BoundedArithmeticOp::WrappingSub => {
                            let wrapped = raw.modulo(&modulus);
                            if signed {
                                wrapped.gt(&max).ite(&Int::sub(self.z3_ctx, &[&wrapped, &modulus]), &wrapped)
                            } else {
                                wrapped
                            }
                        }
                    };
                    self.set_local(dest, VmValue::new(term, dest_ty));
                }
            }
            CallEffect::ReturnWithOverflow {
                lhs_arg,
                rhs_arg,
                op,
            } => {
                if let (Some(lhs), Some(rhs)) = (args.get(*lhs_arg), args.get(*rhs_arg)) {
                    let term = match op {
                        OverflowOp::Add => Int::add(self.z3_ctx, &[&lhs.z3_term, &rhs.z3_term]),
                        OverflowOp::Sub => Int::sub(self.z3_ctx, &[&lhs.z3_term, &rhs.z3_term]),
                        OverflowOp::Mul => Int::mul(self.z3_ctx, &[&lhs.z3_term, &rhs.z3_term]),
                    };
                    self.set_field_value(dest, vec![0], VmValue::new(term, lhs.ty));
                }
            }
            CallEffect::ReturnOptionSomeScanIndex { self_arg } => {
                // `Iterator::position`/`find` return `Option<usize>` whose `Some`
                // payload is a scan index into the iterator, so `0 <= i < self.len()`.
                // The receiver is `&mut iter` (a reference to the Iter/IterMut
                // struct), so resolve the reference to the iterator local it
                // points at (via its provenance = the iterator's stack alloc).
                // The iterator carries `ptr` (field 0) and `end_or_len`
                // (field 1); `len = end_or_len - ptr`.
                if let Some(iter_ref) = caller_arg_locals.get(*self_arg).copied().flatten() {
                    let iter_local = self
                        .local_value(iter_ref)
                        .and_then(|v| v.provenance_alloc_id())
                        .and_then(|alloc| {
                            self.current_frame.local_alloc
                                .iter()
                                .find(|(_, a)| **a == alloc)
                                .map(|(l, _)| *l)
                        });
                    let ptr_term =
                        iter_local.and_then(|l| self.field_value(l, &[0]).map(|v| v.z3_term.clone()));
                    let end_term =
                        iter_local.and_then(|l| self.field_value(l, &[1]).map(|v| v.z3_term.clone()));
                    if let (Some(ptr), Some(end)) = (ptr_term, end_term) {
                        let len = Int::sub(self.z3_ctx, &[&end, &ptr]);
                        let payload = self.fresh_int(&format!("scan_idx_{}", dest.as_usize()));
                        self.constraints.assertions.push(payload.lt(&len));
                        let dest_ty = self.body().local_decls[dest].ty;
                        let payload_ty = match dest_ty.kind() {
                            TyKind::Adt(adt, substs) if adt.is_enum() => substs.type_at(0),
                            _ => dest_ty,
                        };
                        self.set_field_value(
                            dest,
                            vec![0],
                            VmValue::new(payload, payload_ty),
                        );
                    }
                }
            }
            CallEffect::ReturnBranchPayload { arg } => {
                let dest_ty = self.body().local_decls[dest].ty;
                if let Some(value) = args.get(*arg)
                    && let Some(discr) = value.discriminant()
                    && let TyKind::Adt(adt, _) = value.ty.kind()
                {
                    let branch_discr = if self.tcx.is_diagnostic_item(rustc_span::sym::Option, adt.did()) {
                        let one = Int::from_u64(self.z3_ctx, 1);
                        Some(Int::sub(self.z3_ctx, &[&one, discr]))
                    } else if self.tcx.is_diagnostic_item(rustc_span::sym::Result, adt.did()) {
                        Some(discr.clone())
                    } else {
                        None
                    };
                    if let Some(branch_discr) = branch_discr {
                        let term = self.fresh_int("try_branch");
                        self.set_local(dest, VmValue {
                            z3_term: term,
                            ty: dest_ty,
                            provenance: None,
                            facts: ValueFacts::default(),
                            source: ValueSource::Discriminant(branch_discr),
                        });
                    }
                }
                let arg_local = caller_arg_locals.get(*arg).copied().flatten();
                if let Some(l) = arg_local
                    && let Some(payload) = self.field_value(l, &[0]).cloned() {
                        self.set_field_value(dest, vec![0], payload);
                    }
            }
            CallEffect::ReturnScanLength => {
                // `strlen(ptr)` returns the byte length before the NUL
                // terminator. The `ValidCStr` invariant guarantees the NUL is
                // within `isize::MAX` bytes, so `len < isize::MAX`, and
                // `len + 1` (the length with the terminator) fits in
                // `isize::MAX` — discharging `from_raw_parts`'s
                // `ValidNum(size_of(T)*(len+1) <= isize::MAX)`.
                let len = self.fresh_int(&format!("strlen_{}", dest.as_usize()));
                let max = Int::from_i64(self.z3_ctx, i64::MAX);
                self.constraints.assertions.push(len.lt(&max));
                let dest_ty = self.body().local_decls[dest].ty;
                self.set_local(
                    dest,
                    VmValue::new(len, dest_ty),
                );
            }
            CallEffect::ReturnNonZeroIff { arg } => {
                if let Some(a) = args.get(*arg) {
                    let dest_ty = self.body().local_decls[dest].ty;
                    let zero = Int::from_u64(self.z3_ctx, 0);
                    let term = self.fresh_int(&format!("ret_nz_iff_{}", dest.as_usize()));
                    // `result == 0` iff `arg == 0`, i.e. non-zero is preserved
                    // exactly (bit-preserving ops map 0 -> 0, non-zero -> non-zero).
                    self.constraints.assertions
                        .push(term._eq(&zero)._eq(&a.z3_term._eq(&zero)));
                    self.set_local(
                        dest,
                        VmValue::new(term, dest_ty),
                    );
                }
            }
            CallEffect::ReturnOptionSomeNonZero => {
                // `Some` payload is unconditionally non-zero (e.g.
                // `checked_next_power_of_two`).
                let zero = Int::from_u64(self.z3_ctx, 0);
                let term = self.fresh_int(&format!("ret_opt_nz_{}", dest.as_usize()));
                self.constraints.assertions.push(term._eq(&zero).not());
                let payload_ty = args
                    .first()
                    .map(|a| a.ty)
                    .unwrap_or(self.body().local_decls[dest].ty);
                self.set_field_value(
                    dest,
                    vec![0],
                    VmValue::new(term, payload_ty),
                );
            }
            CallEffect::CopyMemory { source_arg, destination_arg, count_arg } => {
                if let (Some(source), Some(target), Some(count)) = (
                    args.get(*source_arg),
                    args.get(*destination_arg),
                    args.get(*count_arg),
                ) {
                    let concrete_count = count.z3_term.simplify().as_u64();
                    if concrete_count == Some(0) {
                        return;
                    }
                    let pointee_ty = match target.ty.kind() {
                        TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) => *inner,
                        _ => return,
                    };
                    let local_target = self.find_local_by_address(&target.z3_term)
                        .is_some_and(|local| self.body().local_decls[local].ty == pointee_ty);
                    let object_target = target.provenance.as_ref().is_some_and(|prov| {
                        let alloc = self.alloc(prov.alloc_id);
                        matches!(&alloc.kind, AllocKind::Object)
                            && alloc.element_ty.as_ty() == Some(pointee_ty)
                            && prov.offset.simplify().as_u64() == Some(0)
                    });
                    if !local_target && !object_target {
                        return;
                    }
                    let source_value = self.find_local_by_address(&source.z3_term)
                        .and_then(|local| self.local_value(local).cloned())
                        .or_else(|| source.provenance.as_ref()
                            .and_then(|prov| self.load_value(prov.alloc_id, pointee_ty, &[]).cloned()));
                    let copied = if concrete_count == Some(1) {
                        source_value.unwrap_or_else(|| VmValue::new(self.fresh_int("copy_value"), pointee_ty))
                    } else {
                        VmValue::new(self.fresh_int("copy_value"), pointee_ty)
                    };
                    if let Some(prov) = &target.provenance {
                        let content = self.content_mut(prov.alloc_id);
                        content.values.clear();
                        content.byte_array = None;
                        content.byte_written.clear();
                        content.facts.cstr_trusted = false;
                        content.facts.utf8_trusted = false;
                    }
                    self.write_through_pointer(target, Vec::new(), copied);
                }
            }
            CallEffect::WriteMemory { pointer_arg } => {
                if let Some(arg_val) = args.get(*pointer_arg)
                    && let Some(prov) = &arg_val.provenance {
                        // Writing a non-`u8` value through a byte buffer reinterprets
                        // it (e.g. `*mut FreeBlock` cast from a `Vec<u8>` buffer):
                        // update the allocation's element type so a later `Typed`
                        // invariant matches the written type.
                        if let rustc_middle::ty::TyKind::RawPtr(inner, _)
                        | rustc_middle::ty::TyKind::Ref(_, inner, _) = arg_val.ty.kind()
                        {
                            let cur = self.alloc(prov.alloc_id).element_ty.as_ty();
                            let is_u8 = |t: rustc_middle::ty::Ty<'_>| {
                                matches!(
                                    t.kind(),
                                    rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::U8)
                                )
                            };
                            if let Some(c) = cur
                                && is_u8(c) && !is_u8(*inner) {
                                    self.alloc_mut(prov.alloc_id).element_ty = ElementTy::Typed(*inner);
                                }
                        }
                        // For locally-created Vec-like types: create a heap data
                        // allocation on first mutation. (Param Vecs already have
                        // an external allocation set by init_parameters.)
                        let is_vec = api_classify::is_vec_push_or_reserve(callee);
                        let is_external = self.alloc(prov.alloc_id).is_external();
                        if is_vec && !is_external {
                            let elem_ty = match arg_val.ty.kind() {
                                TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) => {
                                    crate::verify::call_summary::effects::vec_elem_ty(*inner)
                                }
                                _ => crate::verify::call_summary::effects::vec_elem_ty(arg_val.ty),
                            };
                            let heap_align = elem_ty
                                .map(|ty| self.align_sym(ty))
                                .unwrap_or_else(|| Int::from_u64(self.z3_ctx, 1));
                            if let Some(old_data) =
                                self.container_data_alloc(prov.alloc_id, arg_val.ty)
                            {
                                // Subsequent mutation: invalidate old heap data.
                                self.alloc_mut(old_data).facts.dead = true;
                            }
                            let max_size = Int::from_u64(self.z3_ctx, i64::MAX as u64);
                            let (data_alloc, data_base) =
                                self.allocate_external(max_size, heap_align, elem_ty);
                            let container_ty = match arg_val.ty.kind() {
                                TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) => *inner,
                                _ => arg_val.ty,
                            };
                            self.set_container_data_field(
                                prov.alloc_id,
                                arg_val.ty,
                                data_alloc,
                                data_base,
                                elem_ty.unwrap_or(container_ty),
                            );
                        }
                        // When offset is concrete, only mark the bytes actually
                        // written. For symbolic offsets, mark entire allocation.
                        let off_u64 = prov
                            .offset
                            .as_u64()
                            .or_else(|| prov.offset.simplify().as_u64());
                        if let Some(off) = off_u64 {
                            if off == 0 {
                                self.content_mut(prov.alloc_id).facts.initialized = true;
                            }
                            let elem_size = match arg_val.ty.kind() {
                                rustc_middle::ty::TyKind::Ref(_, inner, _) => {
                                    self.size_of_ty(*inner) as usize
                                }
                                _ => 0,
                            };
                            let write_size = if elem_size > 0 {
                                elem_size
                            } else {
                                self.allocation_size(prov.alloc_id).as_u64().unwrap_or(0) as usize
                            };
                            let end = (off as usize + write_size).min(4096);
                            for byte_off in (off as usize)..end {
                                self.mark_byte_init(prov.alloc_id, byte_off);
                            }
                        } else {
                            // Symbolic write offset: the exact written element
                            // can't be tracked per-byte. For concrete allocation
                            // sizes, mark every byte (as before). For unknown /
                            // zero sizes — generic element types such as
                            // `MaybeUninit<T>` inside `[MaybeUninit<T>; N]` —
                            // mark the whole allocation initialized so a later
                            // `assume_init_read`/`assume_init_drop` can discharge
                            // `Init` on those (fully initialized) elements.
                            let size_val = self.allocation_size(prov.alloc_id).as_u64();
                            match size_val {
                                Some(sz) if sz > 0 => {
                                    for off in 0..(sz as usize).min(1024) {
                                        self.mark_byte_init(prov.alloc_id, off);
                                    }
                                }
                                _ => {
                                    self.content_mut(prov.alloc_id).facts.initialized = true;
                                }
                            }
                        }
                    }
            }
            CallEffect::ReturnFreshAllocation {
                pointer_arg,
                size_arg,
                elem_size,
            } => {
                if let (Some(ptr_val), Some(size_val)) =
                    (args.get(*pointer_arg), args.get(*size_arg))
                {
                    let dest_ty = self.body().local_decls[dest].ty;
                    let elem_ty = crate::verify::call_summary::effects::from_raw_parts_elem_ty(
                        self.tcx,
                        self.current_frame.current_def_id,
                        Some(dest),
                    );
                    // A generic element type uses the shared symbolic `sizeof_T`
                    // so the fresh allocation's size stays consistent with ptr
                    // strides and `InBound` cancels the factor.
                    let elem_sz_term = if *elem_size == 0 {
                        self.size_sym(elem_ty.unwrap_or(dest_ty))
                    } else {
                        Int::from_u64(self.z3_ctx, *elem_size)
                    };
                    let heap_align = elem_ty
                        .map(|ty| self.align_sym(ty))
                        .unwrap_or_else(|| Int::from_u64(self.z3_ctx, 1));
                    let (alloc_id, base) = self.allocate_slice(
                        size_val.z3_term.clone(),
                        elem_sz_term.clone(),
                        heap_align,
                        elem_ty,
                    );
                    let prov = Provenance {
                        alloc_id,
                        offset: Int::from_u64(self.z3_ctx, 0),
                        offset_kind: None,
                    };
                    // Propagate init status and byte-level tracking from the source pointer.
                    if let Some(ref source_prov) = ptr_val.provenance {
                        if !self.alloc(source_prov.alloc_id).facts.dead {
                            self.content_mut(alloc_id).facts.initialized = true;
                            self.alloc_mut(alloc_id).parent = Some(source_prov.alloc_id);
                        }
                        // Copy byte-level tracking (value, init, NUL knowledge),
                        // shifting by the source pointer's byte offset so a
                        // non-zero-offset sub-slice (`from_raw_parts(ptr.add(k),
                        // n)`) inherits the right per-byte state.
                        let src_offset = source_prov
                            .offset
                            .simplify()
                            .as_u64()
                            .map(|v| v as usize)
                            .unwrap_or(0);
                        self.copy_byte_tracking(source_prov.alloc_id, src_offset, alloc_id);
                    }
                    let result_align_n = ptr_val.facts.align_n.clone().or_else(|| {
                        ptr_val
                            .provenance
                            .as_ref()
                            .map(|p| self.alloc(p.alloc_id).align.clone())
                    });
                    let vec_base = base.clone();
                    let vec_prov = prov.clone();
                    let vec_len = size_val.z3_term.clone();
                    self.set_local(
                        dest,
                        VmValue {
                            z3_term: base,
                            ty: dest_ty,
                            provenance: Some(prov),
                            facts: ValueFacts {
                                non_null: true,
                                init: true,
                                in_bounds: true,
                                align_n: result_align_n.clone(),
                            },
                            source: ValueSource::None,
                        },
                    );
                    // Materialize `{ptr, cap, len}` fields for a Vec destination
                    // (`from_raw_parts` sets cap == len).
                    if let rustc_middle::ty::TyKind::Adt(adt_def, _) = dest_ty.kind()
                        && api_classify::is_std_vec(adt_def.did()) {
                            let ptr_field = VmValue {
                                z3_term: vec_base,
                                ty: ptr_val.ty,
                                provenance: Some(vec_prov),
                                facts: ValueFacts {
                                    non_null: true,
                                    init: true,
                                    in_bounds: true,
                                    align_n: result_align_n,
                                },
                                source: ValueSource::None,
                            };
                            self.materialize_vec_fields(dest, ptr_field, vec_len.clone(), vec_len);
                        }
                }
            }
            CallEffect::ReturnBoxAllocation => {
                let dest_ty = self.body().local_decls[dest].ty;
                // `pointee_ty` doesn't unwrap `Box`; extract its `T` from the
                // first generic argument so the heap allocation is sized to the
                // pointee and (below) the inner `Unique<T>.pointer` field can be
                // exposed.
                let pointee = mir_utils::pointee_ty(dest_ty).or_else(|| {
                    if let rustc_middle::ty::TyKind::Adt(adt, substs) = dest_ty.kind() {
                        if api_classify::is_std_box(adt.did()) {
                            substs.first().and_then(|s| s.as_type())
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                });
                let size = pointee
                    .map(|ty| self.size_sym(ty))
                    .unwrap_or_else(|| Int::from_u64(self.z3_ctx, 1));
                let align = pointee
                    .map(|ty| self.align_sym(ty))
                    .unwrap_or_else(|| Int::from_u64(self.z3_ctx, 1));
                let (alloc_id, base) = self.allocate(size, align, pointee);
                self.content_mut(alloc_id).facts.initialized = true;
                let align_n = pointee.map(|ty| self.align_sym(ty));
                let heap_prov = Provenance {
                    alloc_id,
                    offset: Int::from_u64(self.z3_ctx, 0),
                    offset_kind: None,
                };
                // Expose `Box`'s inner `Unique<T>.pointer` (`NonNull<T>` at path
                // `[0, 0]`) so inlined `Box::as_ptr`/`as_mut_ptr` bodies — which
                // read `(_1.0).0` and cast it to `*const`/`*mut T` — inherit the
                // heap pointer's provenance (rustc 1.95 lowers `&raw **b` to
                // exactly this field read + transmute).  Record it both on the
                // local's stack slot (`set_field_value`, for direct `_1.0.0`
                // reads) and on the heap allocation (`MemoryContent::values`, for
                // `(*&box).0.0` deref-reads through a reborrow).
                let nn_field = VmValue {
                    z3_term: base.clone(),
                    ty: dest_ty,
                    provenance: Some(heap_prov.clone()),
                    facts: ValueFacts {
                        non_null: true,
                        init: true,
                        ..Default::default()
                    },
                    source: ValueSource::None,
                };
                let nn_path = self
                    .container_ptr_field(dest_ty)
                    .expect("Box has no owning pointer field");
                self.set_field_value(dest, nn_path.clone(), nn_field.clone());
                self.units[alloc_id.0]
                    .content
                    .values
                    .insert((dest_ty, nn_path), nn_field);
                self.set_local(
                    dest,
                    VmValue {
                        z3_term: base.clone(),
                        ty: dest_ty,
                        provenance: Some(Provenance {
                            alloc_id,
                            offset: Int::from_u64(self.z3_ctx, 0),
                            offset_kind: None,
                        }),
                        facts: ValueFacts {
                            non_null: true,
                            init: true,
                            in_bounds: true,
                            align_n,
                        },
                        source: ValueSource::None,
                    },
                );
            }
            CallEffect::ReturnExchangeMalloc { size_arg } => {
                if let Some(size_val) = args.get(*size_arg) {
                    let dest_ty = self.body().local_decls[dest].ty;
                    let u8_ty = self.tcx.types.u8;
                    let (alloc_id, base) = self.allocate_external(
                        size_val.z3_term.clone(),
                        Int::from_u64(self.z3_ctx, 1),
                        Some(u8_ty),
                    );
                    self.alloc_mut(alloc_id).set_slice_len(size_val.z3_term.clone());
                    self.content_mut(alloc_id).facts.initialized = true;
                    self.set_local(
                        dest,
                        VmValue {
                            z3_term: base,
                            ty: dest_ty,
                            provenance: Some(Provenance {
                                alloc_id,
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
                        },
                    );
                }
            }
            CallEffect::ReturnNewAllocation {
                size_arg,
                elem_size,
            } => {
                if let Some(size_val) = args.get(*size_arg) {
                    let dest_ty = self.body().local_decls[dest].ty;
                    let elem_ty = crate::verify::call_summary::effects::vec_elem_ty(dest_ty);
                    // A generic element type (`elem_size == 0`) uses the shared
                    // symbolic `sizeof_T` so the allocation size stays consistent
                    // with pointer strides (mirrors `ReturnFreshAllocation`).
                    let elem_sz = if *elem_size == 0 {
                        self.size_sym(elem_ty.unwrap_or(dest_ty))
                    } else {
                        Int::from_u64(self.z3_ctx, *elem_size)
                    };
                    let total = Int::mul(self.z3_ctx, &[&size_val.z3_term, &elem_sz]);
                    let heap_align = elem_ty
                        .map(|ty| self.align_sym(ty))
                        .unwrap_or_else(|| Int::from_u64(self.z3_ctx, 1));
                    let (alloc_id, base) = self.allocate_external(total, heap_align, elem_ty);
                    self.alloc_mut(alloc_id).set_slice_len(size_val.z3_term.clone());
                    let dest_alloc_id = self.current_frame.local_alloc.get(&dest).copied();
                    self.content_mut(alloc_id).facts.initialized = true;
                    let vec_base = base.clone();
                    let vec_len = size_val.z3_term.clone();
                    self.set_local(
                        dest,
                        VmValue {
                            z3_term: base,
                            ty: dest_ty,
                            provenance: dest_alloc_id.map(|stack_id| Provenance {
                                alloc_id: stack_id,
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
                        },
                    );
                    // `Vec::from_elem`/`from_elem`-style constructors set
                    // len == cap == count.
                    if let rustc_middle::ty::TyKind::Adt(adt_def, _) = dest_ty.kind()
                        && api_classify::is_std_vec(adt_def.did()) {
                            let ptr_field = VmValue {
                                z3_term: vec_base,
                                ty: elem_ty.unwrap_or(dest_ty),
                                provenance: Some(Provenance {
                                    alloc_id,
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
                            self.materialize_vec_fields(dest, ptr_field, vec_len.clone(), vec_len);
                        }
                }
            }
            CallEffect::ReturnNewAllocationFromCap { cap_arg, elem_size } => {
                if let Some(cap_val) = args.get(*cap_arg) {
                    let dest_ty = self.body().local_decls[dest].ty;
                    let elem_ty = crate::verify::call_summary::effects::vec_elem_ty(dest_ty);
                    // A generic element type (`elem_size == 0`) uses the shared
                    // symbolic `sizeof_T` so the allocation size stays consistent
                    // with pointer strides (mirrors `ReturnFreshAllocation`).
                    let elem_sz = if *elem_size == 0 {
                        self.size_sym(elem_ty.unwrap_or(dest_ty))
                    } else {
                        Int::from_u64(self.z3_ctx, *elem_size)
                    };
                    let total = Int::mul(self.z3_ctx, &[&cap_val.z3_term, &elem_sz]);
                    let heap_align = elem_ty
                        .map(|ty| self.align_sym(ty))
                        .unwrap_or_else(|| Int::from_u64(self.z3_ctx, 1));
                    let (alloc_id, base) = self.allocate_external(total, heap_align, elem_ty);
                    let dest_alloc_id = self.current_frame.local_alloc.get(&dest).copied();
                    self.content_mut(alloc_id).facts.initialized = true;
                    let vec_base = base.clone();
                    let vec_cap = cap_val.z3_term.clone();
                    self.set_local(
                        dest,
                        VmValue {
                            z3_term: base,
                            ty: dest_ty,
                            provenance: dest_alloc_id.map(|stack_id| Provenance {
                                alloc_id: stack_id,
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
                        },
                    );
                    // `Vec::with_capacity(n)`: len == 0, cap == n.
                    if let rustc_middle::ty::TyKind::Adt(adt_def, _) = dest_ty.kind()
                        && api_classify::is_std_vec(adt_def.did()) {
                            let ptr_field = VmValue {
                                z3_term: vec_base,
                                ty: elem_ty.unwrap_or(dest_ty),
                                provenance: Some(Provenance {
                                    alloc_id,
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
                            let zero = Int::from_u64(self.z3_ctx, 0);
                            self.materialize_vec_fields(dest, ptr_field, vec_cap, zero);
                        }
                }
            }
            CallEffect::ReturnNewAllocationFromBox => {
                // Box→Vec conversion (into_vec, box_assume_init_into_vec_unsafe)
                // and `slice::to_vec` (a fresh copy of a slice).
                self.ensure_local_allocation(dest);
                let dest_ty = self.body().local_decls[dest].ty;
                let elem_ty = crate::verify::call_summary::effects::vec_elem_ty(dest_ty);
                let heap_align = elem_ty
                    .map(|ty| self.align_sym(ty))
                    .unwrap_or_else(|| Int::from_u64(self.z3_ctx, 1));
                // Use the receiver's slice length as the allocation size when
                // known (`to_vec`/`into_vec`), else a symbolic upper bound.
                let known_len = args
                    .first()
                    .and_then(|v| v.provenance.as_ref())
                    .and_then(|p| {
                        let alloc = self.alloc(p.alloc_id);
                        if let Some(slice_len) = alloc.slice_len().cloned() {
                            return Some(slice_len);
                        }
                        // A boxed array (`box [T; N]`) has a concrete size but no
                        // slice length; its element count is `size / elem_size`.
                        let elem_size = elem_ty.map(|t| self.size_of_ty(t)).unwrap_or(1);
                        let n = alloc.size.as_u64()?;
                        Some(Int::from_u64(self.z3_ctx, n.checked_div(elem_size)?))
                    });
                let size = known_len
                    .clone()
                    .unwrap_or_else(|| Int::from_u64(self.z3_ctx, i64::MAX as u64));
                let (alloc_id, base) = self.allocate_external(size, heap_align, elem_ty);
                // Copy the boxed slice's tracked byte values into the fresh Vec
                // buffer so byte-level checkers (`ValidCStr`/`ValidString`) can
                // reason over the copied contents.
                if let Some(box_alloc) = args.first().and_then(|v| v.provenance_alloc_id()) {
                    self.copy_byte_tracking(box_alloc, 0, alloc_id);
                }
                let dest_alloc_id = self.current_frame.local_alloc.get(&dest).copied();
                self.content_mut(alloc_id).facts.initialized = true;
                let vec_base = base.clone();
                self.set_local(
                    dest,
                    VmValue {
                        z3_term: base,
                        ty: dest_ty,
                        provenance: dest_alloc_id.map(|stack_id| Provenance {
                            alloc_id: stack_id,
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
                    },
                );
                // `into_vec` / `box_assume_init_into_vec_unsafe`: the Vec's
                // length equals the source boxed slice's length (symbolic);
                // cap == len (no spare capacity).
                if let rustc_middle::ty::TyKind::Adt(adt_def, _) = dest_ty.kind()
                    && api_classify::is_std_vec(adt_def.did()) {
                        let ptr_field = VmValue {
                            z3_term: vec_base,
                            ty: elem_ty.unwrap_or(dest_ty),
                            provenance: Some(Provenance {
                                alloc_id,
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
                        let len_term = known_len
                            .clone()
                            .unwrap_or_else(|| self.fresh_int(&format!("vec_len_{}", dest.as_usize())));
                        self.materialize_vec_fields(dest, ptr_field, len_term.clone(), len_term);
                    }
            }
            CallEffect::ReturnBoxFromVec { arg } => {
                if let Some(vec_val) = args.get(*arg)
                    && let Some(ref prov) = vec_val.provenance
                        && let Some(heap_alloc_id) =
                            self.container_data_alloc(prov.alloc_id, vec_val.ty)
                        {
                            let heap_base = self.allocation_base(heap_alloc_id).clone();
                            let dest_ty = self.body().local_decls[dest].ty;
                            self.set_local(
                                dest,
                                VmValue {
                                    z3_term: heap_base,
                                    ty: dest_ty,
                                    provenance: Some(Provenance {
                                        alloc_id: heap_alloc_id,
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
                                },
                            );
                        }
            }
            CallEffect::OwnsInitMemory { arg } => {
                if let Some(arg_val) = args.get(*arg) {
                    if let Some(prov) = &arg_val.provenance {
                        self.content_mut(prov.alloc_id).facts.initialized = true;
                    }
                    let mut val = arg_val.clone();
                    val.ty = self.body().local_decls[dest].ty;
                    val.facts.init = true;
                    val.facts.non_null = true;
                    // `Box::from_raw`/`from_raw_in` reconstruct a Box whose
                    // `Unique<T>.pointer` (`NonNull<T>` at path `[0, 0]`) must
                    // carry the same provenance: rustc 1.95 lowers `Box::as_ptr`
                    // (`&raw **b`) to a `(_1.0).0` field read + transmute, so
                    // without this the re-derived pointer loses provenance.
                    if let rustc_middle::ty::TyKind::Adt(adt, _) = val.ty.kind()
                        && api_classify::is_std_box(adt.did()) {
                            let nn_path = self
                                .container_ptr_field(val.ty)
                                .expect("Box has no owning pointer field");
                            self.set_field_value(dest, nn_path.clone(), val.clone());
                            if let Some(prov) = &val.provenance {
                                self.units[prov.alloc_id.0]
                                    .content
                                    .values
                                    .insert((val.ty, nn_path), val.clone());
                            }
                        }
                    self.set_local(dest, val);
                }
            }
            CallEffect::DropMemory { pointer_arg } => {
                // `ManuallyDrop::drop(slot)` / `drop_in_place(x)` frees the heap
                // allocation behind the argument. A reference/raw-pointer
                // argument carries the *stack* provenance of the referent
                // (penetrate to its heap field); a value argument (`Box`/`Vec`)
                // carries the heap provenance directly. Mark the allocation
                // dead; a second drop of an already-dead allocation is detected
                // downstream via `dead` alone.
                if let Some(arg_val) = args.get(*pointer_arg) {
                    let alloc_id = if matches!(
                        arg_val.ty.kind(),
                        rustc_middle::ty::TyKind::Ref(..)
                            | rustc_middle::ty::TyKind::RawPtr(..)
                    ) {
                        self.find_local_by_address(&arg_val.z3_term)
                            .and_then(|r| self.owner_ptr_field(r))
                            .and_then(|v| v.provenance_alloc_id())
                    } else {
                        arg_val.provenance_alloc_id()
                    };
                    if let Some(alloc_id) = alloc_id {
                        self.alloc_mut(alloc_id).facts.dead = true;
                    }
                }
            }
            CallEffect::ReturnPowerOfTwo => {
                // `Layout::align()` returns the layout's alignment, which is a
                // non-zero power of two. `Layout::align` inlines to
                // `self.align.as_usize()`, whose transmute-based body drops the
                // `NonZero` provenance; re-establish the non-zero fact (and the
                // power-of-two fact) with a fresh symbol so downstream
                // `from_size_align_unchecked` can discharge `align != 0` (its
                // `(align & (align - 1)) == 0` check is otherwise vacuously
                // proved, since contract-level `BitAnd` is unsupported).
                let dest_ty = self.body().local_decls[dest].ty;
                let term = self.fresh_int(&format!("layout_align_{}", dest.as_usize()));
                let zero = Int::from_u64(self.z3_ctx, 0);
                self.constraints.assertions.push(term.gt(&zero));
                self.set_local(
                    dest,
                    VmValue::new(term, dest_ty),
                );
            }
            CallEffect::ReturnSliceRangeIndex => {
                if args.len() < 2 {
                    return;
                }
                let dest_ty = self.body().local_decls[dest].ty;
                let is_slice = matches!(dest_ty.kind(), TyKind::Ref(_, inner, _)
                    if matches!(inner.kind(), TyKind::Slice(_)));
                let range_kind = args.get(1).and_then(|v| match v.ty.kind() {
                    TyKind::Adt(adt_def, _) => Some(mir_utils::range_kind(
                        self.tcx,
                        adt_def.did(),
                    )),
                    _ => None,
                });
                if !is_slice && range_kind.is_none() {
                    return;
                }
                let Some(prov) = args[0].provenance.clone() else {
                    return;
                };
                let array_term = args[0].z3_term.clone();
                let (elem_ty, elem_size) = match args[0].ty.kind() {
                    TyKind::Ref(_, inner, _) => match inner.kind() {
                        TyKind::Array(e, _) | TyKind::Slice(e) => (*e, self.size_of_ty(*e).max(1)),
                        _ => (args[0].ty, 1),
                    },
                    _ => (args[0].ty, 1),
                };
                let elem_align = self.align_sym(elem_ty);
                let range_local = caller_arg_locals.get(1).copied().flatten();
                let range_field = |idx: usize| -> Option<Int<'z3>> {
                    range_local.and_then(|l| self.field_value(l, &[idx]).map(|v| v.z3_term.clone()))
                };
                let zero = Int::from_u64(self.z3_ctx, 0);
                let one = Int::from_u64(self.z3_ctx, 1);
                let total_len = self
                    .alloc(prov.alloc_id)
                    .size
                    .clone()
                    .div(&Int::from_u64(self.z3_ctx, elem_size));
                let (start, len) = match range_kind {
                    Some(mir_utils::RangeKind::RangeTo) => (
                        zero.clone(),
                        range_field(0).unwrap_or_else(|| total_len.clone()),
                    ),
                    Some(mir_utils::RangeKind::RangeFrom) => {
                        let s = range_field(0).unwrap_or_else(|| zero.clone());
                        (s.clone(), Int::sub(self.z3_ctx, &[&total_len, &s]))
                    }
                    Some(mir_utils::RangeKind::Range) => {
                        let s = range_field(0).unwrap_or_else(|| zero.clone());
                        let e = range_field(1).unwrap_or_else(|| total_len.clone());
                        (s.clone(), Int::sub(self.z3_ctx, &[&e, &s]))
                    }
                    Some(mir_utils::RangeKind::RangeInclusive) => {
                        let s = range_field(0).unwrap_or_else(|| zero.clone());
                        let e = range_field(1).unwrap_or_else(|| total_len.clone());
                        let l = Int::sub(self.z3_ctx, &[&e, &s]);
                        (s.clone(), Int::add(self.z3_ctx, &[&l, &one]))
                    }
                    _ => (zero.clone(), total_len.clone()),
                };
                let elem_size_term = Int::from_u64(self.z3_ctx, elem_size);
                let start_bytes = if elem_size == 1 {
                    start.clone()
                } else {
                    Int::mul(self.z3_ctx, &[&start, &elem_size_term])
                };
                let size_bytes = if elem_size == 1 {
                    len.clone()
                } else {
                    Int::mul(self.z3_ctx, &[&len, &elem_size_term])
                };
                let dest_term = Int::add(self.z3_ctx, &[&array_term, &start_bytes]);
                let (alloc_id, _) = self.allocate(size_bytes, elem_align, Some(elem_ty));
                self.alloc_mut(alloc_id).parent = Some(prov.alloc_id);
                self.set_local(
                    dest,
                    VmValue {
                        z3_term: dest_term,
                        ty: dest_ty,
                        provenance: Some(Provenance {
                            alloc_id,
                            offset: Int::from_u64(self.z3_ctx, 0),
                            offset_kind: None,
                        }),
                        facts: ValueFacts {
                            non_null: true,
                            init: true,
                            in_bounds: true,
                            ..Default::default()
                        },
                        source: ValueSource::None,
                    },
                );
            }
            CallEffect::ReturnIterLen { is_len } => {
                if args.is_empty() {
                    return;
                }
                let Some(local) = caller_arg_locals.first().copied().flatten() else {
                    return;
                };
                let Some((ptr, end)) = self.iter_ptr_end(local) else {
                    return;
                };
                let dest_ty = self.body().local_decls[dest].ty;
                if *is_len {
                    let len = self
                        .iter_len_from_ptrs(&ptr, &end)
                        .expect("iter_ptr_end guarantees same-alloc provenance");
                    self.set_local(dest, VmValue::new(len, dest_ty));
                } else {
                    // is_empty(): ptr == end_or_len  (non-ZST branch)
                    let pp = ptr.provenance.as_ref().unwrap();
                    let ep = end.provenance.as_ref().unwrap();
                    let eq = pp.offset._eq(&ep.offset);
                    let zero = Int::from_u64(self.z3_ctx, 0);
                    let one = Int::from_u64(self.z3_ctx, 1);
                    let val = VmValue {
                        z3_term: eq.ite(&one, &zero),
                        ty: dest_ty,
                        provenance: None,
                        facts: ValueFacts::default(),
                        source: ValueSource::None,
                    };
                    self.set_local(dest, val);
                }
            }
            CallEffect::ReturnNonNullNew => {
                let Some(ptr) = args.first() else {
                    return;
                };
                let dest_ty = self.body().local_decls[dest].ty;
                let definitely_non_null = ptr.facts.non_null
                    || ptr.facts.in_bounds
                    || ptr
                        .provenance
                        .as_ref()
                        .is_some_and(|p| !self.alloc(p.alloc_id).is_external());
                if definitely_non_null {
                    // Some(NonNull(ptr)): the Option data payload is the non-null pointer.
                    let mut val = ptr.clone();
                    val.ty = dest_ty;
                    val.facts.non_null = true;
                    let zero = Int::from_u64(self.z3_ctx, 0);
                    self.constraints.assertions.push(ptr.z3_term._eq(&zero).not());
                    self.set_local(dest, val);
                } else {
                    // ptr may be null, so the Option may be None — keep it symbolic.
                    let term = self.fresh_int(&format!("nn_new_{}", dest.as_usize()));
                    self.set_local(dest, VmValue::new(term, dest_ty));
                }
            }
            CallEffect::ReturnIterNext => {
                if args.is_empty() {
                    return;
                }
                let self_val = &args[0];
                let Some(local) = self.find_iter_self_local(self_val) else {
                    return;
                };
                let Some(iter_prov) = self_val.provenance.as_ref() else {
                    return;
                };
                let iter_key = (iter_prov.alloc_id, iter_prov.offset.simplify());
                let Some((ptr, end)) = self.iter_ptr_end(local) else {
                    return;
                };
                let pp = ptr.provenance.as_ref().unwrap();
                let ep = end.provenance.as_ref().unwrap();
                let buffer = ep.alloc_id;
                let ep_elem = match &ep.offset_kind {
                    Some(OffsetKind::Element(e)) => Some(e.clone()),
                    _ => None,
                };
                let dest_ty = self.body().local_decls[dest].ty;
                // Compute is_empty from fields/tracked offset (same as is_empty()).
                let sz = self.iter_elem_size(&ptr);
                let ep_offset = ep.offset.clone();
                let remaining = self
                    .iter_remaining_len_from_ptrs(&ptr, &end, Some(&iter_key))
                    .expect("iter_ptr_end guarantees same-alloc provenance");
                let is_empty = remaining._eq(&Int::from_u64(self.z3_ctx, 0));
                // The returned element is the *current* position: the tracked element
                // index (iter_ptr_offset) scaled by the element stride, or the base
                // ptr offset on the first call.
                let zero = Int::from_u64(self.z3_ctx, 0);
                let cur_off = match self.constraints.term_caches.iter_ptr_offset.get(&iter_key) {
                    Some((_, prev, _)) => Int::mul(self.z3_ctx, &[prev, &sz]),
                    None => pp.offset.clone(),
                };
                let old_ptr_val = VmValue {
                    z3_term: Int::add(self.z3_ctx, &[self.allocation_base(pp.alloc_id), &cur_off]),
                    ty: ptr.ty,
                    provenance: Some(Provenance {
                        alloc_id: pp.alloc_id,
                        offset: cur_off.clone(),
                        offset_kind: None,
                    }),
                    facts: ValueFacts {
                        non_null: true,
                        init: true,
                        ..Default::default()
                    },
                    source: ValueSource::None,
                };
                // Advance ptr when not empty
                let one_term = Int::from_u64(self.z3_ctx, 1);
                let (old_offset, base_len_elem) =
                    match self.constraints.term_caches.iter_ptr_offset.get(&iter_key) {
                        Some((_, prev, base)) => (prev.clone(), base.clone()),
                        None => (pp.offset.div(&sz), ep_elem),
                    };
                let new_offset = Int::add(self.z3_ctx, &[&old_offset, &one_term]);
                // Push: base_len >= tracked_offset
                let base_len = base_len_elem.clone().unwrap_or_else(|| ep_offset.div(&sz));
                self.constraints.assertions.push(Bool::or(
                    self.z3_ctx,
                    &[&is_empty, &new_offset.le(&base_len)],
                ));
                self.constraints
                    .term_caches
                    .iter_ptr_offset
                    .insert(iter_key, (buffer, is_empty.ite(&old_offset, &new_offset), base_len_elem));
                // Return None or old ptr
                let result_val = VmValue {
                    z3_term: is_empty.ite(&zero, &old_ptr_val.z3_term),
                    ty: dest_ty,
                    provenance: None,
                    facts: ValueFacts::default(),
                    // Tie the Option's discriminant to the emptiness condition so
                    // `switchInt(discriminant(_n))` only takes the `Some` branch when
                    // the iterator was non-empty (and the `None` branch when empty).
                    source: ValueSource::Discriminant(is_empty.ite(&zero, &one_term)),
                };
                self.set_local(dest, result_val);
                self.set_field_value(dest, vec![0], old_ptr_val);
                let next_off = is_empty.ite(
                    &cur_off,
                    &Int::add(self.z3_ctx, &[&cur_off, &sz]),
                );
                let mut next_ptr = ptr.clone();
                next_ptr.z3_term = Int::add(
                    self.z3_ctx,
                    &[self.allocation_base(pp.alloc_id), &next_off],
                );
                next_ptr.provenance = Some(Provenance {
                    alloc_id: pp.alloc_id,
                    offset: next_off,
                    offset_kind: Some(OffsetKind::Element(is_empty.ite(&old_offset, &new_offset))),
                });
                let ptr_path = if self
                    .field_value(local, &[0])
                    .is_some_and(|field| field.z3_term == ptr.z3_term)
                {
                    vec![0]
                } else {
                    vec![0, 0]
                };
                self.set_field_value(local, ptr_path, next_ptr);
            }
            CallEffect::ReturnRangeNext => {
                if args.is_empty() {
                    return;
                }
                let self_val = &args[0];
                // `self` is `&mut Range<A>` / `&mut RangeInclusive<A>`.
                let TyKind::Ref(_, pointee, _) = self_val.ty.kind() else {
                    return;
                };
                let TyKind::Adt(adt_def, _) = pointee.kind() else {
                    return;
                };
                let Some(alloc_id) = self_val.provenance_alloc_id() else {
                    return;
                };
                // The aggregate's fields are stored under the *monomorphized* view type
                // (e.g. `Range<usize>`), not the generic `Range<A>` carried by `self`.
                let range_view_ty = self.units[alloc_id.0]
                    .content
                    .values
                    .keys()
                    .map(|(t, _)| *t)
                    .find(|t| matches!(t.kind(), TyKind::Adt(adt, _) if adt.did() == adt_def.did()));
                let Some(range_view_ty) = range_view_ty else {
                    return;
                };
                let Some(start) = self.load_value(alloc_id, range_view_ty, &[0]).cloned() else {
                    return;
                };
                let Some(end) = self.load_value(alloc_id, range_view_ty, &[1]).cloned() else {
                    return;
                };
                let dest_ty = self.body().local_decls[dest].ty;
                let zero = Int::from_u64(self.z3_ctx, 0);
                let one = Int::from_u64(self.z3_ctx, 1);
                let start_term = start.z3_term.clone();
                let end_term = end.z3_term.clone();
                // `None` when `start >= end`; the `Some` path therefore has `start < end`.
                let is_empty = start_term.ge(&end_term);
                let result_val = VmValue {
                    z3_term: is_empty.ite(&zero, &start_term),
                    ty: dest_ty,
                    provenance: None,
                    facts: ValueFacts::default(),
                    source: ValueSource::Discriminant(is_empty.ite(&zero, &one)),
                };
                self.set_local(dest, result_val);
                self.set_field_value(dest, vec![0], start.clone());
                let mut advanced = start;
                let next = Int::add(self.z3_ctx, &[&start_term, &one]);
                advanced.z3_term = is_empty.ite(&start_term, &next);
                self.store_value(alloc_id, range_view_ty, vec![0], advanced);
            }
        }
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
    fn iter_remaining_len_from_ptrs(
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
    fn find_iter_self_local(&self, arg_val: &VmValue<'z3, 'tcx>) -> Option<Local> {
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
    fn apply_range_effect(
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
