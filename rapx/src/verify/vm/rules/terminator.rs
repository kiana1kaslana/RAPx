//! Transfer functions for MIR terminators.

use rustc_middle::mir::{BasicBlock, Operand, Place, SwitchTargets};
use z3::ast::{Ast, Int};

use super::super::state::VmState;
use crate::compat::Spanned;

pub(crate) fn exec_call<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    func: &Operand<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    destination: &Place<'tcx>,
) {
    let caller_id = state.current_frame.current_def_id;
    state.exec_call(func, args, destination.local, caller_id);
}

pub(crate) fn exec_switch_int<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    discr: &Operand<'tcx>,
    targets: &SwitchTargets,
    switch_succ: Option<BasicBlock>,
) {
    let discr_val = state.value_of_operand(discr);

    // If the discriminator is a comparison result, record the direct boolean
    // condition alongside the ite-encoded `discr == value` fact, so the SMT
    // solver can reason about `offset <= len` directly.
    let cmp_cond = discr_val.bool_cond().cloned();

    // Determine which target block is taken along the path.
    if let Some(chosen) = switch_succ {
        for (value, target) in targets.iter() {
            if target == chosen {
                let val_term = Int::from_u64(state.z3_ctx, value as u64);
                state
                    .constraints
                    .assertions
                    .push(discr_val.z3_term._eq(&val_term));
                if value != 0 {
                    if let Some(ref cond) = cmp_cond {
                        state.constraints.assertions.push(cond.clone());
                    }
                    state.infer_switch_guard(discr);
                } else if let Some(ref cond) = cmp_cond {
                    state.constraints.assertions.push(cond.not());
                }
                return;
            }
        }
        // Otherwise branch: the discrim is NOT any of the explicit values.
        if targets.otherwise() == chosen {
            // Negate every explicit target value.
            for (value, _) in targets.iter() {
                let val_term = Int::from_u64(state.z3_ctx, value as u64);
                state
                    .constraints
                    .assertions
                    .push(discr_val.z3_term._eq(&val_term).not());
            }
            if let Some(ref cond) = cmp_cond {
                // For a boolean discriminator, `otherwise` means the comparison
                // result is *not* any explicit value:
                //   - targets include 0 → `discr != 0` → comparison true;
                //   - targets include 1 → `discr != 1` → comparison false.
                if targets.iter().any(|(v, _)| v == 0) {
                    state.constraints.assertions.push(cond.clone());
                } else if targets.iter().any(|(v, _)| v == 1) {
                    state.constraints.assertions.push(cond.not());
                }
            }
        }
    }
}

pub(crate) fn exec_assert<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    cond: &Operand<'tcx>,
    expected: bool,
) {
    let cond_val = state.value_of_operand(cond);
    // If the asserted operand is a comparison result, record the direct boolean
    // condition (`idx < len`) alongside the ite-encoded fact, so the SMT solver
    // can unfold it (mirrors `exec_switchint`).
    let cmp_cond = cond_val.bool_cond().cloned();
    let zero = Int::from_u64(state.z3_ctx, 0);
    if expected {
        state
            .constraints
            .assertions
            .push(cond_val.z3_term._eq(&zero).not());
        if let Some(c) = &cmp_cond {
            state.constraints.assertions.push(c.clone());
        }
    } else {
        state
            .constraints
            .assertions
            .push(cond_val.z3_term._eq(&zero));
        if let Some(c) = &cmp_cond {
            state.constraints.assertions.push(c.not());
        }
    }

    // Guard inference: trace the assert condition back to find non_null sources
    state.infer_guard_non_null(cond, expected);
    // Infer alignment from == 0 guards on Rem expressions
    state.infer_guard_align(cond, expected);
}

pub(crate) fn exec_drop<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    place: &Place<'tcx>,
) {
    state.exec_drop(place);
}
