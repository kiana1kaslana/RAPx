//! MIR transfer functions for the symbolic VM.

use rustc_middle::mir::{
    BasicBlock, Place, Rvalue, Statement, StatementKind, Terminator,
    TerminatorKind,
};

use super::state::{VmState, VmValue};
use crate::verify::mir_support;

pub(crate) mod rvalue;
pub(crate) mod statement;
pub(crate) mod terminator;

pub(crate) fn eval_rvalue<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> VmValue<'z3, 'tcx> {
    match rvalue {
        Rvalue::Use(operand, ..) => rvalue::eval_use(state, place, operand),
        Rvalue::Ref(_, _, source) => rvalue::eval_ref(state, place, source),
        Rvalue::RawPtr(_, source) => rvalue::eval_raw_ptr(state, place, source),
        Rvalue::BinaryOp(op, pair) => rvalue::eval_binary_op(state, place, *op, pair),
        Rvalue::UnaryOp(op, operand) => rvalue::eval_unary_op(state, place, *op, operand),
        Rvalue::Cast(_, operand, ty) => rvalue::eval_cast(state, operand, *ty),
        Rvalue::Aggregate(kind, operands) => rvalue::eval_aggregate(state, place, kind, operands),
        Rvalue::Discriminant(source) => rvalue::eval_discriminant(state, place, source),
        #[cfg(not(rapx_ge_99))]
        Rvalue::ShallowInitBox(operand, _) => rvalue::eval_shallow_init_box(state, place, operand),
        Rvalue::CopyForDeref(source) => rvalue::eval_copy_for_deref(state, place, source),
        Rvalue::Repeat(..) => rvalue::eval_repeat(state, place),
        Rvalue::ThreadLocalRef(..) => rvalue::eval_thread_local_ref(state, place),
        #[cfg(not(rapx_ge_95))]
        Rvalue::NullaryOp(op) => rvalue::eval_nullary_op(state, place, op),
        Rvalue::WrapUnsafeBinder(..) => rvalue::eval_wrap_unsafe_binder(state, place),
        #[cfg(rapx_rvalue_has_reborrow)]
        Rvalue::Reborrow(..) => rvalue::eval_reborrow(state, place),
    }
}

pub(crate) fn exec_terminator<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    terminator: &Terminator<'tcx>,
    switch_succ: Option<BasicBlock>,
) {
    match &terminator.kind {
        TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } => {
            let caller_id = state.current_frame.current_def_id;
            state.exec_call(func, args, destination.local, caller_id);
        }
        TerminatorKind::SwitchInt { discr, targets } => {
            terminator::exec_switch_int(state, discr, targets, switch_succ);
        }
        TerminatorKind::Assert { cond, expected, .. } => {
            terminator::exec_assert(state, cond, *expected);
        }
        TerminatorKind::Drop { place, .. } => terminator::exec_drop(state, place),
        TerminatorKind::Goto { .. }
        | TerminatorKind::Return
        | TerminatorKind::Unreachable
        | TerminatorKind::UnwindResume
        | TerminatorKind::UnwindTerminate(_)
        | TerminatorKind::FalseEdge { .. }
        | TerminatorKind::FalseUnwind { .. } => {}
        _ => {
            debug_assert!(mir_support::unsupported_terminator(&terminator.kind));
            state.unsupported_mir = true;
        }
    }
}

pub(crate) fn exec_statement<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    statement: &Statement<'tcx>,
) {
    match &statement.kind {
        StatementKind::Assign(assign) => {
            let (place, rvalue) = &**assign;
            statement::exec_assign(state, place, rvalue);
        }
        StatementKind::StorageLive(local) => statement::exec_storage_live(state, *local),
        StatementKind::StorageDead(local) => statement::exec_storage_dead(state, *local),
        _ if mir_support::unsupported_statement(&statement.kind) => state.unsupported_mir = true,
        _ => {}
    }
}
