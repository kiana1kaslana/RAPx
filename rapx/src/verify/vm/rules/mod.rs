//! MIR transfer functions for the symbolic VM.

use rustc_middle::mir::{BasicBlock, Place, Rvalue, Statement, Terminator};

use super::state::{VmState, VmValue};

mod registry;
pub(crate) mod rvalue;
pub(crate) mod statement;
pub(crate) mod terminator;

pub(crate) fn eval_rvalue<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> VmValue<'z3, 'tcx> {
    registry::eval_rvalue(state, place, rvalue)
}

pub(crate) fn exec_terminator<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    terminator: &Terminator<'tcx>,
    switch_succ: Option<BasicBlock>,
) {
    registry::exec_terminator(state, terminator, switch_succ);
}

pub(crate) fn exec_statement<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    statement: &Statement<'tcx>,
) {
    registry::exec_statement(state, statement);
}
