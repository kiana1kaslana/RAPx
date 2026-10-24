//! Rule registry for symbolic MIR execution.

use rustc_middle::mir::{
    BasicBlock, Place, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
};

use super::super::state::{VmState, VmValue};
use super::{rvalue, statement, terminator};
use crate::verify::mir_support::{self, StatementClass, TerminatorClass};

struct StatementRule {
    kind: StatementClass,
    name: &'static str,
    apply: for<'z3, 'tcx> fn(&mut VmState<'z3, 'tcx>, &Statement<'tcx>) -> bool,
}

struct TerminatorRule {
    kind: TerminatorClass,
    name: &'static str,
    apply:
        for<'z3, 'tcx> fn(&mut VmState<'z3, 'tcx>, &Terminator<'tcx>, Option<BasicBlock>) -> bool,
}

struct RvalueRule {
    kind: RvalueRuleKind,
    name: &'static str,
    apply: for<'z3, 'tcx> fn(
        &mut VmState<'z3, 'tcx>,
        &Place<'tcx>,
        &Rvalue<'tcx>,
    ) -> Option<VmValue<'z3, 'tcx>>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum RvalueRuleKind {
    Use,
    Ref,
    RawPtr,
    BinaryOp,
    UnaryOp,
    Cast,
    Aggregate,
    Discriminant,
    #[cfg(not(rapx_ge_99))]
    ShallowInitBox,
    CopyForDeref,
    Repeat,
    ThreadLocalRef,
    #[cfg(not(rapx_ge_95))]
    NullaryOp,
    WrapUnsafeBinder,
    #[cfg(rapx_rvalue_has_reborrow)]
    Reborrow,
    Unsupported,
}

const STATEMENT_RULES: &[StatementRule] = &[
    StatementRule {
        kind: StatementClass::Assign,
        name: "Assign",
        apply: |state, stmt| {
            let StatementKind::Assign(assign) = &stmt.kind else {
                return false;
            };
            let (place, rvalue) = &**assign;
            statement::exec_assign(state, place, rvalue);
            true
        },
    },
    StatementRule {
        kind: StatementClass::StorageLive,
        name: "StorageLive",
        apply: |state, stmt| {
            let StatementKind::StorageLive(local) = stmt.kind else {
                return false;
            };
            statement::exec_storage_live(state, local);
            true
        },
    },
    StatementRule {
        kind: StatementClass::StorageDead,
        name: "StorageDead",
        apply: |state, stmt| {
            let StatementKind::StorageDead(local) = stmt.kind else {
                return false;
            };
            statement::exec_storage_dead(state, local);
            true
        },
    },
    StatementRule {
        kind: StatementClass::Ignored,
        name: "Ignored",
        apply: |_state, _stmt| true,
    },
    StatementRule {
        kind: StatementClass::Unsupported,
        name: "Unsupported",
        apply: |state, _stmt| {
            state.unsupported_mir = true;
            true
        },
    },
];

const TERMINATOR_RULES: &[TerminatorRule] = &[
    TerminatorRule {
        kind: TerminatorClass::Call,
        name: "Call",
        apply: |state, term, _| {
            let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &term.kind
            else {
                return false;
            };
            let caller_id = state.current_frame.current_def_id;
            state.exec_call(func, args, destination.local, caller_id);
            true
        },
    },
    TerminatorRule {
        kind: TerminatorClass::SwitchInt,
        name: "SwitchInt",
        apply: |state, term, successor| {
            let TerminatorKind::SwitchInt { discr, targets } = &term.kind else {
                return false;
            };
            terminator::exec_switch_int(state, discr, targets, successor);
            true
        },
    },
    TerminatorRule {
        kind: TerminatorClass::Assert,
        name: "Assert",
        apply: |state, term, _| {
            let TerminatorKind::Assert { cond, expected, .. } = &term.kind else {
                return false;
            };
            terminator::exec_assert(state, cond, *expected);
            true
        },
    },
    TerminatorRule {
        kind: TerminatorClass::Drop,
        name: "Drop",
        apply: |state, term, _| {
            let TerminatorKind::Drop { place, .. } = &term.kind else {
                return false;
            };
            terminator::exec_drop(state, place);
            true
        },
    },
    TerminatorRule {
        kind: TerminatorClass::Ignored,
        name: "Ignored",
        apply: |_state, _term, _| true,
    },
    TerminatorRule {
        kind: TerminatorClass::Unsupported,
        name: "Unsupported",
        apply: |state, _term, _| {
            state.unsupported_mir = true;
            true
        },
    },
];

const RVALUE_RULES: &[RvalueRule] = &[
    RvalueRule {
        kind: RvalueRuleKind::Use,
        name: "Use",
        apply: |state, place, rv| match rv {
            Rvalue::Use(operand, ..) => Some(rvalue::eval_use(state, place, operand)),
            _ => None,
        },
    },
    RvalueRule {
        kind: RvalueRuleKind::Ref,
        name: "Ref",
        apply: |state, place, rv| match rv {
            Rvalue::Ref(_, _, source) => Some(rvalue::eval_ref(state, place, source)),
            _ => None,
        },
    },
    RvalueRule {
        kind: RvalueRuleKind::RawPtr,
        name: "RawPtr",
        apply: |state, place, rv| match rv {
            Rvalue::RawPtr(_, source) => Some(rvalue::eval_raw_ptr(state, place, source)),
            _ => None,
        },
    },
    RvalueRule {
        kind: RvalueRuleKind::BinaryOp,
        name: "BinaryOp",
        apply: |state, place, rv| match rv {
            Rvalue::BinaryOp(op, pair) => Some(rvalue::eval_binary_op(state, place, *op, pair)),
            _ => None,
        },
    },
    RvalueRule {
        kind: RvalueRuleKind::UnaryOp,
        name: "UnaryOp",
        apply: |state, place, rv| match rv {
            Rvalue::UnaryOp(op, operand) => Some(rvalue::eval_unary_op(state, place, *op, operand)),
            _ => None,
        },
    },
    RvalueRule {
        kind: RvalueRuleKind::Cast,
        name: "Cast",
        apply: |state, _place, rv| match rv {
            Rvalue::Cast(_, operand, ty) => Some(rvalue::eval_cast(state, operand, *ty)),
            _ => None,
        },
    },
    RvalueRule {
        kind: RvalueRuleKind::Aggregate,
        name: "Aggregate",
        apply: |state, place, rv| match rv {
            Rvalue::Aggregate(kind, operands) => {
                Some(rvalue::eval_aggregate(state, place, kind, operands))
            }
            _ => None,
        },
    },
    RvalueRule {
        kind: RvalueRuleKind::Discriminant,
        name: "Discriminant",
        apply: |state, place, rv| match rv {
            Rvalue::Discriminant(source) => Some(rvalue::eval_discriminant(state, place, source)),
            _ => None,
        },
    },
    #[cfg(not(rapx_ge_99))]
    RvalueRule {
        kind: RvalueRuleKind::ShallowInitBox,
        name: "ShallowInitBox",
        apply: |state, place, rv| match rv {
            Rvalue::ShallowInitBox(operand, _) => {
                Some(rvalue::eval_shallow_init_box(state, place, operand))
            }
            _ => None,
        },
    },
    RvalueRule {
        kind: RvalueRuleKind::CopyForDeref,
        name: "CopyForDeref",
        apply: |state, place, rv| match rv {
            Rvalue::CopyForDeref(source) => Some(rvalue::eval_copy_for_deref(state, place, source)),
            _ => None,
        },
    },
    RvalueRule {
        kind: RvalueRuleKind::Repeat,
        name: "Repeat",
        apply: |state, place, rv| match rv {
            Rvalue::Repeat(..) => Some(rvalue::eval_fresh_value(state, place, "repeat")),
            _ => None,
        },
    },
    RvalueRule {
        kind: RvalueRuleKind::ThreadLocalRef,
        name: "ThreadLocalRef",
        apply: |state, place, rv| match rv {
            Rvalue::ThreadLocalRef(..) => {
                Some(rvalue::eval_fresh_value(state, place, "thread_local"))
            }
            _ => None,
        },
    },
    #[cfg(not(rapx_ge_95))]
    RvalueRule {
        kind: RvalueRuleKind::NullaryOp,
        name: "NullaryOp",
        apply: |state, place, rv| match rv {
            Rvalue::NullaryOp(op) => Some(rvalue::eval_nullary_op(state, place, op)),
            _ => None,
        },
    },
    RvalueRule {
        kind: RvalueRuleKind::WrapUnsafeBinder,
        name: "WrapUnsafeBinder",
        apply: |state, place, rv| match rv {
            Rvalue::WrapUnsafeBinder(..) => {
                Some(rvalue::eval_fresh_value(state, place, "wrap_unsafe_binder"))
            }
            _ => None,
        },
    },
    #[cfg(rapx_rvalue_has_reborrow)]
    RvalueRule {
        kind: RvalueRuleKind::Reborrow,
        name: "Reborrow",
        apply: |state, place, rv| match rv {
            Rvalue::Reborrow(..) => Some(rvalue::eval_reborrow(state, place)),
            _ => None,
        },
    },
    RvalueRule {
        kind: RvalueRuleKind::Unsupported,
        name: "Unsupported",
        apply: |state, place, _| {
            state.unsupported_mir = true;
            Some(rvalue::eval_fresh_value(state, place, "unsupported_rvalue"))
        },
    },
];

pub(super) fn exec_statement<'z3, 'tcx>(state: &mut VmState<'z3, 'tcx>, stmt: &Statement<'tcx>) {
    let kind = mir_support::statement_class(&stmt.kind);
    let rule = STATEMENT_RULES
        .iter()
        .find(|rule| rule.kind == kind)
        .expect("statement rule is not registered");
    assert!(
        (rule.apply)(state, stmt),
        "statement rule does not match its MIR kind"
    );
    log::trace!("vm statement rule: {}", rule.name);
}

pub(super) fn exec_terminator<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    term: &Terminator<'tcx>,
    successor: Option<BasicBlock>,
) {
    let kind = mir_support::terminator_class(&term.kind);
    let rule = TERMINATOR_RULES
        .iter()
        .find(|rule| rule.kind == kind)
        .expect("terminator rule is not registered");
    assert!(
        (rule.apply)(state, term, successor),
        "terminator rule does not match its MIR kind"
    );
    log::trace!("vm terminator rule: {}", rule.name);
}

pub(super) fn eval_rvalue<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    place: &Place<'tcx>,
    rv: &Rvalue<'tcx>,
) -> VmValue<'z3, 'tcx> {
    let kind = rvalue_rule_kind(rv);
    let rule = RVALUE_RULES
        .iter()
        .find(|rule| rule.kind == kind)
        .expect("rvalue rule is not registered");
    let value = (rule.apply)(state, place, rv).expect("rvalue rule does not match its MIR kind");
    log::trace!("vm rvalue rule: {}", rule.name);
    value
}

#[allow(unreachable_patterns)]
fn rvalue_rule_kind(rv: &Rvalue<'_>) -> RvalueRuleKind {
    match rv {
        Rvalue::Use(..) => RvalueRuleKind::Use,
        Rvalue::Ref(..) => RvalueRuleKind::Ref,
        Rvalue::RawPtr(..) => RvalueRuleKind::RawPtr,
        Rvalue::BinaryOp(..) => RvalueRuleKind::BinaryOp,
        Rvalue::UnaryOp(..) => RvalueRuleKind::UnaryOp,
        Rvalue::Cast(..) => RvalueRuleKind::Cast,
        Rvalue::Aggregate(..) => RvalueRuleKind::Aggregate,
        Rvalue::Discriminant(..) => RvalueRuleKind::Discriminant,
        #[cfg(not(rapx_ge_99))]
        Rvalue::ShallowInitBox(..) => RvalueRuleKind::ShallowInitBox,
        Rvalue::CopyForDeref(..) => RvalueRuleKind::CopyForDeref,
        Rvalue::Repeat(..) => RvalueRuleKind::Repeat,
        Rvalue::ThreadLocalRef(..) => RvalueRuleKind::ThreadLocalRef,
        #[cfg(not(rapx_ge_95))]
        Rvalue::NullaryOp(..) => RvalueRuleKind::NullaryOp,
        Rvalue::WrapUnsafeBinder(..) => RvalueRuleKind::WrapUnsafeBinder,
        #[cfg(rapx_rvalue_has_reborrow)]
        Rvalue::Reborrow(..) => RvalueRuleKind::Reborrow,
        _ => RvalueRuleKind::Unsupported,
    }
}
