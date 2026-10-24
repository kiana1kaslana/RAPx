//! Shared MIR classification for slicing and symbolic execution.

use rustc_middle::mir::{NonDivergingIntrinsic, StatementKind, TerminatorKind};

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum StatementClass {
    Assign,
    StorageLive,
    StorageDead,
    Ignored,
    Unsupported,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum TerminatorClass {
    Call,
    SwitchInt,
    Assert,
    Drop,
    Ignored,
    Unsupported,
}

pub(crate) fn statement_class(kind: &StatementKind<'_>) -> StatementClass {
    match kind {
        StatementKind::Assign(..) => StatementClass::Assign,
        StatementKind::StorageLive(..) => StatementClass::StorageLive,
        StatementKind::StorageDead(..) => StatementClass::StorageDead,
        StatementKind::Intrinsic(intrinsic)
            if matches!(&**intrinsic, NonDivergingIntrinsic::Assume(..)) =>
        {
            StatementClass::Ignored
        }
        StatementKind::FakeRead(..)
        | StatementKind::AscribeUserType(..)
        | StatementKind::Coverage(..)
        | StatementKind::PlaceMention(..)
        | StatementKind::ConstEvalCounter
        | StatementKind::Nop => StatementClass::Ignored,
        _ => StatementClass::Unsupported,
    }
}

pub(crate) fn terminator_class(kind: &TerminatorKind<'_>) -> TerminatorClass {
    match kind {
        TerminatorKind::Call { .. } => TerminatorClass::Call,
        TerminatorKind::SwitchInt { .. } => TerminatorClass::SwitchInt,
        TerminatorKind::Assert { .. } => TerminatorClass::Assert,
        TerminatorKind::Drop { .. } => TerminatorClass::Drop,
        TerminatorKind::Goto { .. }
        | TerminatorKind::Return
        | TerminatorKind::Unreachable
        | TerminatorKind::UnwindResume
        | TerminatorKind::UnwindTerminate(_)
        | TerminatorKind::FalseEdge { .. }
        | TerminatorKind::FalseUnwind { .. } => TerminatorClass::Ignored,
        _ => TerminatorClass::Unsupported,
    }
}
