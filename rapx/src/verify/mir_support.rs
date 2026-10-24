//! MIR forms without a dedicated slicer or VM transfer rule.

use rustc_middle::mir::{StatementKind, TerminatorKind};

pub(crate) fn ignored_statement(kind: &StatementKind<'_>) -> bool {
    matches!(
        kind,
        StatementKind::FakeRead(..)
                | StatementKind::AscribeUserType(..)
                | StatementKind::Coverage(..)
                | StatementKind::PlaceMention(..)
                | StatementKind::ConstEvalCounter
                | StatementKind::Nop
                | StatementKind::BackwardIncompatibleDropHint { .. }
    )
}

pub(crate) fn ignored_terminator(kind: &TerminatorKind<'_>) -> bool {
    matches!(
        kind,
        TerminatorKind::Goto { .. }
            | TerminatorKind::Return
            | TerminatorKind::Unreachable
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(_)
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. }
    )
}
