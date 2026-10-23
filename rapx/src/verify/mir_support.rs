//! MIR forms whose effects the symbolic VM can model.

use rustc_middle::mir::{NonDivergingIntrinsic, StatementKind, TerminatorKind};

pub(crate) fn unsupported_statement(kind: &StatementKind<'_>) -> bool {
    !matches!(
        kind,
        StatementKind::Assign(..) | StatementKind::StorageLive(..) | StatementKind::StorageDead(..)
    ) && !ignored_statement(kind)
}

pub(crate) fn ignored_statement(kind: &StatementKind<'_>) -> bool {
    matches!(kind, StatementKind::Intrinsic(intrinsic) if matches!(&**intrinsic, NonDivergingIntrinsic::Assume(..)))
        || matches!(
            kind,
            StatementKind::FakeRead(..)
                | StatementKind::AscribeUserType(..)
                | StatementKind::Coverage(..)
                | StatementKind::PlaceMention(..)
                | StatementKind::ConstEvalCounter
                | StatementKind::Nop
        )
}

pub(crate) fn unsupported_terminator(kind: &TerminatorKind<'_>) -> bool {
    !matches!(
        kind,
        TerminatorKind::Call { .. }
            | TerminatorKind::SwitchInt { .. }
            | TerminatorKind::Assert { .. }
            | TerminatorKind::Drop { .. }
    ) && !ignored_terminator(kind)
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
