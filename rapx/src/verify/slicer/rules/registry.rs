//! Rule registry for backward MIR slicing.

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Body, Statement, StatementKind, Terminator, TerminatorKind};

use crate::analysis::dataflow::types::DataflowGraph;
use crate::helpers::def_use::RelevantPlaces;
use crate::verify::mir_support;

use super::super::types::RelevantItem;
use super::super::visitor::BackwardSlicer;
use super::{statement, terminator};

pub(super) struct StatementContext<'a, 'tcx> {
    pub slicer: &'a BackwardSlicer<'tcx>,
    pub def_id: DefId,
    pub block: BasicBlock,
    pub statement_index: usize,
    pub statement: &'tcx Statement<'tcx>,
    pub flow: &'a DataflowGraph,
    pub relevant: &'a mut RelevantPlaces,
    pub items: &'a mut Vec<RelevantItem<'tcx>>,
    pub keep_invalidations: bool,
    pub keep_owner: bool,
}

pub(super) struct TerminatorContext<'a, 'tcx> {
    pub slicer: &'a BackwardSlicer<'tcx>,
    pub def_id: DefId,
    pub block: BasicBlock,
    pub terminator: &'a Terminator<'tcx>,
    pub flow: &'a DataflowGraph,
    pub body: &'a Body<'tcx>,
    pub relevant: &'a mut RelevantPlaces,
    pub items: &'a mut Vec<RelevantItem<'tcx>>,
    pub keep_invalidations: bool,
    pub keep_owner: bool,
    pub successor: Option<BasicBlock>,
}

struct StatementRule {
    kind: StatementRuleKind,
    name: &'static str,
    apply: for<'a, 'tcx> fn(&mut StatementContext<'a, 'tcx>) -> bool,
}

struct TerminatorRule {
    kind: TerminatorRuleKind,
    name: &'static str,
    apply: for<'a, 'tcx> fn(&mut TerminatorContext<'a, 'tcx>) -> bool,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum StatementRuleKind {
    Assign,
    StorageDead,
    StorageLive,
    Ignored,
    Unsupported,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum TerminatorRuleKind {
    Call,
    SwitchInt,
    Assert,
    Drop,
    Ignored,
    Unsupported,
}

const STATEMENT_RULES: &[StatementRule] = &[
    StatementRule {
        kind: StatementRuleKind::Assign,
        name: "Assign",
        apply: assign,
    },
    StatementRule {
        kind: StatementRuleKind::StorageDead,
        name: "StorageDead",
        apply: storage_dead,
    },
    StatementRule {
        kind: StatementRuleKind::StorageLive,
        name: "StorageLive",
        apply: storage_live,
    },
    StatementRule {
        kind: StatementRuleKind::Ignored,
        name: "Ignored",
        apply: ignored_statement,
    },
    StatementRule {
        kind: StatementRuleKind::Unsupported,
        name: "Unsupported",
        apply: unsupported_statement,
    },
];

const TERMINATOR_RULES: &[TerminatorRule] = &[
    TerminatorRule {
        kind: TerminatorRuleKind::Call,
        name: "Call",
        apply: call,
    },
    TerminatorRule {
        kind: TerminatorRuleKind::SwitchInt,
        name: "SwitchInt",
        apply: switch_int,
    },
    TerminatorRule {
        kind: TerminatorRuleKind::Assert,
        name: "Assert",
        apply: assert,
    },
    TerminatorRule {
        kind: TerminatorRuleKind::Drop,
        name: "Drop",
        apply: drop,
    },
    TerminatorRule {
        kind: TerminatorRuleKind::Ignored,
        name: "Ignored",
        apply: ignored_terminator,
    },
    TerminatorRule {
        kind: TerminatorRuleKind::Unsupported,
        name: "Unsupported",
        apply: unsupported_terminator,
    },
];

pub(super) fn apply_statement(ctx: &mut StatementContext<'_, '_>) {
    let kind = statement_rule_kind(&ctx.statement.kind);
    let rule = STATEMENT_RULES
        .iter()
        .find(|rule| rule.kind == kind)
        .expect("statement rule is not registered");
    assert!(
        (rule.apply)(ctx),
        "statement rule does not match its MIR kind"
    );
    log::trace!("slicer statement rule: {}", rule.name);
}

pub(super) fn apply_terminator(ctx: &mut TerminatorContext<'_, '_>) {
    let kind = terminator_rule_kind(&ctx.terminator.kind);
    let rule = TERMINATOR_RULES
        .iter()
        .find(|rule| rule.kind == kind)
        .expect("terminator rule is not registered");
    assert!(
        (rule.apply)(ctx),
        "terminator rule does not match its MIR kind"
    );
    log::trace!("slicer terminator rule: {}", rule.name);
}

fn statement_rule_kind(kind: &StatementKind<'_>) -> StatementRuleKind {
    match kind {
        StatementKind::Assign(..) => StatementRuleKind::Assign,
        StatementKind::StorageDead(..) => StatementRuleKind::StorageDead,
        StatementKind::StorageLive(..) => StatementRuleKind::StorageLive,
        _ if mir_support::ignored_statement(kind) => StatementRuleKind::Ignored,
        _ => StatementRuleKind::Unsupported,
    }
}

fn terminator_rule_kind(kind: &TerminatorKind<'_>) -> TerminatorRuleKind {
    match kind {
        TerminatorKind::Call { .. } => TerminatorRuleKind::Call,
        TerminatorKind::SwitchInt { .. } => TerminatorRuleKind::SwitchInt,
        TerminatorKind::Assert { .. } => TerminatorRuleKind::Assert,
        TerminatorKind::Drop { .. } => TerminatorRuleKind::Drop,
        _ if mir_support::ignored_terminator(kind) => TerminatorRuleKind::Ignored,
        _ => TerminatorRuleKind::Unsupported,
    }
}

fn assign(ctx: &mut StatementContext<'_, '_>) -> bool {
    let StatementKind::Assign(assign) = &ctx.statement.kind else {
        return false;
    };
    let (place, rvalue) = &**assign;
    ctx.slicer.visit_assign_statement(
        ctx.def_id,
        ctx.block,
        ctx.statement_index,
        place,
        rvalue,
        ctx.flow,
        ctx.relevant,
        ctx.items,
        ctx.keep_owner,
    );
    true
}

fn storage_dead(ctx: &mut StatementContext<'_, '_>) -> bool {
    let StatementKind::StorageDead(local) = ctx.statement.kind else {
        return false;
    };
    statement::visit_storage_dead(
        ctx.def_id,
        ctx.block,
        ctx.statement_index,
        local,
        ctx.flow,
        ctx.relevant,
        ctx.items,
        ctx.keep_invalidations,
    );
    true
}

fn storage_live(ctx: &mut StatementContext<'_, '_>) -> bool {
    if !matches!(ctx.statement.kind, StatementKind::StorageLive(..)) {
        return false;
    }
    if ctx.keep_invalidations {
        ctx.items.push(RelevantItem::Statement {
            def_id: ctx.def_id,
            block: ctx.block,
            statement_index: ctx.statement_index,
        });
    }
    true
}

fn ignored_statement(ctx: &mut StatementContext<'_, '_>) -> bool {
    mir_support::ignored_statement(&ctx.statement.kind)
}

fn unsupported_statement(ctx: &mut StatementContext<'_, '_>) -> bool {
    debug_assert!(mir_support::unsupported_statement(&ctx.statement.kind));
    ctx.items.push(RelevantItem::Statement {
        def_id: ctx.def_id,
        block: ctx.block,
        statement_index: ctx.statement_index,
    });
    true
}

fn call(ctx: &mut TerminatorContext<'_, '_>) -> bool {
    let TerminatorKind::Call {
        func,
        args,
        destination,
        ..
    } = &ctx.terminator.kind
    else {
        return false;
    };
    ctx.slicer.visit_call_terminator(
        ctx.def_id,
        ctx.block,
        ctx.terminator,
        func,
        args,
        destination,
        ctx.flow,
        ctx.body,
        ctx.relevant,
        ctx.items,
        ctx.keep_invalidations,
        ctx.keep_owner,
    );
    true
}

fn switch_int(ctx: &mut TerminatorContext<'_, '_>) -> bool {
    if !matches!(ctx.terminator.kind, TerminatorKind::SwitchInt { .. }) {
        return false;
    }
    visit_non_call(ctx);
    true
}

fn assert(ctx: &mut TerminatorContext<'_, '_>) -> bool {
    if !matches!(ctx.terminator.kind, TerminatorKind::Assert { .. }) {
        return false;
    }
    visit_non_call(ctx);
    true
}

fn drop(ctx: &mut TerminatorContext<'_, '_>) -> bool {
    if !matches!(ctx.terminator.kind, TerminatorKind::Drop { .. }) {
        return false;
    }
    visit_non_call(ctx);
    true
}

fn ignored_terminator(ctx: &mut TerminatorContext<'_, '_>) -> bool {
    if !mir_support::ignored_terminator(&ctx.terminator.kind) {
        return false;
    }
    visit_non_call(ctx);
    true
}

fn visit_non_call(ctx: &mut TerminatorContext<'_, '_>) {
    terminator::visit_non_call_terminator(
        ctx.def_id,
        ctx.block,
        ctx.terminator,
        ctx.relevant,
        ctx.items,
        ctx.keep_invalidations,
        ctx.successor,
    );
}

fn unsupported_terminator(ctx: &mut TerminatorContext<'_, '_>) -> bool {
    debug_assert!(mir_support::unsupported_terminator(&ctx.terminator.kind));
    ctx.items.push(RelevantItem::Terminator {
        def_id: ctx.def_id,
        block: ctx.block,
        switch_succ: None,
    });
    true
}
