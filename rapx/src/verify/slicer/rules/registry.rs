//! Rule registry for backward MIR slicing.

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Body, Statement, StatementKind, Terminator, TerminatorKind};

use crate::analysis::dataflow::types::DataflowGraph;
use crate::helpers::def_use::RelevantPlaces;
use crate::verify::mir_support::{self, StatementClass, TerminatorClass};

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
    kind: StatementClass,
    name: &'static str,
    apply: for<'a, 'tcx> fn(&mut StatementContext<'a, 'tcx>) -> bool,
}

struct TerminatorRule {
    kind: TerminatorClass,
    name: &'static str,
    apply: for<'a, 'tcx> fn(&mut TerminatorContext<'a, 'tcx>) -> bool,
}

const STATEMENT_RULES: &[StatementRule] = &[
    StatementRule {
        kind: StatementClass::Assign,
        name: "Assign",
        apply: assign,
    },
    StatementRule {
        kind: StatementClass::StorageDead,
        name: "StorageDead",
        apply: storage_dead,
    },
    StatementRule {
        kind: StatementClass::StorageLive,
        name: "StorageLive",
        apply: storage_live,
    },
    StatementRule {
        kind: StatementClass::Ignored,
        name: "Ignored",
        apply: ignored_statement,
    },
    StatementRule {
        kind: StatementClass::Unsupported,
        name: "Unsupported",
        apply: unsupported_statement,
    },
];

const TERMINATOR_RULES: &[TerminatorRule] = &[
    TerminatorRule {
        kind: TerminatorClass::Call,
        name: "Call",
        apply: call,
    },
    TerminatorRule {
        kind: TerminatorClass::SwitchInt,
        name: "SwitchInt",
        apply: switch_int,
    },
    TerminatorRule {
        kind: TerminatorClass::Assert,
        name: "Assert",
        apply: assert,
    },
    TerminatorRule {
        kind: TerminatorClass::Drop,
        name: "Drop",
        apply: drop,
    },
    TerminatorRule {
        kind: TerminatorClass::Ignored,
        name: "Ignored",
        apply: ignored_terminator,
    },
    TerminatorRule {
        kind: TerminatorClass::Unsupported,
        name: "Unsupported",
        apply: unsupported_terminator,
    },
];

pub(super) fn apply_statement(ctx: &mut StatementContext<'_, '_>) {
    let kind = mir_support::statement_class(&ctx.statement.kind);
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
    let kind = mir_support::terminator_class(&ctx.terminator.kind);
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

fn ignored_statement(_ctx: &mut StatementContext<'_, '_>) -> bool {
    true
}

fn unsupported_statement(ctx: &mut StatementContext<'_, '_>) -> bool {
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
    ctx.items.push(RelevantItem::Terminator {
        def_id: ctx.def_id,
        block: ctx.block,
        switch_succ: None,
    });
    true
}
