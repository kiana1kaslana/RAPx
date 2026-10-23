//! Backward relevance rules for MIR statements and terminators.

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Body, Statement, StatementKind, Terminator, TerminatorKind};

use crate::analysis::dataflow::types::DataflowGraph;
use crate::helpers::def_use::RelevantPlaces;
use crate::verify::mir_support;

use super::types::RelevantItem;
use super::visitor::BackwardSlicer;

mod call;
mod statement;
mod terminator;

impl<'tcx> BackwardSlicer<'tcx> {
    #[allow(clippy::too_many_arguments)]
    pub(in crate::verify::slicer) fn visit_statement(
        &self,
        def_id: DefId,
        block: BasicBlock,
        statement_index: usize,
        statement: &'tcx Statement<'tcx>,
        flow: &DataflowGraph,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<RelevantItem<'tcx>>,
        keep_invalidations: bool,
        keep_owner: bool,
    ) {
        match &statement.kind {
            StatementKind::Assign(assign) => {
                let (place, rvalue) = &**assign;
                self.visit_assign_statement(
                    def_id,
                    block,
                    statement_index,
                    place,
                    rvalue,
                    flow,
                    relevant,
                    items,
                    keep_owner,
                );
            }
            StatementKind::StorageDead(local) => statement::visit_storage_dead(
                def_id,
                block,
                statement_index,
                *local,
                flow,
                relevant,
                items,
                keep_invalidations,
            ),
            StatementKind::StorageLive(..) if keep_invalidations => {
                items.push(RelevantItem::Statement {
                    def_id,
                    block,
                    statement_index,
                });
            }
            _ if mir_support::unsupported_statement(&statement.kind) => {
                items.push(RelevantItem::Statement {
                    def_id,
                    block,
                    statement_index,
                });
            }
            _ => {}
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::verify::slicer) fn visit_terminator(
        &self,
        def_id: DefId,
        block: BasicBlock,
        terminator: &Terminator<'tcx>,
        flow: &DataflowGraph,
        body: &Body<'tcx>,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<RelevantItem<'tcx>>,
        keep_invalidations: bool,
        keep_owner: bool,
        successor: Option<BasicBlock>,
    ) {
        match &terminator.kind {
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                self.visit_call_terminator(
                    def_id,
                    block,
                    terminator,
                    func,
                    args,
                    destination,
                    flow,
                    body,
                    relevant,
                    items,
                    keep_invalidations,
                    keep_owner,
                );
            }
            _ if mir_support::unsupported_terminator(&terminator.kind) => {
                items.push(RelevantItem::Terminator {
                    def_id,
                    block,
                    switch_succ: None,
                });
            }
            _ => terminator::visit_non_call_terminator(
                def_id,
                block,
                terminator,
                relevant,
                items,
                keep_invalidations,
                successor,
            ),
        }
    }
}
