//! Backward relevance rules for MIR terminators.

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Body, TerminatorKind};

use crate::analysis::dataflow::types::DataflowGraph;
use crate::helpers::def_use::{call_args_uses_at, terminator_use_def, RelevantPlaces};
use crate::helpers::mir_utils;
use crate::verify::mir_support;

use super::call;
use super::super::types::RelevantItem;
use super::super::visitor::BackwardSlicer;

impl<'tcx> BackwardSlicer<'tcx> {
    /// Visit one MIR terminator against the current relevance frontier.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::verify::slicer) fn visit_terminator(
        &self,
        def_id: DefId,
        block: BasicBlock,
        terminator: &rustc_middle::mir::Terminator<'tcx>,
        flow: &DataflowGraph,
        body: &Body<'tcx>,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<RelevantItem<'tcx>>,
        keep_invalidations: bool,
        keep_owner: bool,
        successor: Option<BasicBlock>,
    ) {
        if mir_support::unsupported_terminator(&terminator.kind) {
            items.push(RelevantItem::Terminator { def_id, block, switch_succ: None });
            return;
        }
        if keep_invalidations {
            if matches!(terminator.kind, TerminatorKind::Drop { .. }) {
                items.push(RelevantItem::Terminator { def_id, block, switch_succ: None });
                return;
            }
            // A manual drop (`std::mem::drop` / `ManuallyDrop::drop`) also frees
            // the pointee's heap: keep the call and its argument's construction
            // chain so `Allocated`/`Owning` can see the freed allocation and
            // detect a later use / second drop.
            if let TerminatorKind::Call { func, args, .. } = &terminator.kind {
                let is_drop_call =
                    mir_utils::dep_callee_def_id(func).is_some_and(|c| {
                        crate::verify::api_classify::is_manually_drop_drop(Some(c))
                            || crate::verify::api_classify::is_std_drop(Some(c))
                    });
                if is_drop_call {
                    items.push(RelevantItem::Terminator { def_id, block, switch_succ: None });
                    relevant.extend(call_args_uses_at(args, &[0]));
                    return;
                }
            }
        }

        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        {
            // `Owning` traces an owner's construction chain: keep a call whose
            // destination is a `needs_drop` value even when that local is not
            // itself relevant, so its field provenance survives.
            if keep_owner {
                let dest_ty = body.local_decls[destination.local].ty;
                let typing_env = rustc_middle::ty::TypingEnv::non_body_analysis(self.tcx, def_id);
                if dest_ty.needs_drop(self.tcx, typing_env) {
                    let use_def = terminator_use_def(terminator);
                    items.push(RelevantItem::Terminator { def_id, block, switch_succ: None });
                    relevant.remove_all(&use_def.defs);
                    relevant.extend(use_def.uses);
                    return;
                }
            }
            call::visit(
                self.tcx,
                def_id,
                block,
                func,
                args,
                destination,
                flow,
                body,
                relevant,
                items,
            );
            return;
        }

        let use_def = terminator_use_def(terminator);
        if terminator_is_path_condition(terminator) {
            let switch_succ = match terminator.kind {
                TerminatorKind::SwitchInt { .. } => successor,
                _ => None,
            };
            items.push(RelevantItem::Terminator { def_id, block, switch_succ });
            relevant.extend(use_def.uses.clone());
            return;
        }

        if use_def.defs.intersects(relevant) {
            items.push(RelevantItem::Terminator { def_id, block, switch_succ: None });
            relevant.remove_all(&use_def.defs);
            relevant.extend(use_def.uses);
            return;
        }

        if use_def.uses.intersects(relevant) {
            items.push(RelevantItem::Terminator { def_id, block, switch_succ: None });
        }
    }
}

fn terminator_is_path_condition(terminator: &rustc_middle::mir::Terminator<'_>) -> bool {
    matches!(
        terminator.kind,
        TerminatorKind::SwitchInt { .. } | TerminatorKind::Assert { .. }
    )
}
