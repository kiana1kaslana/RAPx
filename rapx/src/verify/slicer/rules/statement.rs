//! Backward relevance rules for MIR statements.

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Operand, Rvalue, StatementKind};

use crate::analysis::dataflow::types::DataflowGraph;
use crate::helpers::def_use::{operand_uses, RelevantPlaces};
use crate::helpers::mir_utils;
use crate::verify::mir_support;

use super::super::types::RelevantItem;
use super::super::visitor::BackwardSlicer;

impl<'tcx> BackwardSlicer<'tcx> {
    /// Visit one MIR statement against the current relevance frontier.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::verify::slicer) fn visit_statement(
        &self,
        def_id: DefId,
        block: BasicBlock,
        statement_index: usize,
        statement: &'tcx rustc_middle::mir::Statement<'tcx>,
        flow: &DataflowGraph,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<RelevantItem<'tcx>>,
        keep_invalidations: bool,
        keep_owner: bool,
    ) {
        if mir_support::unsupported_statement(&statement.kind) {
            items.push(RelevantItem::Statement {
                def_id,
                block,
                statement_index,
            });
            return;
        }
        if keep_invalidations
            && matches!(
                statement.kind,
                StatementKind::StorageDead(_) | StatementKind::StorageLive(_)
            )
        {
            items.push(RelevantItem::Statement {
                def_id,
                block,
                statement_index,
            });
            return;
        }

        // Keep the definition of a `needs_drop` local (an owner's construction
        // chain) so `Owning` can trace its field provenance.
        if keep_owner
            && let StatementKind::Assign(assign) = &statement.kind {
                let (place, _) = &**assign;
                let body = self.tcx.optimized_mir(def_id);
                let ty = body.local_decls[place.local].ty;
                let typing_env = rustc_middle::ty::TypingEnv::non_body_analysis(self.tcx, def_id);
                if ty.needs_drop(self.tcx, typing_env) {
                    let mut defs = RelevantPlaces::new();
                    defs.insert_mir_place(place);
                    let uses =
                        collect_statement_uses(statement, block, statement_index, flow, &defs);
                    items.push(RelevantItem::Statement {
                        def_id,
                        block,
                        statement_index,
                    });
                    relevant.remove_all(&defs);
                    relevant.extend(uses);
                    return;
                }
            }

        let mut defs = RelevantPlaces::new();
        match &statement.kind {
            StatementKind::Assign(assign) => {
                let (place, _) = &**assign;
                defs.insert_mir_place(place);
            }
            StatementKind::StorageDead(local) => {
                defs.insert_local(*local);
            }
            _ => {}
        }

        // A provenance-carrying assignment — a pointer cast (`*const T as
        // *const U`, a reference→pointer cast) or a reborrow through a
        // reference/pointer (`&mut (*_1)`) — carries the source's
        // provenance/align_n even when its destination is not *value*-relevant
        // to the property.  Keep it — and follow its source — so the forward VM
        // propagates the provenance instead of relying on the backward
        // `propagate_single_assign` fill-in.
        let is_provenance_carrier = match &statement.kind {
            StatementKind::Assign(assign) => {
                let (place, rvalue) = &**assign;
                let dest_is_ptr = matches!(
                    self.tcx.optimized_mir(def_id).local_decls[place.local].ty.kind(),
                    rustc_middle::ty::TyKind::RawPtr(..) | rustc_middle::ty::TyKind::Ref(..)
                );
                match rvalue {
                    Rvalue::Cast(..) => dest_is_ptr,
                    Rvalue::Ref(_, _, src_place) | Rvalue::RawPtr(_, src_place) => src_place
                        .projection
                        .iter()
                        .any(|p| {
                            matches!(
                                p.kind(),
                                rustc_middle::mir::ProjectionElem::Deref
                            )
                        }),
                    Rvalue::Use(operand, ..) => {
                        let is_projected = match operand {
                            Operand::Copy(p) | Operand::Move(p) => p.projection.iter().any(|e| {
                                matches!(e.kind(), rustc_middle::mir::ProjectionElem::Deref)
                            }),
                            _ => false,
                        };
                        dest_is_ptr || is_projected
                    }
                    Rvalue::CopyForDeref(p) => dest_is_ptr || !p.projection.is_empty(),
                    _ => false,
                }
            }
            _ => false,
        };

        // A statement that writes an iterator's `ptr` field (`(*self).0 = ...`,
        // the inlined `post_inc_start`) must be kept even when it is not
        // *value*-relevant to the property: the forward VM tracks the iterator's
        // cumulative offset from this write (`track_iter_ptr_update`), which is
        // what makes the loop-carried `i < n` invariant provable.
        let is_iter_ptr_write = match &statement.kind {
            StatementKind::Assign(assign) => {
                let (place, _) = &**assign;
                let mut proj = place.projection.iter();
                if !matches!(
                    proj.next().map(|p| p.kind()),
                    Some(rustc_middle::mir::ProjectionElem::Deref)
                ) {
                    false
                } else {
                    let is_field0 = matches!(
                        (proj.next().map(|p| p.kind()), proj.next()),
                        (Some(rustc_middle::mir::ProjectionElem::Field(f, _)), None)
                            if f.as_usize() == 0
                    );
                    if !is_field0 {
                        false
                    } else {
                        let base_ty = self.tcx.optimized_mir(def_id).local_decls[place.local].ty;
                        match base_ty.kind() {
                            rustc_middle::ty::TyKind::Ref(_, pointee, _) => {
                                match pointee.kind() {
                                    rustc_middle::ty::TyKind::Adt(adt_def, _) => {
                                        crate::verify::api_classify::is_std_iter_or_itermut(
                                            adt_def.did(),
                                        )
                                    }
                                    _ => false,
                                }
                            }
                            _ => false,
                        }
                    }
                }
            }
            _ => false,
        };

        // A write into a `[u8; N]`/`[u8]` buffer (e.g. `box [a, b, 0]`'s element
        // store `((*_8).1).0 = [a, b, 0]`) must be kept even when it is not
        // *value*-relevant to the property: the forward VM records these stores
        // as per-byte values, and `ValidCStr`/`ValidString` reason over them.
        // The backward def-use graph is place-level (it cannot follow the
        // `Box`/`Vec` → buffer indirection), so this structural keep is what
        // preserves the byte-level dataflow.
        let is_byte_write = match &statement.kind {
            StatementKind::Assign(assign) => {
                let (place, _) = &**assign;
                let ty = place.ty(self.tcx.optimized_mir(def_id), self.tcx).ty;
                mir_utils::is_u8_array_or_slice(ty)
            }
            _ => false,
        };

        let is_pointee_write = matches!(&statement.kind, StatementKind::Assign(assign) if
            assign.0.projection.first().is_some_and(|p|
                matches!(p.kind(), rustc_middle::mir::ProjectionElem::Deref)));

        if defs.intersects(relevant)
            || is_provenance_carrier
            || is_iter_ptr_write
            || is_byte_write
            || is_pointee_write
        {
            let mut uses = collect_statement_uses(statement, block, statement_index, flow, &defs);
            items.push(RelevantItem::Statement {
                def_id,
                block,
                statement_index,
            });
            // Save places already in the relevance set before removing
            // the current definition.  When the uses of this statement
            // would re-add a place whose definition was already found earlier
            // in the walk, skip it to prevent wrong (duplicate) matches.
            let already_seen: crate::compat::FxHashSet<crate::helpers::def_use::PlaceKey> =
                relevant.places.clone();
            let indexed_write = matches!(&statement.kind, StatementKind::Assign(assign) if
                assign.0.projection.iter().any(|p| matches!(p.kind(), rustc_middle::mir::ProjectionElem::Index(_))));
            if !indexed_write {
                relevant.remove_all(&defs);
            }
            uses.places.retain(|p| !already_seen.contains(p));
            relevant.extend(uses);
            return;
        }

        if statement_can_refine(statement) {
            let uses = collect_flow_uses(flow, block, statement_index, &defs);
            if uses.intersects(relevant) {
                items.push(RelevantItem::Statement {
                    def_id,
                    block,
                    statement_index,
                });
            }
        }
    }

}

// ── classification helpers ──────────────────────────────────────────────

fn statement_can_refine(statement: &rustc_middle::mir::Statement<'_>) -> bool {
    matches!(&statement.kind, StatementKind::Assign(assign) if matches!(
        &**assign,
        (
            _,
            rustc_middle::mir::Rvalue::BinaryOp(_, _)
            | rustc_middle::mir::Rvalue::UnaryOp(_, _)
            | rustc_middle::mir::Rvalue::Cast(_, _, _),
        )
    ))
}

/// Collect all place-uses for a statement from dataflow edges and operands.
fn collect_statement_uses<'tcx>(
    statement: &'tcx rustc_middle::mir::Statement<'tcx>,
    block: BasicBlock,
    statement_index: usize,
    flow: &DataflowGraph,
    defs: &RelevantPlaces,
) -> RelevantPlaces {
    let mut uses = collect_flow_uses(flow, block, statement_index, defs);

    // Also collect uses directly from operands — the dataflow graph
    // creates synthetic nodes for field projections (e.g. _13.0),
    // so we need the direct operand uses to reach through.
    if let StatementKind::Assign(assign) = &statement.kind {
        let (_, rvalue) = &**assign;
        for operand in crate::helpers::def_use::rvalue_operands(rvalue) {
            uses.extend(operand_uses(operand));
        }
        // A reborrow (`_p = &(*_q)`, `_p = &raw (*_q)`) carries no operands, so
        // `rvalue_operands` misses its referent.  Only when the referent traces
        // back to a projection out of a call's returned tuple (a `split_at`
        // prefix/suffix slice) do we keep the referent's base local, so the
        // split — and its `mid` argument — stays in the backward slice and
        // feeds downstream `len(self)` obligations.  This stays narrow to avoid
        // inflating relevance for ordinary reborrows, which explodes loop path
        // enumeration.
        if let rustc_middle::mir::Rvalue::Ref(_, _, place)
        | rustc_middle::mir::Rvalue::RawPtr(_, place) = rvalue
        {
            uses.insert_local(place.local);
        }
    }

    uses
}

/// Collect the source locals of the dataflow edges entering
/// `(block, statement_index)` from the def locals of `defs`.
fn collect_flow_uses(
    flow: &DataflowGraph,
    block: BasicBlock,
    statement_index: usize,
    defs: &RelevantPlaces,
) -> RelevantPlaces {
    let mut uses = RelevantPlaces::new();
    for &local in &defs.locals {
        for &edge_idx in &flow.node(local).in_edges {
            let edge = &flow.edges[edge_idx];
            if edge.block == block.as_usize() && edge.statement_index == statement_index {
                uses.insert_local(edge.src);
            }
        }
    }
    uses
}
