//! Transfer functions for state-changing MIR statements.

use rustc_middle::mir::{Local, Operand, Place, ProjectionElem, Rvalue};
use z3::ast::Int;

use super::super::state::{Provenance, VmState};
use super::eval_rvalue;

pub(crate) fn exec_assign<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) {
    let mut value = eval_rvalue(state, place, rvalue);

    let has_deref = place
        .projection
        .iter()
        .any(|p| matches!(p.kind(), ProjectionElem::Deref));

    if !place.projection.is_empty() {
        state.record_projected_store(place, &value);
        state.record_indexed_store_for_vm(place, &value);
    }
    value.facts.init = true;

    if place.projection.is_empty() {
        state.set_local(place.local, value);
        // On a whole-place move (`_3 = move _4`), the destination is a fresh
        // container slot: re-point its whole-value provenance from the source's
        // stack slot to its own, so `container_data_alloc` later reads the
        // destination's owning field (copied below) rather than the moved-out
        // source's (which is invalidated after the propagation).
        let moved_from = match rvalue {
            Rvalue::Use(operand, ..) => match operand {
                Operand::Move(p) if p.projection.is_empty() => Some(p.local),
                _ => None,
            },
            _ => None,
        };
        if let Some(src) = moved_from
            && let Some(&src_alloc) = state.current_frame.local_alloc.get(&src)
            && let Some(mut wv) = state.local_value(place.local).cloned()
            && wv
                .provenance
                .as_ref()
                .is_some_and(|p| p.alloc_id == src_alloc)
        {
            let dest_alloc = state.current_frame.local_alloc[&place.local];
            wv.provenance = Some(Provenance {
                alloc_id: dest_alloc,
                offset: Int::from_u64(state.z3_ctx, 0),
                offset_kind: None,
            });
            state.set_local(place.local, wv);
        }
        // Propagate field values for aggregate copies (e.g. `_4 = copy _1`) so
        // downstream field accesses (NonZero::get -> self.0) resolve to the same
        // symbolic field terms.  A projected source (`_11 = move (_1.2)`) shifts
        // the field path by its `Field` projection prefix, so `(_1.2).1` becomes
        // `_11.1` — this keeps the `NonNull` node field's provenance alive across
        // `NodeRef` moves.
        let src_place: Option<&Place<'tcx>> = match rvalue {
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p), ..) => Some(p),
            Rvalue::CopyForDeref(p) => Some(p),
            _ => None,
        };
        if let Some(sp) = src_place {
            let field_prefix: Vec<usize> = sp
                .projection
                .iter()
                .filter_map(|p| match p.kind() {
                    ProjectionElem::Field(fi, _) => Some(fi.as_usize()),
                    _ => None,
                })
                .collect();
            // Also propagate for a leading `Deref` (`_3 = copy (*_1)`): the
            // source is the pointee of a reference, whose per-field values are
            // keyed by the reference local itself, so copying the pointee value
            // into a fresh local must carry those field values along (otherwise
            // `into_leaf(self)`'s `self.node` provenance is lost).
            let only_field_deref = sp
                .projection
                .iter()
                .all(|p| matches!(p.kind(), ProjectionElem::Field(..) | ProjectionElem::Deref));
            if only_field_deref {
                let keys: Vec<Vec<usize>> = state.field_paths(sp.local);
                for k in keys {
                    let rest = if field_prefix.is_empty() {
                        Some(k.clone())
                    } else if k.len() > field_prefix.len()
                        && k[..field_prefix.len()] == field_prefix[..]
                    {
                        Some(k[field_prefix.len()..].to_vec())
                    } else {
                        None
                    };
                    if let Some(rest) = rest
                        && let Some(fv) = state.field_value(sp.local, &k).cloned()
                    {
                        state.set_field_value(place.local, rest, fv);
                    }
                }
            }
        }
        // Invalidate the moved-out source's owner-field provenance *after* the
        // field propagation, so a later `Owning` check does not treat the source
        // as a second owner while the destination kept the pointer.
        if let Some(src) = moved_from {
            state.invalidate_owner_field(src);
        }
    } else if !has_deref {
        // Field projection (no Deref): update the base local's field values.
        let field_indices: Vec<usize> = place
            .projection
            .iter()
            .filter_map(|p| match p.kind() {
                ProjectionElem::Field(idx, _) => Some(idx.as_usize()),
                _ => None,
            })
            .collect();
        if !field_indices.is_empty() {
            // Track cumulative ptr offset for Iter/IterMut before moving value.
            let track_iter = field_indices == [0];
            state.set_field_value(place.local, field_indices, value);
            if track_iter {
                state.track_iter_ptr_update(place.local);
            }
        }
    } else {
        // Deref projection (`(*ptr).field = val`): resolve the referent local and
        // write the field there, so `&mut self` setters (`set_len`, `clear`, …)
        // actually update the referent's materialized fields instead of being
        // silently dropped.
        //
        // A pure `*ptr = val` (no trailing Field) still must NOT overwrite the
        // pointer local — writing through a pointer should not reassign the
        // pointer variable.
        let mut proj = place.projection.iter();
        if matches!(proj.next().map(|p| p.kind()), Some(ProjectionElem::Deref)) {
            let field_indices: Vec<usize> = proj
                .filter_map(|p| match p.kind() {
                    ProjectionElem::Field(idx, _) => Some(idx.as_usize()),
                    _ => None,
                })
                .collect();
            if field_indices.is_empty() {
                let pointed = state.local_value(place.local).cloned();
                if let Some(pointed) = pointed {
                    state.write_through_pointer(&pointed, Vec::new(), value);
                }
                return;
            } else {
                // `&mut self` (and other reference parameters) materialize their
                // pointee's scalar fields keyed by the *reference* local itself,
                // so a `(*self).field = val` write must land in the reference
                // local's own field values directly.  (This is what makes a
                // struct-invariant re-proof see `self.len += 1`.)
                if state.field_value(place.local, &field_indices).is_some() {
                    let is_iter_field = field_indices == [0];
                    state.set_field_value(place.local, field_indices, value);
                    if is_iter_field {
                        state.track_iter_ptr_update(place.local);
                    }
                    return;
                }
                // Otherwise resolve the dereferenced pointer (a reference/reborrow
                // temp) back to the local it points at, matching its address term
                // against the known local addresses.
                let pointed = state.local_value(place.local).cloned();
                if let Some(pointed) = pointed {
                    state.write_through_pointer(&pointed, field_indices, value);
                }
            }
        }
    }
}

pub(crate) fn exec_storage_live<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    local: Local,
) {
    state.ensure_local_allocation(local);
    let alloc_id = state.current_frame.local_alloc[&local];
    state.alloc_mut(alloc_id).facts.dead = false;
}

pub(crate) fn exec_storage_dead<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    local: Local,
) {
    if let Some(alloc_id) = state.current_frame.local_alloc.get(&local).copied() {
        state.alloc_mut(alloc_id).facts.dead = true;
    }
}
