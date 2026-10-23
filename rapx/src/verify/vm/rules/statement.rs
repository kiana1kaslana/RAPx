//! Transfer functions for state-changing MIR statements.

use rustc_middle::mir::{Local, Operand, Place, ProjectionElem, Rvalue};
use z3::ast::{Ast, Int};

use super::super::state::{Provenance, VmState, VmValue};
use crate::helpers::mir_utils;
use super::eval_rvalue;

pub(crate) fn exec_assign<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) {
    let source_place = match rvalue {
        Rvalue::Use(Operand::Copy(source) | Operand::Move(source), ..)
        | Rvalue::CopyForDeref(source) => Some(source),
        _ => None,
    };
    let uninit_source = source_place
        .and_then(|source| state.current_frame.local_alloc.get(&source.local))
        .is_some_and(|id| state.possible_uninit_allocs.contains(id));
    let mut value = eval_rvalue(state, place, rvalue);

    let has_deref = place
        .projection
        .iter()
        .any(|p| matches!(p.kind(), ProjectionElem::Deref));

    if !place.projection.is_empty() {
        state.record_projected_store(place, &value);
        state.record_indexed_store(place, &value);
    }
    value.facts.init = true;

    if place.projection.is_empty() {
        state.set_local(place.local, value);
        if uninit_source
            && let Some(id) = state.current_frame.local_alloc.get(&place.local)
        {
            state.possible_uninit_allocs.insert(*id);
        }
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
        if let Some(sp) = source_place {
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

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    /// Record byte-level values when assigning to a place with projections.
    /// This handles patterns like `buf[i] = 0u8` (nul-store) and `arr[i] = val`.
    fn record_projected_store(&mut self, place: &Place<'tcx>, value: &VmValue<'z3, 'tcx>) {
        // Prefer the value's provenance (pointee alloc) over slots
        // (reference alloc) for ref/ptr parameters.
        let Some(alloc_id) = self
            .local_value(place.local)
            .and_then(|v| v.provenance_alloc_id())
            .or_else(|| self.current_frame.local_alloc.get(&place.local).copied())
        else {
            return;
        };

        let value_ty = value.ty;
        let value_size = self.size_of_ty(value_ty) as usize;

        let mut byte_offset: usize = 0;
        let mut concrete = true;

        let base_ty = self.body().local_decls[place.local].ty;
        let mut cur_ty = base_ty;

        for proj in place.projection.iter() {
            match proj.kind() {
                rustc_middle::mir::ProjectionElem::Field(field_idx, _) => {
                    let off = self.field_offset_in_bytes(cur_ty, field_idx.as_usize()) as usize;
                    byte_offset += off;
                    if let rustc_middle::ty::TyKind::Adt(adt_def, substs) = cur_ty.kind()
                        && !adt_def.is_enum() {
                            let variant = adt_def.non_enum_variant();
                            if let Some(field_def) = variant.fields.get(field_idx) {
                                cur_ty = mir_utils::field_ty(
                                    self.tcx, field_def, substs,
                                );
                            }
                        }
                }
                rustc_middle::mir::ProjectionElem::Deref => {
                    if let rustc_middle::ty::TyKind::Ref(_, inner, _) = cur_ty.kind() {
                        cur_ty = *inner;
                    }
                }
                rustc_middle::mir::ProjectionElem::Index(_local) => {
                    concrete = false;
                    break;
                }
                rustc_middle::mir::ProjectionElem::Subslice {
                    from,
                    to: _,
                    from_end: _,
                } => {
                    byte_offset += from as usize;
                }
                _ => {}
            }
        }

        if concrete && value_size > 0 {
            self.content_mut(alloc_id).facts.initialized = true;

            let is_u8_write = matches!(
                value_ty.kind(),
                rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::U8)
            );

            if is_u8_write {
                self.record_byte_value(alloc_id, byte_offset, value.z3_term.clone());
            }
        }
    }

    /// Track byte-level values for index-based stores (e.g. `buf[i] = 0u8`)
    /// that `record_projected_store` skips due to Index projections.
    fn record_indexed_store(
        &mut self,
        place: &Place<'tcx>,
        value: &VmValue<'z3, 'tcx>,
    ) {
        if place.projection.len() == 1
            && let rustc_middle::mir::ProjectionElem::Index(index_local) = place.projection[0]
            && let rustc_middle::ty::TyKind::Array(elem_ty, _) =
                self.body().local_decls[place.local].ty.kind()
            && *elem_ty == value.ty
        {
            let array_ty = self.body().local_decls[place.local].ty;
            let index = self
                .local_value(index_local)
                .and_then(|v| v.z3_term.simplify().as_u64())
                .and_then(|v| usize::try_from(v).ok());
            if let Some(index) = index {
                if let Some(alloc_id) = self.current_frame.local_alloc.get(&place.local).copied() {
                    self.content_mut(alloc_id).values.retain(|(ty, path), _| {
                        *ty != array_ty || path.first() != Some(&index)
                    });
                }
                if matches!(
                    value.ty.kind(),
                    rustc_middle::ty::TyKind::Int(_)
                        | rustc_middle::ty::TyKind::Uint(_)
                        | rustc_middle::ty::TyKind::Bool
                        | rustc_middle::ty::TyKind::Char
                ) {
                    self.set_field_value(place.local, vec![index], value.clone());
                }
            } else if let Some(alloc_id) = self
                .local_value(place.local)
                .and_then(|v| v.provenance_alloc_id())
                .or_else(|| self.current_frame.local_alloc.get(&place.local).copied())
            {
                self.content_mut(alloc_id)
                    .values
                    .retain(|(ty, path), _| *ty != array_ty || path.is_empty());
            }
        }
        let is_u8 = matches!(
            value.ty.kind(),
            rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::U8)
        );
        if !is_u8 {
            return;
        }
        let has_index_with_concrete = place.projection.iter().any(|p| {
            if let rustc_middle::mir::ProjectionElem::Index(local) = p {
                self.local_value(local)
                    .and_then(|v| v.z3_term.simplify().as_u64())
                    .is_some()
            } else {
                false
            }
        });
        if !has_index_with_concrete {
            return;
        }
        if let Some(addr) = self.address_of_place(place)
            && let Some(ref prov) = addr.provenance {
                let alloc_id = prov.alloc_id;
                let byte_offset = prov.offset.as_u64().map(|v| v as usize).unwrap_or(0);
                self.content_mut(alloc_id).facts.initialized = true;
                self.record_byte_value(alloc_id, byte_offset, value.z3_term.clone());
            }
    }

}
