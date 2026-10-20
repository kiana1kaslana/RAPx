//! `Rvalue` interpretation rules: one `(match, eval)` pair per constructor.

use rustc_middle::mir::{BinOp, Place, Rvalue, UnOp};
use z3::ast::{Ast, Int};

use super::super::state::{ValueFacts, ValueSource, VmState, VmValue};

use crate::helpers::mir_utils;
use crate::verify::api_classify;


pub(crate) fn eval_use<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> Option<VmValue<'z3, 'tcx>> {
    let Rvalue::Use(operand, ..) = rvalue else {
        return None;
    };
    let mut val = state.value_of_operand(operand);
    if let rustc_middle::mir::Operand::Constant(c) = operand
        && place.projection.is_empty() {
            state.materialize_const_adt(place.local, &c.const_);
        }
    state.try_materialize_const_bytes(&mut val, operand);
    state.inject_layout_constraints(operand, &val);
    state.try_emit_gcd_divisibility(operand, &val);
    Some(val)
}


pub(crate) fn eval_ref<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> Option<VmValue<'z3, 'tcx>> {
    let Rvalue::Ref(_, _borrow_kind, place) = rvalue else {
        return None;
    };
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;
    if let Some(addr) = state.address_of_place(place) {
        let alloc_align = state.alloc_align_of(&addr);
        // Inherit in_bounds. For &[T] created via Deref of a fat raw ptr
        // (inlined from_raw_parts), set in_bounds like ReturnFreshAllocation does
        // in builtin_models.
        let has_deref = place
            .projection
            .iter()
            .any(|p| matches!(p.kind(), rustc_middle::mir::ProjectionElem::Deref));
        let src_ty = state.body().local_decls[place.local].ty;
        let is_from_raw_parts_like =
            matches!(src_ty.kind(), rustc_middle::ty::TyKind::RawPtr(_, _));
        let is_slice_ref = if let rustc_middle::ty::TyKind::Ref(_, inner, _) = dest_ty.kind() {
            matches!(inner.kind(), rustc_middle::ty::TyKind::Slice(_))
        } else {
            false
        };
        let is_slice_ref_from_raw = is_slice_ref && is_from_raw_parts_like && has_deref;
        let src_in_bounds = if is_slice_ref_from_raw {
            addr.is_pointer()
        } else {
            state
                .local_value(place.local)
                .is_some_and(|v| v.facts.in_bounds)
        };
        // An empty slice (`&[]` from `align_to`'s `offset > len` / ZST branch)
        // is built as `&*dangling`: the dangling raw pointer (`NonNull::dangling`)
        // is aligned to the *element* type, but its provenance here may reuse
        // `self`'s allocation (whose align is that of `T`).  Record the element
        // type's alignment so `check_align` can discharge it.
        let slice_elem_align = if is_slice_ref_from_raw {
            if let rustc_middle::ty::TyKind::Ref(_, inner, _) = dest_ty.kind() {
                if let rustc_middle::ty::TyKind::Slice(elem) = inner.kind() {
                    let a = state.align_sym(*elem);
                    if a.simplify().as_u64() != Some(1) {
                        Some(a)
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        };
        let val = VmValue {
            z3_term: addr.z3_term,
            ty: dest_ty,
            provenance: addr.provenance,
            facts: ValueFacts {
                non_null: true,
                init: true,
                in_bounds: src_in_bounds,
                align_n: slice_elem_align.or(alloc_align),
            },
            source: ValueSource::None,
        };
        state.propagate_byte_values_to_ref(place, &val);
        state.propagate_field_values_to_ref(place, dest_place.local);
        // Expose the freshly-created reference's provenance before asserting
        // the pointee struct's `#[rapx::invariant]`s: the invariant predicates
        // (`ValidNum(len <= CAPACITY)` on `&LeafNode`) resolve their field
        // places through the pointee allocation, which needs `dest_place`'s
        // provenance to be live (`exec_assign` only stores `val` afterwards).
        state.set_local(dest_place.local, val.clone());
        state.assert_pointee_struct_invariants(dest_ty, dest_place.local);
        Some(val)
    } else {
        let term = state.fresh_int("ref_addr");
        Some(VmValue {
            z3_term: term,
            ty: dest_ty,
            provenance: None,
            facts: ValueFacts {
                non_null: true,
                init: true,
                ..Default::default()
            },
            source: ValueSource::None,
        })
    }
}


pub(crate) fn eval_raw_ptr<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> Option<VmValue<'z3, 'tcx>> {
    let Rvalue::RawPtr(_, place) = rvalue else {
        return None;
    };
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;
    if let Some(addr) = state.address_of_place(place) {
        let alloc_align = state.alloc_align_of(&addr);
        let source_in_bounds = state
            .local_value(place.local)
            .is_some_and(|v| v.facts.in_bounds);
        Some(VmValue {
            z3_term: addr.z3_term,
            ty: dest_ty,
            provenance: addr.provenance,
            facts: ValueFacts {
                non_null: true,
                in_bounds: source_in_bounds,
                align_n: alloc_align,
                ..Default::default()
            },
            source: ValueSource::None,
        })
    } else {
        let term = state.fresh_int("rawptr_addr");
        Some(VmValue {
            z3_term: term,
            ty: dest_ty,
            provenance: None,
            facts: ValueFacts {
                non_null: true,
                ..Default::default()
            },
            source: ValueSource::None,
        })
    }
}


pub(crate) fn eval_binary_op<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> Option<VmValue<'z3, 'tcx>> {
    let Rvalue::BinaryOp(op, pair) = rvalue else {
        return None;
    };
    let op = *op;
    let (lhs_op, rhs_op) = &**pair;
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;

    let lhs = state.value_of_operand(lhs_op);
    let rhs = state.value_of_operand(rhs_op);
    let term = state.eval_binary_op(op, &lhs.z3_term, &rhs.z3_term);
    let provenance = state.provenance_for_binary_op(op, &lhs, &rhs);
    let invariants = state.facts_for_binary_op(op, &lhs, &rhs, &provenance);
    let lhs_pk = mir_utils::operand_place(lhs_op);
    let rhs_pk = mir_utils::operand_place(rhs_op);
    // Carry the direct boolean condition alongside the ite-encoded result so
    // `switchInt`/`Assert` can record a precise path condition (e.g.
    // `offset <= len - 16`) instead of `ite(cond, 1, 0) != 0`, which the SMT
    // solver often fails to unfold.
    let cmp_cond = state
        .iter_ptr_comparison(op, &lhs, &rhs)
        .or_else(|| match op {
            BinOp::Le => Some(lhs.z3_term.le(&rhs.z3_term)),
            BinOp::Lt => Some(lhs.z3_term.lt(&rhs.z3_term)),
            BinOp::Ge => Some(lhs.z3_term.ge(&rhs.z3_term)),
            BinOp::Gt => Some(lhs.z3_term.gt(&rhs.z3_term)),
            BinOp::Eq => Some(lhs.z3_term._eq(&rhs.z3_term)),
            BinOp::Ne => Some(lhs.z3_term._eq(&rhs.z3_term).not()),
            _ => None,
        });
    if matches!(op, BinOp::Div | BinOp::Rem) {
        state.emit_div_rem_axioms(op, &term, &lhs.z3_term, &rhs.z3_term);
    }
    // For tuple-returning binary ops (AddWithOverflow, MulWithOverflow),
    // populate the field values so that .0 (result) and .1 (overflow flag)
    // are properly tracked. Without this, field access falls through to
    // cloning the base term, mixing the arithmetic result with the boolean
    // overflow flag and corrupting path conditions.
    if let rustc_middle::ty::TyKind::Tuple(fields) = dest_ty.kind()
        && fields.len() == 2
    {
        let result_val = VmValue {
            z3_term: term.clone(),
            ty: fields[0],
            provenance: provenance.clone(),
            facts: invariants.clone(),
            source: ValueSource::None,
        };
        state.set_field_value(dest_place.local, vec![0], result_val);
        let overflow_term = state.fresh_int("overflow_flag");
        let overflow_val = VmValue::new(overflow_term, fields[1]);
        state.set_field_value(dest_place.local, vec![1], overflow_val);
    }
    Some(VmValue {
        z3_term: term,
        ty: dest_ty,
        provenance,
        facts: invariants,
        source: match cmp_cond {
            Some(cond) => ValueSource::Comparison {
                lhs: lhs_pk,
                rhs: rhs_pk,
                op,
                cond,
            },
            None => ValueSource::BinaryOp {
                lhs: lhs_pk,
                rhs: rhs_pk,
                op,
            },
        },
    })
}


pub(crate) fn eval_unary_op<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> Option<VmValue<'z3, 'tcx>> {
    let Rvalue::UnaryOp(op, operand) = rvalue else {
        return None;
    };
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;
    let val = state.value_of_operand(operand);
    let is_bool = matches!(val.ty.kind(), rustc_middle::ty::TyKind::Bool);
    let term = if matches!(op, UnOp::PtrMetadata) {
        // `PtrMetadata` on a `&[T]` gives the slice length, which is the
        // allocation size divided by the element size. Reuse the same symbolic
        // term as the allocation size so downstream InBound checks
        // (`offset <= len`) agree with the `len` used in loop guards
        // (`offset <= len - 16`).
        state
            .slice_len_from_value(&val)
            .unwrap_or_else(|| state.fresh_int("ptr_metadata"))
    } else {
        state.eval_unary_op(*op, &val.z3_term, is_bool)
    };
    Some(VmValue {
        z3_term: term,
        ty: dest_ty,
        provenance: val.provenance,
        facts: val.facts,
        source: ValueSource::None,
    })
}


pub(crate) fn eval_cast<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    _dest_place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> Option<VmValue<'z3, 'tcx>> {
    let Rvalue::Cast(_kind, operand, cast_ty) = rvalue else {
        return None;
    };
    let src_val = state.value_of_operand(operand);
    let src_ty = src_val.ty;
    // A raw-pointer cast to a *different* ADT pointee reinterprets the
    // allocation's fields (e.g. `NonNull<LeafNode>::as_ptr() as *mut
    // InternalNode` in `NodeRef::as_internal_ptr`).  Lazily materialize the
    // target ADT's field view (keyed by type) so a later `(*cast_ptr).field`
    // resolves to the right field instead of the original view's field at the
    // same index.
    if let rustc_middle::ty::TyKind::RawPtr(target_ty, _) = cast_ty.kind()
        && let rustc_middle::ty::TyKind::Adt(adt_def, _) = target_ty.kind()
        && adt_def.is_struct()
        && let Some(alloc_id) = src_val.provenance_alloc_id()
    {
        state.decompose_pointee_fields(alloc_id, Vec::new(), *target_ty, *target_ty, 0, 0, 0);
    }
    // Transmute-like casts of single-field newtypes (e.g. NonZero::get's
    // `_0 = copy _1 as T`) yield the underlying field value, not the wrapper's
    // own term.
    let term = mir_utils::extract_local(operand)
        .and_then(|l| state.field_value(l, &[0]).map(|v| v.z3_term.clone()))
        .unwrap_or(src_val.z3_term);
    // A pointer→integer cast (`ptr as usize`) yields the (always non-negative)
    // address. Record this as a *path condition* so downstream pointer
    // arithmetic (e.g. `align_up` in a free-list allocator) can discharge
    // `NonNull` on the derived pointer — `check_non_null`'s SMT query only sees
    // path conditions, not the `term >= 0` constraint `assert_value_constraints`
    // adds.
    let src_is_ptr = matches!(
        src_ty.kind(),
        rustc_middle::ty::TyKind::RawPtr(..) | rustc_middle::ty::TyKind::Ref(..)
    );
    let dest_is_int = matches!(
        cast_ty.kind(),
        rustc_middle::ty::TyKind::Uint(_) | rustc_middle::ty::TyKind::Int(_)
    );
    if src_is_ptr && dest_is_int {
        let zero = Int::from_u64(state.z3_ctx, 0);
        state.constraints.assertions.push(term.ge(&zero));
        if src_val.facts.non_null {
            state.constraints.assertions.push(term._eq(&zero).not());
        }
    }
    Some(VmValue {
        z3_term: term,
        ty: *cast_ty,
        provenance: src_val.provenance,
        facts: ValueFacts {
            non_null: src_val.facts.non_null,
            init: src_val.facts.init,
            in_bounds: src_val.facts.in_bounds,
            align_n: if mir_utils::pointee_ty(src_ty).is_some_and(|t| t.is_unit()) {
                None
            } else {
                src_val.facts.align_n
            },
        },
        source: src_val.source.field_offset_only(),
    })
}


pub(crate) fn eval_aggregate<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> Option<VmValue<'z3, 'tcx>> {
    let Rvalue::Aggregate(kind, operands) = rvalue else {
        return None;
    };
    let kind = &**kind;
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;

    // For an enum aggregate, remember whether this is the data-carrying variant
    // of `Option`/`Result` (`Some`/`Ok`), so the nested-field flattening below
    // only fires on paths that actually carry a `Self`.
    let data_variant = match kind {
        rustc_middle::mir::AggregateKind::Adt(did, variant_idx, ..) => {
            if state.tcx.is_diagnostic_item(rustc_span::sym::Result, *did) {
                Some(variant_idx.as_usize() == 0)
            } else if state.tcx.is_diagnostic_item(rustc_span::sym::Option, *did) {
                Some(variant_idx.as_usize() == 1)
            } else {
                None
            }
        }
        _ => None,
    };
    // `NonNull::new_unchecked(ptr)` / `NonNull::from(&T)` construct a
    // repr(transparent) single-field newtype whose value *is* the underlying
    // pointer.  Model the wrapper as the pointer field itself (term + provenance
    // + invariants) so downstream checks like `NonNull(node)` / `Align(node, T)`
    // / `Allocated(node, ..)` can discharge against the real pointer instead of
    // a fresh unconstrained `aggregate` symbol.  The same transparent modelling
    // applies to value newtypes (`MaybeUninit<T>`, `ManuallyDrop<T>`) so that
    // `MaybeUninit::new(x).assume_init()` round-trips back to `x`.
    if operands.len() == 1
        && (state.find_nn_pointee(dest_ty).is_some() || state.is_transparent_newtype(dest_ty))
    {
        let field_val = state.value_of_operand(operands.iter().next().unwrap());
        let dest_local = dest_place.local;
        state.set_field_value(dest_local, vec![0], field_val.clone());
        if let Some(alloc_id) = state.current_frame.local_alloc.get(&dest_local).copied() {
            state.content_mut(alloc_id).facts.initialized = true;
        }
        return Some(VmValue {
            z3_term: field_val.z3_term,
            ty: dest_ty,
            provenance: field_val.provenance,
            facts: field_val.facts,
            source: ValueSource::None,
        });
    }
    let term = state.fresh_int("aggregate");
    let dest_local = dest_place.local;
    // Prefer the pointee allocation (through a `*ptr` deref) over the base
    // local's own stack slot, so byte values land on the real buffer (e.g.
    // `((*_8).1).0 = [a, b, 0]` writes into the box).
    let dest_alloc_id = state
        .local_value(dest_local)
        .and_then(|v| v.provenance_alloc_id())
        .or_else(|| state.current_frame.local_alloc.get(&dest_local).copied());
    let is_byte_array = mir_utils::is_u8_array_or_slice(dest_ty);
    let field_types: Vec<_> = state.aggregate_field_tys(dest_ty);
    let mut byte_offset = 0usize;
    for (i, operand) in operands.iter().enumerate() {
        let mut field_val = state.value_of_operand(operand);
        let field_ty_opt = field_types.get(i).copied();
        if let Some(field_ty) = field_ty_opt {
            let src_is_ref = matches!(field_val.ty.kind(), rustc_middle::ty::TyKind::Ref(..));
            let dst_is_raw = matches!(field_ty.kind(), rustc_middle::ty::TyKind::RawPtr(..));
            if dst_is_raw && (src_is_ref || field_val.facts.non_null) {
                field_val.facts.in_bounds = true;
                field_val.ty = field_ty;
            }
        }
        let field_sz = field_ty_opt
            .map(|ty| state.size_of_ty(ty) as usize)
            .unwrap_or(1);
        let field_term = field_val.z3_term.clone();
        state.set_field_value(dest_local, vec![i], field_val);
        // Flatten a nested aggregate: if the operand is a local whose own fields
        // are tracked (e.g. `_0 = Result::Ok(_24)` where `_24 = RawVecInner { ptr:
        // _25, .. }`), expose the nested fields under the destination's field
        // path so a contract place like `Return.Field(0).Field(0)` can resolve to
        // `_25`.  Only flatten the data-carrying variant (`Ok`/`Some`); on
        // `Err`/`None` paths there is no `Self` and the nested place should
        // resolve to `Unknown`.
        if data_variant != Some(false)
            && let Some(op_place) = operand.place()
            && op_place.projection.is_empty()
        {
            let nested: Vec<(Vec<usize>, VmValue<'z3, 'tcx>)> = state
                .field_paths(op_place.local)
                .into_iter()
                .filter_map(|p| {
                    state
                        .field_value(op_place.local, &p)
                        .cloned()
                        .map(|v| (p, v))
                })
                .collect();
            for (nested_path, nested_val) in nested {
                let mut full = vec![i];
                full.extend_from_slice(&nested_path);
                state.set_field_value(dest_local, full, nested_val);
            }
        }
        if let Some(alloc_id) = dest_alloc_id {
            state.content_mut(alloc_id).facts.initialized = true;
            if is_byte_array && field_sz == 1 {
                state.record_byte_value(alloc_id, byte_offset, field_term.clone());
            }
            // Record known_nul / known_non_nul from constant operands
            if let Some(int_val) = mir_utils::operand_const_u64(operand) {
                if field_sz == 1 {
                    if int_val == 0 {
                        if !is_byte_array {
                            state.record_byte_value(
                                alloc_id,
                                byte_offset,
                                Int::from_u64(state.z3_ctx, 0),
                            );
                        }
                    } else if !is_byte_array {
                        state.record_byte_value(
                            alloc_id,
                            byte_offset,
                            Int::from_u64(state.z3_ctx, int_val),
                        );
                    }
                }
                // For multi-byte fields: track each constituent byte
                for b in 0..field_sz.min(8) {
                    let byte_off = byte_offset + b;
                    let byte_val = (int_val >> (b * 8)) & 0xFF;
                    state.record_byte_value(
                        alloc_id,
                        byte_off,
                        Int::from_u64(state.z3_ctx, byte_val),
                    );
                }
            }
        }
        byte_offset += field_sz;
    }
    // Fat-pointer construction (inlined `from_raw_parts` /
    // `slice_from_raw_parts_mut`): the result's address and provenance are those
    // of the data pointer (field 0), so downstream `Allocated`/`Owning` checks
    // on the slice resolve against the real buffer instead of a fresh `aggregate`
    // symbol.
    let is_slice_ptr = matches!(dest_ty.kind(),
        rustc_middle::ty::TyKind::RawPtr(inner, _) | rustc_middle::ty::TyKind::Ref(_, inner, _)
            if matches!(inner.kind(), rustc_middle::ty::TyKind::Slice(_)));
    let (result_term, result_prov) = if is_slice_ptr {
        match state.field_value(dest_local, &[0]).cloned() {
            Some(data) => (data.z3_term.clone(), data.provenance.clone()),
            None => (term.clone(), None),
        }
    } else {
        // `Box<T>` (an aggregate `Box(Unique<T>, A)`) takes its provenance from
        // the inner `Unique<T>.pointer` (`NonNull<T>` at path `[0, 0]`), which
        // the field-flattening above just recorded.  Without this,
        // `Box::assume_init`'s rebuild drops the heap provenance and a later
        // `Box::as_ptr` field read fails `NonNull`.
        let box_prov = if let rustc_middle::ty::TyKind::Adt(adt, _) = dest_ty.kind() {
            if api_classify::is_std_box(adt.did()) {
                state
                    .container_ptr_field(dest_ty)
                    .and_then(|path| state.field_value(dest_local, &path))
                    .and_then(|v| v.provenance.clone())
            } else {
                None
            }
        } else {
            None
        };
        (term.clone(), box_prov)
    };
    Some(VmValue {
        z3_term: result_term,
        ty: dest_ty,
        provenance: result_prov,
        facts: ValueFacts::default(),
        source: ValueSource::None,
    })
}


pub(crate) fn eval_discriminant<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> Option<VmValue<'z3, 'tcx>> {
    let Rvalue::Discriminant(place) = rvalue else {
        return None;
    };
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;
    // If the ADT's variant is known symbolically (e.g. `Iterator::next` returns
    // `Some` iff the iterator was non-empty), reuse that term so
    // `switchInt(discriminant)` branches stay tied to the real condition instead
    // of a fresh unconstrained symbol.
    let place_val = state
        .value_of_place(place)
        .or_else(|| state.local_value(place.local).cloned());
    let term = place_val
        .as_ref()
        .and_then(|v| v.discriminant().cloned())
        .unwrap_or_else(|| state.fresh_int("discriminant"));
    // For Ordering (repr i8, values: Less=-1 Equal=0 Greater=1), the
    // discriminant index equals the repr value + 1.  Connect the fresh
    // discriminant term to the ADT value so that SwitchInt constraints propagate
    // to the stored value.
    if let Some(ref pv) = place_val
        && let rustc_middle::ty::TyKind::Adt(adt_def, _) = pv.ty.kind()
        && api_classify::is_std_ordering(adt_def.did())
        && adt_def.is_enum()
    {
        let one = Int::from_u64(state.z3_ctx, 1);
        let discr_minus_one = Int::sub(state.z3_ctx, &[&term, &one]);
        state
            .constraints
            .assertions
            .push(pv.z3_term._eq(&discr_minus_one));
        // Also bound the discriminant to {0, 1, 2}
        let zero = Int::from_u64(state.z3_ctx, 0);
        let two = Int::from_u64(state.z3_ctx, 2);
        state.constraints.assertions.push(term.ge(&zero));
        state.constraints.assertions.push(term.le(&two));
    }
    Some(VmValue::new(term, dest_ty))
}

#[cfg(not(rapx_ge_99))]
pub(crate) fn eval_shallow_init_box<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> Option<VmValue<'z3, 'tcx>> {
    let Rvalue::ShallowInitBox(operand, _ty) = rvalue else {
        return None;
    };
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;
    let val = state.value_of_operand(operand);
    Some(VmValue {
        z3_term: val.z3_term,
        ty: dest_ty,
        provenance: val.provenance,
        facts: val.facts,
        source: ValueSource::None,
    })
}


pub(crate) fn eval_copy_for_deref<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> Option<VmValue<'z3, 'tcx>> {
    let Rvalue::CopyForDeref(place) = rvalue else {
        return None;
    };
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;
    if let Some(val) = state.value_of_place(place) {
        Some(val)
    } else {
        let term = state.fresh_int("copy_for_deref");
        Some(VmValue::new(term, dest_ty))
    }
}


pub(crate) fn eval_repeat<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> Option<VmValue<'z3, 'tcx>> {
    let Rvalue::Repeat(..) = rvalue else {
        return None;
    };
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;
    let term = state.fresh_int("repeat");
    Some(VmValue::new(term, dest_ty))
}


pub(crate) fn eval_thread_local_ref<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> Option<VmValue<'z3, 'tcx>> {
    let Rvalue::ThreadLocalRef(..) = rvalue else {
        return None;
    };
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;
    let term = state.fresh_int("thread_local");
    Some(VmValue::new(term, dest_ty))
}

#[cfg(not(rapx_ge_95))]
pub(crate) fn eval_nullary_op<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> Option<VmValue<'z3, 'tcx>> {
    let Rvalue::NullaryOp(op) = rvalue else {
        return None;
    };
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;
    let term = state.fresh_int("nullary");
    let op_debug = format!("{:?}", op);
    let is_align_of = op_debug.contains("AlignOf") || op_debug.contains("min_align_of");
    let is_size_of = op_debug.contains("SizeOf");
    if is_align_of || is_size_of {
        let one = Int::from_u64(state.z3_ctx, 1);
        state.constraints.assertions.push(term.ge(&one));
    }
    Some(VmValue::new(term, dest_ty))
}


pub(crate) fn eval_wrap_unsafe_binder<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> Option<VmValue<'z3, 'tcx>> {
    let Rvalue::WrapUnsafeBinder(..) = rvalue else {
        return None;
    };
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;
    let term = state.fresh_int("wrap_unsafe_binder");
    Some(VmValue::new(term, dest_ty))
}

#[cfg(rapx_rvalue_has_reborrow)]
pub(crate) fn eval_reborrow<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    dest_place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> Option<VmValue<'z3, 'tcx>> {
    let Rvalue::Reborrow(..) = rvalue else {
        return None;
    };
    let dest_ty = dest_place.ty(state.body(), state.tcx).ty;
    let term = state.fresh_int("reborrow");
    Some(VmValue {
        z3_term: term,
        ty: dest_ty,
        provenance: None,
        facts: ValueFacts {
            non_null: true,
            ..Default::default()
        },
        source: ValueSource::None,
    })
}
