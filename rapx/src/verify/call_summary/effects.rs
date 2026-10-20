//! Hand-written effect models for standard-library APIs: a matcher + effect
//! builder per API, looked up by [`lookup_effect`].

use crate::helpers::mir_utils;
#[cfg(rapx_has_attr_ir)]
use rustc_attr_ir::LangItem;
#[cfg(all(not(rapx_has_attr_ir), not(rapx_ge_100)))]
use rustc_hir::LangItem;
#[cfg(all(not(rapx_has_attr_ir), rapx_ge_100))]
use rustc_hir::attrs::lang_items::LangItem;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{Local, Operand};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};

use super::{CallEffect, CallEffectSummary};
use crate::def_id;
use crate::helpers::mir_utils::{destination_stride, pointee_alignment, pointee_ty, type_layout};
use crate::verify::api_classify;

// ── Context for effect builders ────────────────────────────────────────

pub(crate) struct EffCtx<'a, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub caller: DefId,
    pub func: &'a Operand<'tcx>,
    pub dest: Option<rustc_middle::mir::Local>,
}

// ── Registry table ─────────────────────────────────────────────────────

struct Entry {
    matches: fn(Option<DefId>) -> bool,
    effects: fn(&EffCtx<'_, '_>) -> Vec<CallEffect>,
    /// Whether the path graph keeps this call opaque (does not inline its CFG).
    /// `true` when the VM's effect is strictly more precise than the inlined
    /// body; `false` for hand-specialized shapes that still need their body
    /// inlined by the path graph to carry loop/range bounds into downstream
    /// checkpoints.
    opaque: bool,
}

/// `DefId`-based matcher row (`fn(Option<DefId>) -> bool`), opaque to the path
/// graph (the VM's effect replaces the inlined body).
macro_rules! ED {
    ($m:expr, $e:ident) => {
        Entry {
            matches: $m,
            effects: $e,
            opaque: true,
        }
    };
}

/// Matcher row whose body the path graph still inlines (the VM's effect only
/// handles execution-time semantics; the inlined CFG carries the bounds).
macro_rules! ED_INLINE {
    ($m:expr, $e:ident) => {
        Entry {
            matches: $m,
            effects: $e,
            opaque: false,
        }
    };
}

static REGISTRY: &[Entry] = &[
    // ── Hand-specialized VM shapes (opaque: false) ──────────────────
    // Listed first so they win over the generic def-path matchers below.
    ED_INLINE!(api_classify::is_branch, eff_branch),
    ED_INLINE!(api_classify::is_index_method, eff_slice_range_index),
    ED_INLINE!(api_classify::is_slice_get, eff_slice_range_get),
    ED!(api_classify::is_iter_len, eff_iter_len),
    ED!(api_classify::is_iter_is_empty, eff_iter_is_empty),
    ED_INLINE!(api_classify::is_nonnull_checked_new, eff_nonnull_new),
    ED_INLINE!(api_classify::is_iter_next, eff_iter_next),
    ED_INLINE!(api_classify::is_range_next, eff_range_next),
    ED!(api_classify::is_eq_call, eff_none),
    // ── Intrinsics — no MIR body ────────────────────────────────────
    ED!(api_classify::is_layout_constant, eff_layout_const),
    ED!(
        api_classify::is_select_unpredictable,
        eff_select_unpredictable
    ),
    ED!(api_classify::is_ptr_offset_from, eff_ptr_offset_from),
    // ── MIR unavailable — non-#[inline] cross-crate ─────────────────
    ED!(api_classify::is_vec_alloc_constructor, eff_new_allocation),
    ED!(api_classify::is_box_alloc_ctor, eff_box_alloc),
    ED!(api_classify::is_exchange_malloc, eff_exchange_malloc),
    // Needed on older toolchains where `vec![…]` lowers to `into_vec`.
    ED!(api_classify::is_vec_from_box, eff_vec_from_box),
    // `slice::to_vec` copies the slice; model like `into_vec` so
    // `String::from(&str)`'s Vec buffer gets provenance.
    ED!(api_classify::is_slice_to_vec, eff_vec_from_box),
    ED!(
        api_classify::is_vec_with_capacity,
        eff_new_allocation_from_cap
    ),
    ED!(api_classify::is_into_boxed_slice, eff_box_from_vec),
    ED!(api_classify::is_vec_push_or_reserve, eff_write_mem),
    // ── MIR available — precise symbolic summary ────────────────────
    // Non-zero-preserving integer ops discharge `!= 0` conditionally.
    ED!(api_classify::is_max, eff_return_max),
    ED!(api_classify::is_clamp, eff_return_clamp),
    ED!(api_classify::is_abs, eff_return_abs),
    ED!(api_classify::is_neg, eff_return_neg),
    ED!(api_classify::is_sat_unchecked_add, eff_return_add),
    ED!(api_classify::is_sat_unchecked_mul, eff_return_mul),
    ED!(api_classify::is_checked_add, eff_return_option_some_add),
    ED!(api_classify::is_checked_mul, eff_return_option_some_mul),
    ED!(api_classify::is_overflowing_abs_neg, eff_overflowing_nz),
    ED!(api_classify::is_unwrap, eff_alias_arg0),
    // Pointer arithmetic: direction × granularity.
    ED!(api_classify::is_element_ptr_add, eff_ptr_add),
    ED!(api_classify::is_element_ptr_sub, eff_ptr_sub),
    ED!(api_classify::is_byte_ptr_add, eff_ptr_add_byte),
    ED!(api_classify::is_byte_ptr_sub, eff_ptr_sub_byte),
    // Raw-pointer `cast` is excluded (`is_as_ptr_valid`) — left to inlining.
    ED!(api_classify::is_as_ptr_valid, eff_alias_ptr),
    ED!(api_classify::is_str_as_bytes, eff_alias_arg0),
    ED!(api_classify::is_min_like, eff_cmp_min),
    ED!(api_classify::is_bit_preserving_nz, eff_return_nonzero_iff),
    ED!(
        api_classify::is_checked_nonzero_iff,
        eff_return_option_some_nonzero_iff
    ),
    ED!(
        api_classify::is_checked_next_pow2,
        eff_return_option_some_nonzero
    ),
    ED!(api_classify::is_slice_get_unchecked, eff_alias_ptr),
    // `SliceIndex::get_unchecked(self, slice)` returns `slice + self` (receiver
    // is the index), so model as element-strided add off argument 1.
    ED!(
        api_classify::is_sliceindex_get_unchecked,
        eff_sliceindex_get_unchecked
    ),
    ED!(
        api_classify::is_ownership_reconstruction,
        eff_ownership_recon
    ),
    ED!(api_classify::is_manually_drop_drop, eff_drop_memory),
    ED!(api_classify::is_std_drop, eff_drop_memory),
    ED!(api_classify::is_drop_in_place, eff_drop_memory),
    ED!(api_classify::is_split_at, eff_split_at),
    ED!(api_classify::is_from_raw_parts, eff_from_raw_parts),
    ED!(api_classify::is_align_offset, eff_align_offset),
    ED!(api_classify::is_cstr_from_ptr, eff_alias_arg0),
    ED!(api_classify::is_slice_range, eff_slice_range),
    ED!(api_classify::is_mem_replace, eff_mem_replace),
    ED!(api_classify::is_layout_align, eff_layout_align),
    // Local `_ext` re-implementations, matched by name-scanning `fn_defs()`.
    ED!(api_classify::is_align_to_local, eff_align_to),
    ED!(api_classify::is_iter_position, eff_option_scan_index),
    ED!(api_classify::is_strlen, eff_scan_length),
    // ── MIR available — deliberately opaque ─────────────────────────
    // `eff_none` keeps `is_modeled` true so the path graph does not inline.
    ED!(api_classify::is_nonnull_new_unchecked, eff_new_unchecked),
    ED!(api_classify::is_maybe_uninit_uninit, eff_none),
    ED!(api_classify::is_maybe_uninit_assume_init, eff_none),
    ED!(api_classify::is_maybe_uninit_write, eff_write_mem),
];

/// True when `callee` matches a hand-modelled API in the registry. The path
/// graph uses this to keep such calls opaque (it must not inline their branchy
/// CFG when the VM models their semantics more precisely).
pub(crate) fn is_modeled(callee: Option<DefId>) -> bool {
    REGISTRY.iter().any(|e| e.opaque && (e.matches)(callee))
}

/// True when the VM has a symbolic model for `callee` (any registry entry). A
/// cross-crate trait method matching here stays opaque in the path graph rather
/// than being resolved to its impl and inlined.
pub(crate) fn is_symbolically_modeled(callee: Option<DefId>) -> bool {
    REGISTRY.iter().any(|e| (e.matches)(callee))
}

pub(crate) fn lookup_effect<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    callee: Option<DefId>,
    func: &Operand<'tcx>,
    destination: rustc_middle::mir::Local,
) -> Option<CallEffectSummary> {
    let dest = Some(destination);
    for e in REGISTRY {
        if (e.matches)(callee) {
            let ctx = EffCtx {
                tcx,
                caller,
                func,
                dest,
            };
            return Some((e.effects)(&ctx));
        }
    }
    None
}

// ── Effect builders — one small function per API semantic ──────────────

fn eff_none(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    Vec::new()
}

fn eff_select_unpredictable(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::SelectUnpredictable]
}

fn eff_alias_ptr(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    let mut eff = vec![CallEffect::ReturnPointerFromArg { arg: 0 }];
    if pointee_alignment(ctx.tcx, ctx.caller, ctx.dest).is_some() {
        eff.push(CallEffect::ReturnAligned);
    }
    eff
}

/// `SliceIndex::get_unchecked(self, slice)` / `get_unchecked_mut`: returns an
/// element pointer at `slice + self` (receiver is the index, slice pointer is
/// argument 1). Element-strided add off argument 1, inheriting non-nullness
/// from the slice.
fn eff_sliceindex_get_unchecked(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    if !dest_is_pointer(ctx.tcx, ctx.caller, ctx.dest) {
        return Vec::new();
    }
    vec![CallEffect::ReturnPointerAdd {
        base_arg: 1,
        offset_arg: 0,
        stride: destination_stride(ctx.tcx, ctx.caller, ctx.dest),
        dereferenceable: true,
    }]
}

fn eff_alias_arg0(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnAliasArg { arg: 0 }]
}

/// `NonNull::new_unchecked(ptr)`: a transparent re-wrap that preserves `ptr`'s
/// value and provenance (element offset included), inheriting non-nullness from
/// the source rather than asserting it.
fn eff_new_unchecked(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnPointerFromArg { arg: 0 }]
}

fn eff_ptr_add(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    eff_ptr_arith(ctx, PtrDirection::Add, PtrGranularity::Element)
}

fn eff_ptr_sub(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    eff_ptr_arith(ctx, PtrDirection::Sub, PtrGranularity::Element)
}

fn eff_ptr_add_byte(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    eff_ptr_arith(ctx, PtrDirection::Add, PtrGranularity::Byte)
}

fn eff_ptr_sub_byte(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    eff_ptr_arith(ctx, PtrDirection::Sub, PtrGranularity::Byte)
}

fn eff_ptr_offset_from(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnPtrOffsetFrom {
        ptr_arg: 0,
        base_arg: 1,
    }]
}

enum PtrDirection {
    Add,
    Sub,
}

enum PtrGranularity {
    Element,
    Byte,
}

/// Shared model for `ReturnPointerAdd`/`ReturnPointerSub`.
///
/// `wrapping_add`/`wrapping_sub` are shared between integers and raw pointers.
/// When the destination is not a pointer type the call is an integer
/// `wrapping_add`, whose result may wrap to zero, so it is left unconstrained
/// rather than modelled as pointer arithmetic.
fn eff_ptr_arith(
    ctx: &EffCtx<'_, '_>,
    dir: PtrDirection,
    granularity: PtrGranularity,
) -> Vec<CallEffect> {
    if !dest_is_pointer(ctx.tcx, ctx.caller, ctx.dest) {
        return Vec::new();
    }
    let stride = match granularity {
        PtrGranularity::Byte => Some(1),
        PtrGranularity::Element => destination_stride(ctx.tcx, ctx.caller, ctx.dest),
    };
    let effect = match dir {
        PtrDirection::Sub => CallEffect::ReturnPointerSub {
            base_arg: 0,
            offset_arg: 1,
            stride,
        },
        PtrDirection::Add => CallEffect::ReturnPointerAdd {
            base_arg: 0,
            offset_arg: 1,
            stride,
            dereferenceable: false,
        },
    };
    vec![effect]
}

fn eff_write_mem(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::WriteMemory { pointer_arg: 0 }]
}

fn eff_cmp_min(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnMin {
        lhs_arg: 0,
        rhs_arg: 1,
    }]
}

fn eff_return_nonzero_iff(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnNonZeroIff { arg: 0 }]
}

fn eff_return_option_some_nonzero_iff(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnOptionSomeNonZeroIff { arg: 0 }]
}

fn eff_return_option_some_nonzero(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnOptionSomeNonZero]
}

fn eff_return_max(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnMax {
        lhs_arg: 0,
        rhs_arg: 1,
    }]
}

fn eff_return_clamp(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnClamp {
        value_arg: 0,
        min_arg: 1,
        max_arg: 2,
    }]
}

fn eff_return_abs(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnAbs { arg: 0 }]
}

fn eff_return_neg(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnNeg { arg: 0 }]
}

fn eff_return_add(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnAdd {
        lhs_arg: 0,
        rhs_arg: 1,
    }]
}

fn eff_return_mul(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnMul {
        lhs_arg: 0,
        rhs_arg: 1,
    }]
}

fn eff_return_option_some_add(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnOptionSomeAdd {
        lhs_arg: 0,
        rhs_arg: 1,
    }]
}

fn eff_return_option_some_mul(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnOptionSomeMul {
        lhs_arg: 0,
        rhs_arg: 1,
    }]
}

fn eff_overflowing_nz(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnTupleFieldNonZero { field: 0 }]
}

fn eff_ownership_recon(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![
        CallEffect::ReturnAliasArg { arg: 0 },
        CallEffect::ReturnNonZero,
        CallEffect::OwnsInitMemory { arg: 0 },
    ]
}

fn eff_drop_memory(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::DropMemory { pointer_arg: 0 }]
}

fn eff_align_to(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnAlignTo { receiver_arg: 0 }]
}

fn eff_option_scan_index(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnOptionSomeScanIndex { self_arg: 0 }]
}

fn eff_scan_length(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnScanLength]
}

fn eff_align_offset(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnAlignOffset {
        ptr_arg: 0,
        align_arg: 1,
    }]
}

fn eff_split_at(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![
        CallEffect::ReturnAliasArg { arg: 0 },
        CallEffect::ReturnTupleFieldLength {
            field: 0,
            from_arg: 1,
        },
    ]
}

fn eff_slice_range(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnRange { bounds_arg: 1 }]
}

fn eff_mem_replace(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnDerefArg { arg: 0 }]
}

fn eff_from_raw_parts(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    let elem = from_raw_parts_elem_size(ctx.tcx, ctx.caller, ctx.dest);
    let mut eff = vec![
        CallEffect::ReturnFreshAllocation {
            pointer_arg: 0,
            size_arg: 1,
            elem_size: elem,
        },
        CallEffect::ReturnNonZero,
    ];
    if pointee_alignment(ctx.tcx, ctx.caller, ctx.dest).is_some() {
        eff.push(CallEffect::ReturnAligned);
    }
    eff
}

fn eff_new_allocation(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    let elem = from_raw_parts_elem_size(ctx.tcx, ctx.caller, ctx.dest);
    vec![CallEffect::ReturnNewAllocation {
        size_arg: 1,
        elem_size: elem,
    }]
}

fn eff_box_alloc(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnBoxAllocation]
}

fn eff_exchange_malloc(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnExchangeMalloc { size_arg: 0 }]
}

fn eff_new_allocation_from_cap(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    let elem = from_raw_parts_elem_size(ctx.tcx, ctx.caller, ctx.dest);
    vec![CallEffect::ReturnNewAllocationFromCap {
        cap_arg: 0,
        elem_size: elem,
    }]
}

fn eff_vec_from_box(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnNewAllocationFromBox]
}

fn eff_layout_align(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnPowerOfTwo]
}

fn eff_layout_const(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    layout_constant_effect(ctx.tcx, ctx.caller, ctx.func)
        .map_or_else(Vec::new, |e| vec![e])
}

fn eff_branch(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnBranchPayload { arg: 0 }]
}

fn eff_slice_range_index(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnSliceRangeIndex]
}

fn eff_slice_range_get(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnSliceRangeGet]
}

fn eff_iter_len(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnIterLen { is_len: true }]
}

fn eff_iter_is_empty(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnIterLen { is_len: false }]
}

fn eff_nonnull_new(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnNonNullNew]
}

fn eff_iter_next(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnIterNext]
}

fn eff_range_next(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnRangeNext]
}

// ── Layout helpers (used by effect builders) ─────────────────────────

fn dest_is_pointer(tcx: TyCtxt<'_>, caller: DefId, dest: Option<rustc_middle::mir::Local>) -> bool {
    let Some(d) = dest else { return false };
    pointee_ty(tcx.optimized_mir(caller).local_decls[d].ty).is_some()
}

fn layout_call_ty<'tcx>(func: &Operand<'tcx>) -> Option<Ty<'tcx>> {
    mir_utils::fn_def_first_type_arg(func)
}

fn layout_constant_effect<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    func: &Operand<'tcx>,
) -> Option<CallEffect> {
    let ty = layout_call_ty(func)?;
    let callee = mir_utils::dep_callee_def_id(func)?;
    let is_align = def_id::contains(
        &[def_id::mem_align_of(), def_id::intrinsics_align_of()],
        callee,
    );
    let is_size = def_id::contains(
        &[def_id::mem_size_of(), def_id::intrinsics_size_of()],
        callee,
    );
    if !is_size && !is_align {
        return None;
    }
    let (align, size) = type_layout(tcx, caller, ty)?;
    // `type_layout` reports `(0, 0)` for a generic `T` (layout unknown): bind
    // the shared symbolic `sizeof_T` / `align_T` at apply time (the
    // `align_of::<T>() >= 1` bound keeps a cast like `align as *const T` in
    // `NonNull::dangling` non-null).
    if align == 0 && size == 0 {
        return Some(CallEffect::ReturnLayoutSymbolic { is_size });
    }
    Some(CallEffect::ReturnConst {
        value: if is_align { align } else { size },
    })
}

fn eff_box_from_vec(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnBoxFromVec { arg: 0 }]
}

// ── Non-registry effect fallback ────────────────────────────────────

/// Transparent-wrapper deref (`ManuallyDrop`/`MaybeDangling`) when the registry
/// has no match: the return aliases the receiver's inner value.
pub(crate) fn effect_summary<'tcx>(tcx: TyCtxt<'tcx>, func: &Operand<'tcx>) -> Option<CallEffectSummary> {
    if let Some(peel) = transparent_deref_peel(tcx, func) {
        return Some(vec![CallEffect::ReturnTransparentDeref { arg: 0, peel }]);
    }
    None
}

fn transparent_deref_peel<'tcx>(tcx: TyCtxt<'tcx>, func: &Operand<'tcx>) -> Option<usize> {
    let self_ty = mir_utils::fn_def_first_type_arg(func)?;
    let TyKind::Adt(adt_def, _) = self_ty.kind() else {
        return None;
    };
    let did = adt_def.did();
    if tcx.is_lang_item(did, LangItem::ManuallyDrop) {
        return Some(2);
    }
    if tcx.is_lang_item(did, LangItem::MaybeDangling) {
        return Some(1);
    }
    None
}

// ── Collection element-size helpers ─────────────────────────────────

/// Element type of a `Vec<T>`, if `ty` is a `Vec`.
pub(crate) fn vec_elem_ty<'tcx>(ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    if let TyKind::Adt(adt_def, substs) = ty.kind()
        && api_classify::is_std_vec(adt_def.did()) {
            return substs.first().and_then(|s| s.as_type());
        }
    None
}

/// Element type of a `from_raw_parts` result: `&[T]`/`*[T]`/`Vec<T>` yield `T`;
/// other types (including `String`) return `None`.
pub(crate) fn from_raw_parts_elem_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    dest: Option<Local>,
) -> Option<Ty<'tcx>> {
    let d = dest?;
    let ty = tcx.optimized_mir(caller).local_decls[d].ty;
    match ty.kind() {
        TyKind::Ref(_, inner, _) => match inner.kind() {
            TyKind::Slice(e) => Some(*e),
            _ => None,
        },
        TyKind::RawPtr(inner, _) => match inner.kind() {
            TyKind::Slice(e) => Some(*e),
            _ => None,
        },
        TyKind::Adt(..) => vec_elem_ty(ty),
        _ => None,
    }
}

/// Element size of a `from_raw_parts` result; `String`/unknown layouts fall
/// back to 1 (`String`'s element is `u8`).
pub(crate) fn from_raw_parts_elem_size<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    dest: Option<Local>,
) -> u64 {
    from_raw_parts_elem_ty(tcx, caller, dest)
        .and_then(|e| mir_utils::type_layout(tcx, caller, e).map(|(_, s)| s))
        .unwrap_or(1)
}
