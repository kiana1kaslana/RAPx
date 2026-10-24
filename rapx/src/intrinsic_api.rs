//! Compiler intrinsic identification and call classification by `DefId`.
//! Intrinsic identities come from compiler metadata, independently of the
//! standard-library API path table.

use std::collections::HashMap;
use std::sync::OnceLock;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_public::{CrateDef, rustc_internal};
use rustc_span::Symbol;

static IDS: OnceLock<HashMap<DefId, Symbol>> = OnceLock::new();

pub fn init(tcx: TyCtxt<'_>) {
    IDS.get_or_init(|| {
        let mut ids = HashMap::new();
        for krate in std::iter::once(rustc_public::local_crate())
            .chain(rustc_public::external_crates())
            .filter(|krate| matches!(krate.name.as_str(), "core" | "std" | "alloc"))
        {
            for function in krate.fn_defs() {
                let id = rustc_internal::internal(tcx, function.def_id());
                if let Some(intrinsic) = tcx.intrinsic(id) {
                    ids.insert(id, intrinsic.name);
                }
            }
        }
        ids
    });
}

fn matches_names(callee: Option<DefId>, names: &[&str]) -> bool {
    callee
        .and_then(|id| {
            IDS.get()
                .expect("Intrinsic IDs have not been initialized")
                .get(&id)
        })
        .is_some_and(|name| names.contains(&name.as_str()))
}

pub fn get(name: &str) -> Option<DefId> {
    IDS.get()
        .expect("Intrinsic IDs have not been initialized")
        .iter()
        .find_map(|(&id, intrinsic)| (intrinsic.as_str() == name).then_some(id))
}

pub fn is_intrinsic(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    tcx.intrinsic(callee).is_some()
}

pub fn is_size_of(callee: Option<DefId>) -> bool {
    matches_names(callee, &["size_of"])
}

pub fn is_align_of(callee: Option<DefId>) -> bool {
    matches_names(callee, &["align_of"])
}

pub fn is_copy(callee: Option<DefId>) -> bool {
    matches_names(callee, &["copy", "copy_nonoverlapping"])
}

pub fn is_ptr_offset_from(callee: Option<DefId>) -> bool {
    matches_names(callee, &["ptr_offset_from", "ptr_offset_from_unsigned"])
}

/// `intrinsics::arith_offset` is the *wrapping* pointer offset backing
/// `wrapping_add`/`wrapping_offset`.  Unlike `intrinsics::offset` (which the
/// MIR builder lowers to `BinOp::Offset`), it stays a `Call` to the intrinsic,
/// so it must be classified here rather than reaching the `Offset` rvalue rule.
pub fn is_arith_offset(callee: Option<DefId>) -> bool {
    matches_names(callee, &["arith_offset"])
}

pub fn is_pure_opaque(callee: Option<DefId>) -> bool {
    matches_names(
        callee,
        &[
            "float_to_int_unchecked",
            "vtable_size",
            "vtable_align",
            "size_of_val",
        ],
    )
}

pub fn is_raw_eq(callee: Option<DefId>) -> bool {
    matches_names(callee, &["raw_eq"])
}

pub fn is_exact_div(callee: Option<DefId>) -> bool {
    matches_names(callee, &["exact_div"])
}

pub fn is_typed_swap_nonoverlapping(callee: Option<DefId>) -> bool {
    matches_names(callee, &["typed_swap_nonoverlapping"])
}

pub fn is_write_bytes(callee: Option<DefId>) -> bool {
    matches_names(callee, &["write_bytes"])
}

pub fn is_black_box(callee: Option<DefId>) -> bool {
    matches_names(callee, &["black_box"])
}

pub(crate) fn is_select_unpredictable(callee: Option<DefId>) -> bool {
    matches_names(callee, &["select_unpredictable"])
}

pub(crate) fn is_branch_hint(callee: Option<DefId>) -> bool {
    matches_names(callee, &["unlikely", "likely"])
}

pub(crate) fn is_with_overflow(callee: Option<DefId>) -> bool {
    matches_names(
        callee,
        &[
            "add_with_overflow",
            "sub_with_overflow",
            "mul_with_overflow",
        ],
    )
}

pub(crate) fn is_add_with_overflow(callee: Option<DefId>) -> bool {
    matches_names(callee, &["add_with_overflow"])
}

pub(crate) fn is_sub_with_overflow(callee: Option<DefId>) -> bool {
    matches_names(callee, &["sub_with_overflow"])
}

pub fn is_integer_min(callee: Option<DefId>) -> bool {
    matches_names(callee, &["integer_min"])
}

pub fn is_integer_max(callee: Option<DefId>) -> bool {
    matches_names(callee, &["integer_max"])
}

pub fn is_saturating_sub(callee: Option<DefId>) -> bool {
    matches_names(callee, &["saturating_sub"])
}

pub fn is_nonzero_preserving(callee: Option<DefId>) -> bool {
    matches_names(
        callee,
        &[
            "bswap",
            "ctpop",
            "bitreverse",
            "rotate_left",
            "rotate_right",
        ],
    )
}

pub fn is_saturating_add(callee: Option<DefId>) -> bool {
    matches_names(callee, &["saturating_add"])
}

pub fn is_unchecked_add(callee: Option<DefId>) -> bool {
    matches_names(callee, &["unchecked_add"])
}

pub fn is_unchecked_mul(callee: Option<DefId>) -> bool {
    matches_names(callee, &["unchecked_mul"])
}

pub fn is_wrapping_sub(callee: Option<DefId>) -> bool {
    matches_names(callee, &["wrapping_sub"])
}
