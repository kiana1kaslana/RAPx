//! Identity checks for compiler lang items used by the verifier.

#[cfg(rapx_has_attr_ir)]
pub(crate) use rustc_attr_ir::LangItem;
#[cfg(all(not(rapx_has_attr_ir), not(rapx_ge_100)))]
pub(crate) use rustc_hir::LangItem;
#[cfg(all(not(rapx_has_attr_ir), rapx_ge_100))]
pub(crate) use rustc_hir::attrs::lang_items::LangItem;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

/// Match a compiler-provided lang item by its `DefId`.
pub(crate) fn matches(tcx: TyCtxt<'_>, def_id: DefId, item: LangItem) -> bool {
    tcx.is_lang_item(def_id, item)
}

/// The plain `panic!` entry point, which only consumes a static message.
pub(crate) fn is_panic_exit(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    matches(tcx, callee, LangItem::Panic)
}

/// Panic lang items used as diverging exits in MIR.
pub(crate) fn is_panic_family(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    is_panic_exit(tcx, callee)
        || matches(tcx, callee, LangItem::PanicNounwind)
        || matches(tcx, callee, LangItem::PanicFmt)
        || matches(tcx, callee, LangItem::PanicDisplay)
        || matches(tcx, callee, LangItem::ConstPanicFmt)
        || matches(tcx, callee, LangItem::PanicBoundsCheck)
        || matches(tcx, callee, LangItem::PanicMisalignedPointerDereference)
}
