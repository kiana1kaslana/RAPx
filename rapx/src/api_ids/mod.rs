//! API identities and the current compilation's MIR availability.

pub(crate) mod intrinsic_api;
pub(crate) mod nomir_api;
pub(crate) mod other_api;

use rustc_middle::ty::TyCtxt;

pub(crate) fn init(tcx: TyCtxt<'_>) {
    other_api::init(tcx);
    intrinsic_api::init(tcx);
    nomir_api::init(tcx);
}
