//! Unified property checker for the symbolic VM.
//!
//! `PropertyChecker::check` is the entry point; `check_inner` dispatches each
//! `PropertyKind` to a per-family `check_*` method living in one of the sibling
//! submodules (`memory`, `bounds`, `typed`, `numeric`, `string`, `alias`,
//! `cstr`, `transmute`).  Shared helpers live in `util`.

use crate::verify::checkpoint::Checkpoint;
use crate::verify::vm::state::{OffsetKind, VmState};
use crate::verify::{
    contract::{Property, PropertyKind},
    report::{CheckResult, UnknownReason},
};

mod alias;
mod auto_trait;
mod bounds;
mod cstr;
mod memory;
mod numeric;
mod string;
mod transmute;
mod typed;
mod util;

pub(crate) use auto_trait::{
    atomic_update_check, contain_no_type_check, field_invariant_check, no_internal_mut_check,
    no_raw_ptr_check, ref_send_check, uni_internal_mut_check,
};

pub(crate) struct PropertyChecker;

/// A property-checking rule: prove a [`PropertyKind`] by matching the kind and
/// running the associated checker.  `kind` is the `PropertyKind` itself (a
/// `Copy` enum, so no predicate function is needed), and `apply` is the checker
/// under one uniform signature.
pub(crate) struct PropertyRule {
    /// Rule name, for logging / hit-statistics / debugging.
    pub name: &'static str,
    /// The `PropertyKind` this rule discharges.
    pub kind: PropertyKind,
    /// The checker: prove `property` (whose kind equals `self.kind`).
    pub apply: for<'z3, 'tcx> fn(
        &PropertyChecker,
        &VmState<'z3, 'tcx>,
        &Checkpoint<'tcx>,
        &Property<'tcx>,
    ) -> CheckResult,
}

/// `NonVolatile` is uncheckable: the VM does not model volatile access, so
/// there is nothing to disprove.  Treated as satisfied (Proved) as a documented
/// soundness assumption — analysed code is assumed not to mix volatile and
/// non-volatile access.  Revisit if volatile tracking is ever added.
fn check_non_volatile<'z3, 'tcx>(
    _checker: &PropertyChecker,
    _vm_state: &VmState<'z3, 'tcx>,
    _checkpoint: &Checkpoint<'tcx>,
    _property: &Property<'tcx>,
) -> CheckResult {
    CheckResult::ProvedByRule
}

/// Fallback for `PropertyKind`s without a dedicated checker (`Unwrap`, `Pinned`,
/// `Opened`, `Unreachable`, `Unknown`, …): reported `Unknown`.
fn check_unknown<'z3, 'tcx>(
    _checker: &PropertyChecker,
    _vm_state: &VmState<'z3, 'tcx>,
    _checkpoint: &Checkpoint<'tcx>,
    _property: &Property<'tcx>,
) -> CheckResult {
    CheckResult::Unknown(UnknownReason::Unimplemented)
}

/// Every property rule, in dispatch order.
pub(crate) const PROPERTY_RULES: &[PropertyRule] = &[
    PropertyRule {
        name: "align",
        kind: PropertyKind::Align,
        apply: PropertyChecker::check_align,
    },
    PropertyRule {
        name: "non_null",
        kind: PropertyKind::NonNull,
        apply: PropertyChecker::check_non_null,
    },
    PropertyRule {
        name: "null",
        kind: PropertyKind::Null,
        apply: PropertyChecker::check_null,
    },
    PropertyRule {
        name: "allocated",
        kind: PropertyKind::Allocated,
        apply: PropertyChecker::check_allocated,
    },
    PropertyRule {
        name: "in_bound",
        kind: PropertyKind::InBound,
        apply: PropertyChecker::check_in_bound,
    },
    PropertyRule {
        name: "init",
        kind: PropertyKind::Init,
        apply: PropertyChecker::check_init,
    },
    PropertyRule {
        name: "typed",
        kind: PropertyKind::Typed,
        apply: PropertyChecker::check_typed,
    },
    PropertyRule {
        name: "alias",
        kind: PropertyKind::Alias,
        apply: PropertyChecker::check_alias,
    },
    PropertyRule {
        name: "owning",
        kind: PropertyKind::Owning,
        apply: PropertyChecker::check_owning,
    },
    PropertyRule {
        name: "alive",
        kind: PropertyKind::Alive,
        apply: PropertyChecker::check_alive,
    },
    PropertyRule {
        name: "non_overlap",
        kind: PropertyKind::NonOverlap,
        apply: PropertyChecker::check_non_overlap,
    },
    PropertyRule {
        name: "non_volatile",
        kind: PropertyKind::NonVolatile,
        apply: check_non_volatile,
    },
    PropertyRule {
        name: "valid_num",
        kind: PropertyKind::ValidNum,
        apply: PropertyChecker::check_valid_num,
    },
    PropertyRule {
        name: "valid_string",
        kind: PropertyKind::ValidString,
        apply: PropertyChecker::check_valid_string,
    },
    PropertyRule {
        name: "valid_cstr",
        kind: PropertyKind::ValidCStr,
        apply: PropertyChecker::check_valid_cstr,
    },
    PropertyRule {
        name: "valid_transmute",
        kind: PropertyKind::ValidTransmute,
        apply: PropertyChecker::check_valid_transmute,
    },
    PropertyRule {
        name: "split_transmute",
        kind: PropertyKind::SplitTransmute,
        apply: PropertyChecker::check_split_transmute,
    },
    PropertyRule {
        name: "trait",
        kind: PropertyKind::Trait,
        apply: PropertyChecker::check_trait,
    },
    PropertyRule {
        name: "size",
        kind: PropertyKind::Size,
        apply: PropertyChecker::check_size,
    },
    PropertyRule {
        name: "no_padding",
        kind: PropertyKind::NoPadding,
        apply: PropertyChecker::check_no_padding,
    },
    PropertyRule {
        name: "contain_no_type",
        kind: PropertyKind::ContainNoType,
        apply: PropertyChecker::check_contain_no_type,
    },
    PropertyRule {
        name: "no_raw_ptr",
        kind: PropertyKind::NoRawPtr,
        apply: PropertyChecker::check_no_raw_ptr,
    },
    PropertyRule {
        name: "no_internal_mut",
        kind: PropertyKind::NoInternalMut,
        apply: PropertyChecker::check_no_internal_mut,
    },
    PropertyRule {
        name: "uni_internal_mut",
        kind: PropertyKind::UniInternalMut,
        apply: PropertyChecker::check_uni_internal_mut,
    },
    PropertyRule {
        name: "atomic_update",
        kind: PropertyKind::AtomicUpdate,
        apply: PropertyChecker::check_atomic_update,
    },
    PropertyRule {
        name: "ref_send",
        kind: PropertyKind::RefSend,
        apply: PropertyChecker::check_ref_send,
    },
];

/// Fallback rule for kinds with no dedicated checker.
pub(crate) const UNKNOWN_RULE: PropertyRule = PropertyRule {
    name: "unknown",
    kind: PropertyKind::Unknown,
    apply: check_unknown,
};

impl PropertyChecker {
    pub(crate) fn check<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        if vm_state.unsupported_mir {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        }
        self.check_inner(vm_state, checkpoint, property)
    }

    fn check_inner<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        // Vacuous truth (implicit): a property whose target place carries an
        // `unwrap_some()` / `iter()` projection is trivially satisfied when the
        // container resolves to no allocation (e.g. `Option::None`).  This is
        // distinct from the explicit `Null(p)` guard in `any(Null(p), …)`,
        // which is a `PropertyKind::Null` disjunct handled by `check_null`.
        if self.is_vacuously_true_for_nullable(vm_state, checkpoint, property) {
            return CheckResult::ProvedByRule;
        }
        match property {
            Property::Or(_) => self.check_or(vm_state, checkpoint, property),
            Property::And(_) => self.check_and(vm_state, checkpoint, property),
            Property::Atom(atom) => {
                // A property whose target value (or a checkpoint argument it
                // reads) depends on a truncated inline cannot be decided:
                // report `Unknown` instead of failing on the placeholder term.
                if self.atom_depends_on_truncated_inline(vm_state, checkpoint, property) {
                    return CheckResult::Unknown(UnknownReason::InlineDepthExceeded);
                }
                let rule = PROPERTY_RULES
                    .iter()
                    .find(|r| r.kind == atom.kind)
                    .unwrap_or(&UNKNOWN_RULE);
                crate::rap_debug!("property rule: {}", rule.name);
                (rule.apply)(self, vm_state, checkpoint, property)
            }
        }
    }

    /// Whether this atom's target value (or a checkpoint argument it reads, or
    /// its pointer provenance offset) depends on a truncated inline — i.e. it is
    /// one of `VmState::inline_truncated_terms`.  Such a value is an
    /// unconstrained placeholder, so any proof/failure would be spurious.
    fn atom_depends_on_truncated_inline<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> bool {
        let truncated = &vm_state.inline.inline_truncated_terms;
        if truncated.is_empty() {
            return false;
        }
        // The checkpoint's argument operands (e.g. `ptr.add(n)`'s `n`) are what
        // the property constrains; a truncated argument makes the check
        // undecidable even when the target pointer itself is well-defined.
        for operand in &checkpoint.args {
            if self.value_involves_truncated(truncated, &vm_state.value_of_operand(operand)) {
                return true;
            }
        }
        if let Some(value) = self.target_value(vm_state, checkpoint, property)
            && self.value_involves_truncated(truncated, &value)
        {
            return true;
        }
        false
    }

    fn value_involves_truncated<'z3, 'tcx>(
        &self,
        truncated: &rustc_hash::FxHashSet<z3::ast::Int<'z3>>,
        value: &crate::verify::vm::state::VmValue<'z3, 'tcx>,
    ) -> bool {
        if truncated.contains(&value.z3_term) {
            return true;
        }
        value.provenance.as_ref().is_some_and(|p| {
            truncated.contains(&p.offset)
                || matches!(
                    &p.offset_kind,
                    Some(OffsetKind::Element(e)) if truncated.contains(e)
                )
        })
    }

    fn check_or<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        // OR semantics: proved if any disjunct is proved; failed only if every
        // disjunct is definitely violated; otherwise unknown.  An empty
        // disjunction is unsatisfiable, hence Failed.
        let mut overall = CheckResult::Failed;
        for disjunct in property.disjuncts() {
            let result = self.check_inner(vm_state, checkpoint, disjunct);
            overall = overall.or(result);
        }
        overall
    }

    fn check_and<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        // AND semantics: proved if every conjunct is proved; failed if any is
        // definitely violated; otherwise unknown.  An empty conjunction is
        // vacuously proved.
        let mut overall = CheckResult::ProvedByRule;
        for conjunct in property.conjuncts() {
            let result = self.check_inner(vm_state, checkpoint, conjunct);
            overall = overall.and(result);
        }
        overall
    }
}
