//! Known `core`/`std`/`alloc` API identities and semantic classifications.
//!
//! The path table resolves well-known items to [`DefId`]s. The classifiers
//! below combine those identities into operations used by analyses and checks.
//! The table owns global state initialized by the compiler callback.
//!
//! # How a lookup works
//!
//! 1. The [`known_items!`] macro declares a *path table*: each identifier maps
//!    to one or more candidate `fn_def.name()` strings (typically the `std::`
//!    re-export plus the `core::`/`alloc::` canonical form, for `#![no_std]`
//!    crates) and generates a `{id}() -> Option<DefId>` accessor.
//! 2. [`init`] runs once from [`crate::RapCallback::after_analysis`], iterates
//!    every `fn_def` of the `core`/`std`/`alloc` crates via `rustc_public`,
//!    and caches the `path -> DefId` map in a `OnceLock`.
//! 3. [`contains`] tests whether a call-site `DefId` is in a set of resolved
//!    ids; [`is_drop_fn`] is a convenience wrapper over the drop family.
//!
//! # Path format
//!
//! `rustc_public::CrateDef::name()` is `def_path_str` with crate-name
//! resolution and untrimmed paths, so a re-exported item appears under its
//! `std::` name and generics are kept: `std::mem::MaybeUninit::<T>::write`,
//! `std::result::Result::<T, E>::unwrap`, `std::vec::Vec::<T, A>::push`,
//! `std::ptr::mut_ptr::<impl *mut T>::copy_from`.
//!
//! # Limitations
//!
//! - In `#![no_std]` builds some standard-library items are absent; [`init`] only warns
//!   (`rap_warn!`) instead of panicking, so an entry with no matching path
//!   simply yields `None`.

use indexmap::IndexMap;
#[cfg(rapx_has_attr_ir)]
use rustc_attr_ir::LangItem;
#[cfg(all(not(rapx_has_attr_ir), not(rapx_ge_100)))]
use rustc_hir::LangItem;
#[cfg(all(not(rapx_has_attr_ir), rapx_ge_100))]
use rustc_hir::attrs::lang_items::LangItem;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_public::{CrateDef, rustc_internal};
use rustc_span::sym;
use std::sync::OnceLock;

static INIT: OnceLock<KnownItems> = OnceLock::new();

struct KnownItems {
    // The key is fn path, starting from `core::` or `std::`. The value is internal def id.
    map: IndexMap<Box<str>, DefId>,
}

static TYPES: OnceLock<Types> = OnceLock::new();

/// Resolved `DefId`s of well-known std *types* (ADTs), used by the ADT
/// type-name classifiers ([`crate::other_api::is_std_box`],
/// [`crate::other_api::is_std_vec`], …).  Each entry collects the
/// std type's `DefId` (via lang/diagnostic item, or — for `NonNull`, which has
/// neither — by name-scanning the std crates' `adts()`) *and* any same-named
/// re-implementations in the local crate (the std-challenge suites re-implement
/// `Vec`/`NonNull` under the same names).
struct Types {
    box_types: Vec<DefId>,
    cstring_types: Vec<DefId>,
    vec_types: Vec<DefId>,
    nonnull_types: Vec<DefId>,
    maybe_uninit_types: Vec<DefId>,
    ascii_char_types: Vec<DefId>,
    ordering_types: Vec<DefId>,
    iter_types: Vec<DefId>,
    rc_types: Vec<DefId>,
    sync_primitive_types: Vec<DefId>,
    index_range_types: Vec<DefId>,
    /// `alloc::alloc::exchange_malloc` (`Box::new`'s lang item on toolchains
    /// that lower `Box::new` to it) — resolved by name scan, since it has no
    /// lang item on newer toolchains.
    exchange_malloc: Option<DefId>,
    /// Negative auto-trait types (`Cell`/`UnsafeCell`/`RefCell`/`Ref`/`RefMut`/
    /// guards), keyed by short name — used by `ContainNoType` in Send/Sync obligations.
    negative_types: IndexMap<Box<str>, Vec<DefId>>,
}

/// Short names of the std `!Send`/`!Sync` negative types resolved by name scan
/// (those without a lang/diagnostic item).  `UnsafeCell` is resolved via its
/// `#[lang = "unsafe_cell"]` item instead.
const NEGATIVE_TYPE_NAMES: &[&str] = &[
    "Cell",
    "RefCell",
    "Ref",
    "RefMut",
    "MutexGuard",
    "RwLockWriteGuard",
    "MappedMutexGuard",
];

pub fn init(tcx: TyCtxt) {
    INIT.get_or_init(|| init_inner(tcx));
    TYPES.get_or_init(|| init_types(tcx));
    METHODS.get_or_init(|| init_methods(tcx));
}

fn init_types(tcx: TyCtxt) -> Types {
    let mut types = Types {
        box_types: Vec::new(),
        cstring_types: Vec::new(),
        vec_types: Vec::new(),
        nonnull_types: Vec::new(),
        maybe_uninit_types: Vec::new(),
        ascii_char_types: Vec::new(),
        ordering_types: Vec::new(),
        iter_types: Vec::new(),
        rc_types: Vec::new(),
        sync_primitive_types: Vec::new(),
        index_range_types: Vec::new(),
        exchange_malloc: None,
        negative_types: IndexMap::new(),
    };

    // Real std types via diagnostic/lang items (`NonNull` only before rustc
    // 1.100, when it was still a diagnostic item).
    types.box_types.extend(tcx.lang_items().owned_box());
    types
        .cstring_types
        .extend(tcx.get_diagnostic_item(sym::cstring_type));
    types.vec_types.extend(tcx.get_diagnostic_item(sym::Vec));
    types.rc_types.extend(tcx.get_diagnostic_item(sym::Rc));
    // `core::cmp::Ordering` is `#[lang = "Ordering"]`.
    types
        .ordering_types
        .extend(tcx.lang_items().ordering_enum());
    // `core::mem::MaybeUninit` is `#[lang = "maybe_uninit"]`.
    types
        .maybe_uninit_types
        .extend(tcx.lang_items().maybe_uninit());
    // `core::cell::UnsafeCell` is `#[lang = "unsafe_cell"]`.
    if let Some(unsafe_cell) = tcx.lang_items().unsafe_cell_type() {
        types
            .negative_types
            .entry("UnsafeCell".into())
            .or_default()
            .push(unsafe_cell);
    }

    // `core::slice::Iter` is `#[rustc_diagnostic_item = "SliceIter"]` on older
    // toolchains (the item was dropped once `adts()` became available, so only
    // referenced when `adts()` is absent). `slice::IterMut` has no diagnostic
    // item, so resolve it from the self type of its `fn_defs()`-emitted methods.
    #[cfg(not(rapx_has_public_adts))]
    {
        types
            .iter_types
            .extend(tcx.get_diagnostic_item(sym::SliceIter));
        types
            .nonnull_types
            .extend(tcx.get_diagnostic_item(sym::NonNull));

        for krate in rustc_public::external_crates()
            .into_iter()
            .filter(|k| ["core", "std", "alloc"].iter().any(|n| *n == k.name))
        {
            for fn_def in krate.fn_defs() {
                let name = fn_def.name();
                let did = rustc_internal::internal(tcx, fn_def.def_id());
                if name.contains("::IterMut::") {
                    if let Some(adt_did) = assoc_self_adt_did(tcx, did) {
                        types.iter_types.push(adt_did);
                    }
                }
                // `std::ascii::Char` has no diagnostic item on toolchains
                // without `adts()`; resolve it from the self type of its
                // methods (`core::ascii::Char::from_u8` etc.).
                if name.contains("::Char::") {
                    if let Some(adt_did) = assoc_self_adt_did(tcx, did) {
                        if !types.ascii_char_types.contains(&adt_did) {
                            types.ascii_char_types.push(adt_did);
                        }
                    }
                }
                // `alloc::alloc::exchange_malloc` (`Box::new`'s allocator on
                // some toolchains) has no lang item on newer toolchains; resolve
                // it by name so `Box::new`'s fresh allocation keeps provenance.
                if name.contains("exchange_malloc") {
                    types.exchange_malloc.get_or_insert(did);
                }
                // Synchronization primitives have no diagnostic/lang item, so
                // resolve them from the self type of their methods (the
                // `adts()`-less fallback path).
                if is_sync_primitive_method(&name) {
                    if let Some(adt_did) = assoc_self_adt_did(tcx, did) {
                        if !types.sync_primitive_types.contains(&adt_did) {
                            types.sync_primitive_types.push(adt_did);
                        }
                    }
                }
            }
        }
    }

    // Same-named re-implementations in the local crate (the std-challenge
    // suites re-implement `NonNull`/`Iter`/`IterMut`). Scan local ADTs by name
    // via `iter_local_def_id`, which works on every toolchain.
    for local_did in tcx.iter_local_def_id() {
        let did = local_did.to_def_id();
        if !matches!(
            tcx.def_kind(did),
            rustc_hir::def::DefKind::Struct
                | rustc_hir::def::DefKind::Enum
                | rustc_hir::def::DefKind::Union
        ) {
            continue;
        }
        let name = tcx.def_path_str(did);
        collect_type_by_name(&mut types, &name, did);
    }

    // External std ADTs with neither a lang nor a diagnostic item: `NonNull`
    // on newer toolchains (it became `#[lang = "non_null"]`, which has no
    // `LangItem` variant) and `slice::Iter`/`IterMut` (no diagnostic item).
    // Resolve by name-scanning the std crates' `adts()`.
    #[cfg(rapx_has_public_adts)]
    {
        for krate in rustc_public::external_crates()
            .into_iter()
            .filter(|k| ["core", "std", "alloc"].iter().any(|n| *n == k.name))
        {
            for adt in krate.adts() {
                let name = adt.name();
                let did = rustc_internal::internal(tcx, adt.def_id());
                collect_type_by_name(&mut types, &name, did);
            }
        }
    }

    types
}

/// Collect `did` into the matching well-known type group by name.  Shared by the
/// local-crate scan (`iter_local_def_id`) and the external std scan (`adts()`),
/// which collect the *same* groups from different crates (std originals vs the
/// std-challenge suites' re-implementations).
fn collect_type_by_name(types: &mut Types, name: &str, did: DefId) {
    if name.ends_with("::Vec") || name == "Vec" {
        types.vec_types.push(did);
    }
    if name.ends_with("::Iter")
        || name == "Iter"
        || name.ends_with("::IterMut")
        || name == "IterMut"
    {
        types.iter_types.push(did);
    }
    if name.ends_with("::NonNull") || name == "NonNull" {
        types.nonnull_types.push(did);
    }
    if name.ends_with("::MaybeUninit") || name == "MaybeUninit" {
        types.maybe_uninit_types.push(did);
    }
    if name.ends_with("::IndexRange") || name == "IndexRange" {
        types.index_range_types.push(did);
    }
    if name.ends_with("::AsciiChar")
        || name.ends_with("::Char")
        || name == "AsciiChar"
        || name == "Char"
    {
        types.ascii_char_types.push(did);
    }
    if name.ends_with("::Rc") || name == "Rc" {
        types.rc_types.push(did);
    }
    let short = name.rsplit("::").next().unwrap_or(name);
    if is_sync_primitive_short_name(short) {
        types.sync_primitive_types.push(did);
    }
    if let Some(neg) = negative_type_name(short) {
        types
            .negative_types
            .entry(neg.into())
            .or_default()
            .push(did);
    }
}

/// Whether a type's short name denotes a synchronization primitive that guards
/// its interior mutability (`Mutex`/`RwLock`/`OnceLock`/`OnceCell`/`Atomic*`).
fn is_sync_primitive_short_name(short: &str) -> bool {
    matches!(short, "Mutex" | "RwLock" | "OnceLock" | "OnceCell") || short.starts_with("Atomic")
}

/// The negative-type name for a short type name, if it is one of the std
/// `!Send`/`!Sync` negative types.
fn negative_type_name(short: &str) -> Option<&'static str> {
    NEGATIVE_TYPE_NAMES.iter().copied().find(|&n| n == short)
}

/// Whether an `fn_def.name()` (e.g. `std::sync::Mutex::<T>::lock`) belongs to a
/// synchronization primitive's inherent method.  Used to resolve the primitive's
/// ADT from its methods' self type when `adts()` is unavailable.
#[cfg(not(rapx_has_public_adts))]
fn is_sync_primitive_method(name: &str) -> bool {
    name.contains("::Mutex::")
        || name.contains("::RwLock::")
        || name.contains("::OnceLock::")
        || name.contains("::OnceCell::")
        || name.contains("::Atomic")
}

macro_rules! type_defs {
    ($( $(#[$attr:meta])* $name:ident ,)+) => {
        $(
            $(#[$attr])*
            pub fn $name() -> &'static [DefId] {
                &TYPES
                    .get()
                    .expect("Type DefIds haven't been initialized.")
                    .$name
            }
        )+
    };
}

type_defs! {
    /// `alloc::boxed::Box` (and any local `Box` re-implementation).
    box_types,
    /// `alloc::ffi::CString` (and any local `CString` re-implementation).
    cstring_types,
    /// `alloc::vec::Vec` (and any local `Vec` re-implementation).
    vec_types,
    /// `core::ptr::NonNull` (and any local `NonNull` re-implementation).
    nonnull_types,
    /// `core::mem::MaybeUninit` (and any local re-implementation).
    maybe_uninit_types,
    /// `core::ascii::Char` (`AsciiChar`, the `u8` newtype; and any local
    /// re-implementation).
    ascii_char_types,
    /// `core::cmp::Ordering`.
    ordering_types,
    /// `core::slice::Iter` / `core::slice::IterMut` (the two-field `ptr`/`end`
    /// slice iterators, plus any local re-implementation).
    iter_types,
    /// `alloc::rc::Rc` (and any local `Rc` re-implementation) — the non-atomic
    /// reference-counted smart pointer, a `!Send`/`!Sync` negative type.
    rc_types,
    /// Synchronization primitives (`Mutex`/`RwLock`/`OnceLock`/`OnceCell`/`Atomic*`,
    /// plus any local re-implementation) that guard their interior mutability, used
    /// to discharge the `RefSend` auto-trait obligation.
    sync_primitive_types,
    /// `core::range::IndexRange` (and any local re-implementation).
    index_range_types,
}

/// `alloc::alloc::exchange_malloc`, if present on this toolchain.
pub fn exchange_malloc() -> Option<DefId> {
    TYPES
        .get()
        .expect("Type DefIds haven't been initialized.")
        .exchange_malloc
}

/// Resolve a negative-type name (as written in `std-trait-ensures.json`) to its
/// resolved `DefId` set.  Unknown names resolve to an empty set (the checker
/// then reports `Unknown`).
pub fn negative_type_defs(name: &str) -> &'static [DefId] {
    match name {
        "Rc" => rc_types(),
        "NonNull" => nonnull_types(),
        _ => TYPES
            .get()
            .and_then(|t| t.negative_types.get(name))
            .map(Vec::as_slice)
            .unwrap_or(&[]),
    }
}

/// Resolved `DefId`s of std *methods* that are matched by *generic name* rather
/// than a fixed `known_items!` path (e.g. `len`, `capacity`, `::abs`,
/// `::checked_add`, `::split_at`, `Iterator::position`, …). Each group collects
/// every `fn_def` — from the std crates *and* the local crate (the
/// std-challenge suites re-implement `Vec`/slice-like types and their methods) —
/// whose name matches the group's pattern. Callers match a call-site `DefId`
/// against these sets via [`contains`].
static METHODS: OnceLock<Methods> = OnceLock::new();

struct Methods {
    len_fns: Vec<DefId>,
    from_raw_parts_fns: Vec<DefId>,
    from_raw_parts_mut_fns: Vec<DefId>,
    with_metadata_of_fns: Vec<DefId>,
    integer_wrapping_sub_fns: Vec<DefId>,
    with_capacity_fns: Vec<DefId>,
    box_alloc_ctors: Vec<DefId>,
    vec_ownership_transfer_fns: Vec<DefId>,
    checked_next_pow2: Vec<DefId>,
    layout_align: Vec<DefId>,
    split_at: Vec<DefId>,
    align_to_local: Vec<DefId>,
    iter_position: Vec<DefId>,
    strlen: Vec<DefId>,
    slice_get_unchecked: Vec<DefId>,
    slice_get: Vec<DefId>,
    sliceindex_get_unchecked: Vec<DefId>,
    slice_range_fns: Vec<DefId>,
    range_next: Vec<DefId>,
    iter_next: Vec<DefId>,
    iter_len: Vec<DefId>,
    iter_is_empty: Vec<DefId>,
    as_ptr_like: Vec<DefId>,
    ptr_add: Vec<DefId>,
    branch: Vec<DefId>,
    gcd: Vec<DefId>,
    known_nonnull: Vec<DefId>,
    null_ptr: Vec<DefId>,
    index_fns: Vec<DefId>,
    eq_fns: Vec<DefId>,
}

fn init_methods(tcx: TyCtxt) -> Methods {
    let mut methods = Methods {
        len_fns: Vec::new(),
        from_raw_parts_fns: Vec::new(),
        from_raw_parts_mut_fns: Vec::new(),
        with_metadata_of_fns: Vec::new(),
        integer_wrapping_sub_fns: Vec::new(),
        with_capacity_fns: Vec::new(),
        box_alloc_ctors: Vec::new(),
        vec_ownership_transfer_fns: Vec::new(),
        checked_next_pow2: Vec::new(),
        layout_align: Vec::new(),
        split_at: Vec::new(),
        align_to_local: Vec::new(),
        iter_position: Vec::new(),
        strlen: Vec::new(),
        slice_get_unchecked: Vec::new(),
        slice_get: Vec::new(),
        sliceindex_get_unchecked: Vec::new(),
        slice_range_fns: Vec::new(),
        range_next: Vec::new(),
        iter_next: Vec::new(),
        iter_len: Vec::new(),
        iter_is_empty: Vec::new(),
        as_ptr_like: Vec::new(),
        ptr_add: Vec::new(),
        branch: Vec::new(),
        gcd: Vec::new(),
        known_nonnull: Vec::new(),
        null_ptr: Vec::new(),
        index_fns: Vec::new(),
        eq_fns: Vec::new(),
    };

    for krate in std::iter::once(rustc_public::local_crate())
        .chain(rustc_public::external_crates())
        .filter(|k| k.is_local || ["core", "std", "alloc"].iter().any(|n| *n == k.name))
    {
        for fn_def in krate.fn_defs() {
            let name = fn_def.name();
            let did = rustc_internal::internal(tcx, fn_def.def_id());

            // `Index::index` / `IndexMut::index_mut` (the `a[b]` indexing
            // sugar): matched by lang-item trait container, not by def_path.
            if let Some(assoc) = tcx.opt_associated_item(did)
                && let Some(trait_id) = assoc.trait_container(tcx)
                && (tcx.is_lang_item(trait_id, LangItem::Index) && assoc.name().as_str() == "index"
                    || tcx.is_lang_item(trait_id, LangItem::IndexMut)
                        && assoc.name().as_str() == "index_mut")
            {
                methods.index_fns.push(did);
            }

            // `PartialEq::eq` (the `a == b` comparison): matched by def_path,
            // since blanket impls (`<impl PartialEq<&B> for &A>::eq`) have no
            // `trait_container` (their assoc is not a trait-method item).
            if name.contains("PartialEq") && name.ends_with("::eq") {
                methods.eq_fns.push(did);
            }

            if name.ends_with("::len") {
                methods.len_fns.push(did);
            }
            if name.ends_with("::from_raw_parts") || name.ends_with("::from_raw_parts_mut") {
                methods.from_raw_parts_fns.push(did);
            }
            if name.ends_with("::from_raw_parts_mut") {
                methods.from_raw_parts_mut_fns.push(did);
            }
            if name.ends_with("::with_metadata_of") {
                methods.with_metadata_of_fns.push(did);
            }
            if name.ends_with("::wrapping_sub") && name.contains("::num::<impl ") {
                methods.integer_wrapping_sub_fns.push(did);
            }
            if name.ends_with("::with_capacity") && name.contains("::Vec::") {
                methods.with_capacity_fns.push(did);
            }
            if name.contains("::Box::")
                && (name.ends_with("::new")
                    || name.ends_with("::new_in")
                    || name.ends_with("::new_uninit")
                    || name.ends_with("::new_uninit_in")
                    || name.ends_with("::try_new_uninit")
                    || name.ends_with("::try_new_uninit_in"))
            {
                methods.box_alloc_ctors.push(did);
            }
            if (name.ends_with("::from_raw_parts") || name.ends_with("::from_parts"))
                && (name.contains("Vec") || name.contains("vec::"))
            {
                methods.vec_ownership_transfer_fns.push(did);
            }

            if name.ends_with("::checked_next_power_of_two") {
                methods.checked_next_pow2.push(did);
            }
            if name.ends_with("Layout::align") {
                methods.layout_align.push(did);
            }
            if name.contains("::split_at") {
                methods.split_at.push(did);
            }
            if name.ends_with("align_to_ext") || name.ends_with("align_to_mut_ext") {
                methods.align_to_local.push(did);
            }
            if name.contains("Iterator::position")
                || name.contains("Iterator::find")
                || name.contains("Iterator::rposition")
            {
                methods.iter_position.push(did);
            }
            if name == "strlen" || name.ends_with("::strlen") {
                methods.strlen.push(did);
            }
            if (name.contains("::get_unchecked") || name.contains("::get_unchecked_mut"))
                && (name.contains("::<impl [T]>::get_unchecked")
                    || name.contains("::<impl *mut [T]>::get_unchecked")
                    || name.contains("::<impl *const [T]>::get_unchecked")
                    || name.contains("::mut_ptr::get_unchecked")
                    || name.contains("::const_ptr::get_unchecked"))
            {
                methods.slice_get_unchecked.push(did);
            }
            if (name.ends_with("::get") || name.ends_with("::get_mut"))
                && (name.contains("::<impl [T]>::get")
                    || name.contains("::<impl *mut [T]>::get")
                    || name.contains("::<impl *const [T]>::get"))
            {
                methods.slice_get.push(did);
            }
            if (name.contains("::get_unchecked") || name.contains("::get_unchecked_mut"))
                && name.contains("::SliceIndex")
            {
                methods.sliceindex_get_unchecked.push(did);
            }
            if name.ends_with("slice::index::range") || name.ends_with("::slice::range") {
                methods.slice_range_fns.push(did);
            }
            // `Range::next` / `RangeInclusive::next` and their `spec_next` impls:
            // the loop variable of `for i in 0..N` is produced by these, so the
            // VM models them to carry the `0 <= i < N` bound.
            if (name.ends_with("::next") || name.ends_with("::spec_next"))
                && (name.contains("RangeIteratorImpl")
                    || name.contains("RangeInclusiveIteratorImpl")
                    || (name.contains("Iterator for") && name.contains("Range<"))
                    || (name.contains("Iterator for") && name.contains("RangeInclusive<")))
            {
                methods.range_next.push(did);
            }
            // `Iter::next` / `IterMut::next` (and the `Iterator::next` trait
            // method they forward to): the slice-iterator element accessor.
            if name.ends_with("::next")
                && (name.starts_with("Iter::")
                    || name.starts_with("IterMut::")
                    || name.contains("::Iter::")
                    || name.contains("::IterMut::")
                    || name.contains("::Iter<")
                    || name.contains("::IterMut<")
                    || name.contains("::Iterator::next"))
            {
                methods.iter_next.push(did);
            }
            // `Iter::len` / `IterMut::len` (the slice-iterator length query,
            // computed from the ptr/end_or_len fields).
            if name.ends_with("::len")
                && (name.starts_with("Iter::")
                    || name.starts_with("IterMut::")
                    || name.contains("::Iter::")
                    || name.contains("::IterMut::")
                    || name.contains("::Iter<")
                    || name.contains("::IterMut<")
                    || name.ends_with("::Iter::len")
                    || name.ends_with("::IterMut::len"))
            {
                methods.iter_len.push(did);
            }
            // `Iter::is_empty` / `IterMut::is_empty`.
            if name.ends_with("::is_empty")
                && (name.starts_with("Iter::")
                    || name.starts_with("IterMut::")
                    || name.contains("::Iter::")
                    || name.contains("::IterMut::")
                    || name.contains("::Iter<")
                    || name.contains("::IterMut<")
                    || name.ends_with("::Iter::is_empty")
                    || name.ends_with("::IterMut::is_empty"))
            {
                methods.iter_is_empty.push(did);
            }
            // `as_ptr`/`as_mut_ptr`/`as_ref`/`as_mut` (and other `as_*` casts)
            // that re-expose the pointee; used by const-byte tracing.
            if name.contains("as_ptr") || name.contains("::as_") {
                methods.as_ptr_like.push(did);
            }
            // Pointer `add` (any `::add` method).
            if name.contains("::add") {
                methods.ptr_add.push(did);
            }
            // `<Option<T> as Try>::branch` (the `?` operator on `Option`).
            // `branch` has no lang/diagnostic item; `Option` disambiguates it
            // from `<Result<T, E> as Try>::branch`.
            if name.ends_with("::branch") && name.contains("Option") {
                methods.branch.push(did);
            }
            // `gcd` const fn (const-eval integer GCD).
            if name.ends_with("::gcd") {
                methods.gcd.push(did);
            }
            // Known non-null-returning pointer methods (`into_raw` / `Box::new`
            // / `as_ptr` / `as_mut_ptr`), used by path analysis.
            if name.contains("::into_raw")
                || (name.contains("::new") && name.contains("Box"))
                || name.contains("::as_mut_ptr")
                || name.contains("::as_ptr")
            {
                methods.known_nonnull.push(did);
            }
            // Null-returning pointer methods (`null` / `null_mut`).
            if name.contains("null_mut") || (name.contains("null") && name.contains("ptr::")) {
                methods.null_ptr.push(did);
            }
        }
    }

    methods
}

macro_rules! method_fns {
    ($( $(#[$attr:meta])* $name:ident => $field:ident ,)+) => {
        $(
            $(#[$attr])*
            pub fn $name() -> &'static [DefId] {
                &METHODS
                    .get()
                    .expect("Method DefIds haven't been initialized.")
                    .$field
            }
        )+
    };
}

method_fns! {
    /// `len` query methods (`slice::len`, `str::len`, `Vec::len`, `String::len`,
    /// pointer-slice `len`, and any local re-implementation).
    len_fns => len_fns,
    /// `from_raw_parts` constructors (`slice`/`str`/`ptr`/`NonNull`/`Vec`/`String`
    /// and local re-implementations).
    from_raw_parts_fns => from_raw_parts_fns,
    /// `from_raw_parts_mut` constructors (`slice`/`ptr`/`NonNull` and local
    /// re-implementations).
    from_raw_parts_mut_fns => from_raw_parts_mut_fns,
    /// `*const T::with_metadata_of` / `*mut T::with_metadata_of` (used by
    /// `byte_add`/`byte_offset`).
    with_metadata_of_fns => with_metadata_of_fns,
    integer_wrapping_sub_fns => integer_wrapping_sub_fns,
    /// `Vec::with_capacity` (and local re-implementations).
    with_capacity_fns => with_capacity_fns,
    /// `Box::new` / `new_in` / `new_uninit` / `new_uninit_in` (and `try_` variants).
    box_alloc_ctors => box_alloc_ctors,
    /// `Vec::from_raw_parts` / `Vec::from_parts` (ownership transfer into a `Vec`).
    vec_ownership_transfer_fns => vec_ownership_transfer_fns,
}

/// The ADT `DefId` that `def_id`'s associated function belongs to (the impl's
/// `self` type), used to resolve an ADT that has no lang/diagnostic item from
/// one of its emitted methods (e.g. `slice::IterMut`).
#[cfg(not(rapx_has_public_adts))]
fn assoc_self_adt_did(tcx: TyCtxt, def_id: DefId) -> Option<DefId> {
    let ty = crate::helpers::name::get_struct_self_ty(tcx, def_id)?;
    match ty.kind() {
        rustc_middle::ty::TyKind::Adt(adt, _) => Some(adt.did()),
        _ => None,
    }
}

method_fns! {
    checked_next_pow2_fns => checked_next_pow2,
    layout_align_fns => layout_align,
    split_at_fns => split_at,
    align_to_local_fns => align_to_local,
    iter_position_fns => iter_position,
    strlen_fns => strlen,
    slice_get_unchecked_fns => slice_get_unchecked,
    slice_get_fns => slice_get,
    sliceindex_get_unchecked_fns => sliceindex_get_unchecked,
    slice_range_fns => slice_range_fns,
    range_next_fns => range_next,
    /// `Iter::next` / `IterMut::next` (and the `Iterator::next` trait method).
    iter_next_fns => iter_next,
    /// `Iter::len` / `IterMut::len`.
    iter_len_fns => iter_len,
    /// `Iter::is_empty` / `IterMut::is_empty`.
    iter_is_empty_fns => iter_is_empty,
    /// `as_ptr`/`as_mut_ptr`/`as_ref`/`as_mut` (and other `as_*` casts).
    as_ptr_like_fns => as_ptr_like,
    /// Pointer `add` methods.
    ptr_add_fns => ptr_add,
    /// `<Option<T> as Try>::branch`.
    branch_fns => branch,
    /// `gcd` const functions.
    gcd_fns => gcd,
    /// Known non-null-returning pointer methods (`into_raw` / `Box::new` /
    /// `as_ptr` / `as_mut_ptr`).
    known_nonnull_fns => known_nonnull,
    /// Null-returning pointer methods (`null` / `null_mut`).
    null_ptr_fns => null_ptr,
    /// `Index::index` / `IndexMut::index_mut` (the `a[b]` indexing sugar).
    index_fns => index_fns,
    /// `PartialEq::eq` (the `a == b` comparison).
    eq_fns => eq_fns,
}

fn init_inner(tcx: TyCtxt) -> KnownItems {
    const CRATES: &[&str] = &["core", "std", "alloc"];

    // Map every registered path — both with and without its
    // `std::`/`core::`/`alloc::` prefix — to its entry index.
    // `rustc_public::CrateDef::name()` emits the crate prefix only on newer
    // toolchains, so both forms must resolve to the same entry.
    let path_to_idx: std::collections::HashMap<&str, usize> = KNOWN_ITEM_PATHS
        .iter()
        .enumerate()
        .flat_map(|(idx, paths)| {
            paths.iter().flat_map(move |&p| {
                std::iter::once(p)
                    .chain(
                        ["std::", "core::", "alloc::"]
                            .into_iter()
                            .filter_map(move |pfx| p.strip_prefix(pfx)),
                    )
                    .map(move |q| (q, idx))
            })
        })
        .collect();

    let mut indices: IndexMap<_, _> = (0..KNOWN_ITEM_PATHS.len())
        .map(|idx| (idx, false))
        .collect();
    let mut map = IndexMap::<Box<str>, DefId>::with_capacity(KNOWN_ITEM_PATHS.len());

    let mut try_insert = |name: &str, def_id: rustc_public::DefId| {
        let Some(&idx) = path_to_idx.get(name) else {
            return;
        };
        assert_eq!(
            indices.insert(idx, true),
            Some(false),
            "DefId for {name} has been found: {:?}",
            map.get(KNOWN_ITEM_PATHS[idx][0])
        );
        // Store under the canonical (first) registered path so the `{id}()`
        // accessors — which probe the registered paths — find it regardless of
        // whether `name` carried a crate prefix.
        map.insert(
            Box::from(KNOWN_ITEM_PATHS[idx][0]),
            rustc_internal::internal(tcx, def_id),
        );
    };

    let mut loaded_crates = std::collections::HashSet::new();
    for krate in std::iter::once(rustc_public::local_crate())
        .chain(rustc_public::external_crates())
        .filter(|krate| CRATES.iter().any(|name| *name == krate.name))
    {
        loaded_crates.insert(krate.name.clone());
        for fn_def in krate.fn_defs() {
            try_insert(&fn_def.name(), fn_def.def_id());
        }
    }

    #[cfg(debug_assertions)]
    map.sort_unstable_by(|a, _, b, _| a.cmp(b));

    if KNOWN_ITEM_PATHS.len() != map.len() {
        // The reason to not make this an assertion is allowing compilation on
        // missing instrinsics, e.g. no_std crates without using alloc will never
        // have the dealloc intrinsic.
        // cc https://github.com/Artisan-Lab/RAPx/issues/190#issuecomment-3303049000
        let not_found = indices
            .iter()
            .filter_map(|(&idx, &found)| {
                if found {
                    return None;
                }
                // Only report entries whose crate was actually loaded for this
                // compilation. Entries pointing solely at unloaded crates (e.g.
                // `alloc` when verifying `core`) are expected to be absent.
                let in_loaded_crate = KNOWN_ITEM_PATHS[idx].iter().any(|p| {
                    p.split("::")
                        .next()
                        .is_some_and(|pfx| loaded_crates.contains(pfx))
                });
                in_loaded_crate.then_some(KNOWN_ITEM_PATHS[idx])
            })
            .collect::<Vec<_>>();
        if !not_found.is_empty() {
            rap_warn!(
                "Known standard-library functions are incompletely resolved.\n\
                 {} fn ids are not found: {not_found:#?}",
                not_found.len()
            );
        }
    }

    KnownItems { map }
}

macro_rules! known_items {
    ($( $(#[$attr:meta])* $id:ident : $paths:expr ,)+) => {
        const KNOWN_ITEM_PATHS: &[&[&str]] = &[$( $(#[$attr])* $paths ,)+];
        $(
            $(#[$attr])*
            pub fn $id() -> Option<DefId> {
                let map = &INIT.get().expect("Known item DefIds haven't been initialized.").map;
                for path in $paths {
                    match map.get(*path) {
                        Some(id) => return Some(*id),
                        None => ()
                    }
                }
                None
            }
        )+
    };
}

// for #![no_std] crates, intrinsics fn paths start from core instead of core.
// cc https://github.com/Artisan-Lab/RAPx/issues/190
known_items! {
    call_mut: &[
        "std::ops::FnMut::call_mut",
        "core::ops::FnMut::call_mut",
        "std::ops::function::FnMut::call_mut",
        "core::ops::function::FnMut::call_mut"
    ],
    clone: &[
        "std::clone::Clone::clone",
        "core::clone::Clone::clone"
    ],
    copy_from: &[
        "std::ptr::mut_ptr::<impl *mut T>::copy_from",
        "core::ptr::mut_ptr::<impl *mut T>::copy_from"
    ],
    copy_from_nonoverlapping: &[
        "std::ptr::mut_ptr::<impl *mut T>::copy_from_nonoverlapping",
        "core::ptr::mut_ptr::<impl *mut T>::copy_from_nonoverlapping"
    ],
    copy_to: &[
        "std::ptr::const_ptr::<impl *const T>::copy_to",
        "core::ptr::const_ptr::<impl *const T>::copy_to",
    ],
    copy_to_nonoverlapping: &[
        "std::ptr::const_ptr::<impl *const T>::copy_to_nonoverlapping",
        "core::ptr::const_ptr::<impl *const T>::copy_to_nonoverlapping"
    ],
    dealloc: &[
        "std::alloc::dealloc",
        "alloc::alloc::dealloc"
    ],
    drop: &[
        "std::mem::drop",
        "core::mem::drop",
    ],
    drop_in_place: &[
        "std::ptr::drop_in_place",
        "core::ptr::drop_in_place",
    ],
    manually_drop: &[
        "std::mem::ManuallyDrop::<T>::drop",
        "core::mem::ManuallyDrop::<T>::drop",
        "std::mem::manually_drop::ManuallyDrop::<T>::drop",
        "core::mem::manually_drop::ManuallyDrop::<T>::drop"
    ],
    replace: &[
        "std::mem::replace",
        "core::mem::replace"
    ],
    take: &[
        "std::mem::take",
        "core::mem::take"
    ],
    ptr_read: &[
        "std::ptr::read",
        "core::ptr::read"
    ],
    ptr_read_unaligned: &[
        "std::ptr::read_unaligned",
        "core::ptr::read_unaligned"
    ],
    ptr_read_volatile: &[
        "std::ptr::read_volatile",
        "core::ptr::read_volatile"
    ],
    ptr_write: &[
        "std::ptr::write",
        "core::ptr::write"
    ],
    ptr_write_unaligned: &[
        "std::ptr::write_unaligned",
        "core::ptr::write_unaligned"
    ],
    ptr_write_volatile: &[
        "std::ptr::write_volatile",
        "core::ptr::write_volatile"
    ],
    ptr_write_bytes: &[
        "std::ptr::write_bytes",
        "core::ptr::write_bytes"
    ],
    ptr_copy: &[
        "std::ptr::copy",
        "core::ptr::copy"
    ],
    ptr_copy_nonoverlapping: &[
        "std::ptr::copy_nonoverlapping",
        "core::ptr::copy_nonoverlapping"
    ],
    assume_init_read: &[
        "std::mem::MaybeUninit::<T>::assume_init_read",
        "core::mem::MaybeUninit::<T>::assume_init_read",
        "std::mem::maybe_uninit::MaybeUninit::<T>::assume_init_read",
        "core::mem::maybe_uninit::MaybeUninit::<T>::assume_init_read"
    ],
    maybe_uninit_uninit: &[
        "std::mem::MaybeUninit::<T>::uninit",
        "core::mem::MaybeUninit::<T>::uninit",
        "std::mem::maybe_uninit::MaybeUninit::<T>::uninit",
        "core::mem::maybe_uninit::MaybeUninit::<T>::uninit"
    ],
    maybe_uninit_write: &[
        "std::mem::MaybeUninit::<T>::write",
        "core::mem::MaybeUninit::<T>::write",
        "std::mem::maybe_uninit::MaybeUninit::<T>::write",
        "core::mem::maybe_uninit::MaybeUninit::<T>::write"
    ],
    maybe_uninit_as_ptr: &[
        "std::mem::MaybeUninit::<T>::as_ptr",
        "core::mem::MaybeUninit::<T>::as_ptr",
        "std::mem::maybe_uninit::MaybeUninit::<T>::as_ptr",
        "core::mem::maybe_uninit::MaybeUninit::<T>::as_ptr"
    ],
    maybe_uninit_as_mut_ptr: &[
        "std::mem::MaybeUninit::<T>::as_mut_ptr",
        "core::mem::MaybeUninit::<T>::as_mut_ptr",
        "std::mem::maybe_uninit::MaybeUninit::<T>::as_mut_ptr",
        "core::mem::maybe_uninit::MaybeUninit::<T>::as_mut_ptr"
    ],
    maybe_uninit_assume_init: &[
        "std::mem::MaybeUninit::<T>::assume_init",
        "core::mem::MaybeUninit::<T>::assume_init",
        "std::mem::maybe_uninit::MaybeUninit::<T>::assume_init",
        "core::mem::maybe_uninit::MaybeUninit::<T>::assume_init"
    ],
    maybe_uninit_assume_init_ref: &[
        "std::mem::MaybeUninit::<T>::assume_init_ref",
        "core::mem::MaybeUninit::<T>::assume_init_ref",
        "std::mem::maybe_uninit::MaybeUninit::<T>::assume_init_ref",
        "core::mem::maybe_uninit::MaybeUninit::<T>::assume_init_ref"
    ],
    maybe_uninit_assume_init_mut: &[
        "std::mem::MaybeUninit::<T>::assume_init_mut",
        "core::mem::MaybeUninit::<T>::assume_init_mut",
        "std::mem::maybe_uninit::MaybeUninit::<T>::assume_init_mut",
        "core::mem::maybe_uninit::MaybeUninit::<T>::assume_init_mut"
    ],
    mem_size_of: &[
        "std::mem::size_of",
        "core::mem::size_of"
    ],
    mem_align_of: &[
        "std::mem::align_of",
        "core::mem::align_of"
    ],
    ptr_align_offset: &[
        "std::ptr::align_offset",
        "core::ptr::align_offset"
    ],
    nonnull_align_offset: &[
        "std::ptr::NonNull::<T>::align_offset",
        "core::ptr::NonNull::<T>::align_offset",
        "std::ptr::non_null::NonNull::<T>::align_offset",
        "core::ptr::non_null::NonNull::<T>::align_offset"
    ],
    nonnull_as_ref: &[
        "std::ptr::NonNull::<T>::as_ref",
        "core::ptr::NonNull::<T>::as_ref",
        "std::ptr::non_null::NonNull::<T>::as_ref",
        "core::ptr::non_null::NonNull::<T>::as_ref"
    ],
    nonnull_as_mut: &[
        "std::ptr::NonNull::<T>::as_mut",
        "core::ptr::NonNull::<T>::as_mut",
        "std::ptr::non_null::NonNull::<T>::as_mut",
        "core::ptr::non_null::NonNull::<T>::as_mut"
    ],
    nonnull_new: &[
        "std::ptr::NonNull::<T>::new",
        "core::ptr::NonNull::<T>::new",
        "std::ptr::non_null::NonNull::<T>::new",
        "core::ptr::non_null::NonNull::<T>::new"
    ],
    nonnull_new_unchecked: &[
        "std::ptr::NonNull::<T>::new_unchecked",
        "core::ptr::NonNull::<T>::new_unchecked",
        "std::ptr::non_null::NonNull::<T>::new_unchecked",
        "core::ptr::non_null::NonNull::<T>::new_unchecked"
    ],
    const_ptr_align_offset: &[
        "std::ptr::const_ptr::<impl *const T>::align_offset",
        "core::ptr::const_ptr::<impl *const T>::align_offset"
    ],
    mut_ptr_align_offset: &[
        "std::ptr::mut_ptr::<impl *mut T>::align_offset",
        "core::ptr::mut_ptr::<impl *mut T>::align_offset"
    ],
    const_ptr_add: &[
        "std::ptr::const_ptr::<impl *const T>::add",
        "core::ptr::const_ptr::<impl *const T>::add"
    ],
    const_ptr_wrapping_add: &[
        "std::ptr::const_ptr::<impl *const T>::wrapping_add",
        "core::ptr::const_ptr::<impl *const T>::wrapping_add"
    ],
    const_ptr_sub: &[
        "std::ptr::const_ptr::<impl *const T>::sub",
        "core::ptr::const_ptr::<impl *const T>::sub"
    ],
    const_ptr_wrapping_sub: &[
        "std::ptr::const_ptr::<impl *const T>::wrapping_sub",
        "core::ptr::const_ptr::<impl *const T>::wrapping_sub"
    ],
    const_ptr_offset: &[
        "std::ptr::const_ptr::<impl *const T>::offset",
        "core::ptr::const_ptr::<impl *const T>::offset"
    ],
    const_ptr_wrapping_offset: &[
        "std::ptr::const_ptr::<impl *const T>::wrapping_offset",
        "core::ptr::const_ptr::<impl *const T>::wrapping_offset"
    ],
    const_ptr_byte_add: &[
        "std::ptr::const_ptr::<impl *const T>::byte_add",
        "core::ptr::const_ptr::<impl *const T>::byte_add"
    ],
    const_ptr_wrapping_byte_add: &[
        "std::ptr::const_ptr::<impl *const T>::wrapping_byte_add",
        "core::ptr::const_ptr::<impl *const T>::wrapping_byte_add"
    ],
    const_ptr_byte_sub: &[
        "std::ptr::const_ptr::<impl *const T>::byte_sub",
        "core::ptr::const_ptr::<impl *const T>::byte_sub"
    ],
    const_ptr_wrapping_byte_sub: &[
        "std::ptr::const_ptr::<impl *const T>::wrapping_byte_sub",
        "core::ptr::const_ptr::<impl *const T>::wrapping_byte_sub"
    ],
    const_ptr_byte_offset: &[
        "std::ptr::const_ptr::<impl *const T>::byte_offset",
        "core::ptr::const_ptr::<impl *const T>::byte_offset"
    ],
    const_ptr_wrapping_byte_offset: &[
        "std::ptr::const_ptr::<impl *const T>::wrapping_byte_offset",
        "core::ptr::const_ptr::<impl *const T>::wrapping_byte_offset"
    ],
    mut_ptr_add: &[
        "std::ptr::mut_ptr::<impl *mut T>::add",
        "core::ptr::mut_ptr::<impl *mut T>::add"
    ],
    mut_ptr_wrapping_add: &[
        "std::ptr::mut_ptr::<impl *mut T>::wrapping_add",
        "core::ptr::mut_ptr::<impl *mut T>::wrapping_add"
    ],
    mut_ptr_sub: &[
        "std::ptr::mut_ptr::<impl *mut T>::sub",
        "core::ptr::mut_ptr::<impl *mut T>::sub"
    ],
    mut_ptr_wrapping_sub: &[
        "std::ptr::mut_ptr::<impl *mut T>::wrapping_sub",
        "core::ptr::mut_ptr::<impl *mut T>::wrapping_sub"
    ],
    mut_ptr_offset: &[
        "std::ptr::mut_ptr::<impl *mut T>::offset",
        "core::ptr::mut_ptr::<impl *mut T>::offset"
    ],
    mut_ptr_wrapping_offset: &[
        "std::ptr::mut_ptr::<impl *mut T>::wrapping_offset",
        "core::ptr::mut_ptr::<impl *mut T>::wrapping_offset"
    ],
    mut_ptr_byte_add: &[
        "std::ptr::mut_ptr::<impl *mut T>::byte_add",
        "core::ptr::mut_ptr::<impl *mut T>::byte_add"
    ],
    mut_ptr_wrapping_byte_add: &[
        "std::ptr::mut_ptr::<impl *mut T>::wrapping_byte_add",
        "core::ptr::mut_ptr::<impl *mut T>::wrapping_byte_add"
    ],
    mut_ptr_byte_sub: &[
        "std::ptr::mut_ptr::<impl *mut T>::byte_sub",
        "core::ptr::mut_ptr::<impl *mut T>::byte_sub"
    ],
    mut_ptr_wrapping_byte_sub: &[
        "std::ptr::mut_ptr::<impl *mut T>::wrapping_byte_sub",
        "core::ptr::mut_ptr::<impl *mut T>::wrapping_byte_sub"
    ],
    mut_ptr_byte_offset: &[
        "std::ptr::mut_ptr::<impl *mut T>::byte_offset",
        "core::ptr::mut_ptr::<impl *mut T>::byte_offset"
    ],
    mut_ptr_wrapping_byte_offset: &[
        "std::ptr::mut_ptr::<impl *mut T>::wrapping_byte_offset",
        "core::ptr::mut_ptr::<impl *mut T>::wrapping_byte_offset"
    ],
    nonnull_add: &[
        "std::ptr::NonNull::<T>::add",
        "core::ptr::NonNull::<T>::add",
        "std::ptr::non_null::NonNull::<T>::add",
        "core::ptr::non_null::NonNull::<T>::add"
    ],
    nonnull_sub: &[
        "std::ptr::NonNull::<T>::sub",
        "core::ptr::NonNull::<T>::sub",
        "std::ptr::non_null::NonNull::<T>::sub",
        "core::ptr::non_null::NonNull::<T>::sub"
    ],
    nonnull_byte_add: &[
        "std::ptr::NonNull::<T>::byte_add",
        "core::ptr::NonNull::<T>::byte_add",
        "std::ptr::non_null::NonNull::<T>::byte_add",
        "core::ptr::non_null::NonNull::<T>::byte_add"
    ],
    nonnull_byte_sub: &[
        "std::ptr::NonNull::<T>::byte_sub",
        "core::ptr::NonNull::<T>::byte_sub",
        "std::ptr::non_null::NonNull::<T>::byte_sub",
        "core::ptr::non_null::NonNull::<T>::byte_sub"
    ],
    nonnull_offset: &[
        "std::ptr::NonNull::<T>::offset",
        "core::ptr::NonNull::<T>::offset",
        "std::ptr::non_null::NonNull::<T>::offset",
        "core::ptr::non_null::NonNull::<T>::offset"
    ],
    nonnull_byte_offset: &[
        "std::ptr::NonNull::<T>::byte_offset",
        "core::ptr::NonNull::<T>::byte_offset",
        "std::ptr::non_null::NonNull::<T>::byte_offset",
        "core::ptr::non_null::NonNull::<T>::byte_offset"
    ],
    cstr_from_ptr: &[
        "std::ffi::CStr::from_ptr",
        "core::ffi::CStr::from_ptr",
        "std::ffi::c_str::CStr::from_ptr",
        "core::ffi::c_str::CStr::from_ptr"
    ],
    cstr_from_bytes_with_nul_unchecked: &[
        "std::ffi::CStr::from_bytes_with_nul_unchecked",
        "core::ffi::CStr::from_bytes_with_nul_unchecked",
        "std::ffi::c_str::CStr::from_bytes_with_nul_unchecked",
        "core::ffi::c_str::CStr::from_bytes_with_nul_unchecked"
    ],
    cstring_from_vec_with_nul_unchecked: &[
        "std::ffi::CString::from_vec_with_nul_unchecked",
        "alloc::ffi::CString::from_vec_with_nul_unchecked",
        "std::ffi::c_str::CString::from_vec_with_nul_unchecked",
        "alloc::ffi::c_str::CString::from_vec_with_nul_unchecked"
    ],
    vec_push: &[
        "std::vec::Vec::<T, A>::push",
        "alloc::vec::Vec::<T, A>::push"
    ],
    vec_reserve: &[
        "std::vec::Vec::<T, A>::reserve",
        "alloc::vec::Vec::<T, A>::reserve"
    ],
    vec_reserve_exact: &[
        "std::vec::Vec::<T, A>::reserve_exact",
        "alloc::vec::Vec::<T, A>::reserve_exact"
    ],
    vec_shrink_to_fit: &[
        "std::vec::Vec::<T, A>::shrink_to_fit",
        "alloc::vec::Vec::<T, A>::shrink_to_fit"
    ],
    vec_shrink_to: &[
        "std::vec::Vec::<T, A>::shrink_to",
        "alloc::vec::Vec::<T, A>::shrink_to"
    ],
    vec_insert: &[
        "std::vec::Vec::<T, A>::insert",
        "alloc::vec::Vec::<T, A>::insert"
    ],
    vec_remove: &[
        "std::vec::Vec::<T, A>::remove",
        "alloc::vec::Vec::<T, A>::remove"
    ],
    vec_clear: &[
        "std::vec::Vec::<T, A>::clear",
        "alloc::vec::Vec::<T, A>::clear"
    ],
    vec_truncate: &[
        "std::vec::Vec::<T, A>::truncate",
        "alloc::vec::Vec::<T, A>::truncate"
    ],
    vec_set_len: &[
        "std::vec::Vec::<T, A>::set_len",
        "alloc::vec::Vec::<T, A>::set_len"
    ],
    box_from_raw: &[
        "std::boxed::Box::<T>::from_raw",
        "alloc::boxed::Box::<T>::from_raw"
    ],
    cstring_from_raw: &[
        "std::ffi::CString::from_raw",
        "alloc::ffi::CString::from_raw",
        "std::ffi::c_str::CString::from_raw",
        "alloc::ffi::c_str::CString::from_raw"
    ],
    arc_from_raw: &[
        "std::sync::Arc::<T>::from_raw",
        "alloc::sync::Arc::<T>::from_raw"
    ],
    rc_from_raw: &[
        "std::rc::Rc::<T>::from_raw",
        "alloc::rc::Rc::<T>::from_raw"
    ],
    box_from_raw_in: &[
        "std::boxed::Box::<T, A>::from_raw_in",
        "alloc::boxed::Box::<T, A>::from_raw_in"
    ],
    arc_from_raw_in: &[
        "std::sync::Arc::<T, A>::from_raw_in",
        "alloc::sync::Arc::<T, A>::from_raw_in"
    ],
    rc_from_raw_in: &[
        "std::rc::Rc::<T, A>::from_raw_in",
        "alloc::rc::Rc::<T, A>::from_raw_in"
    ],
    box_into_raw: &[
        "std::boxed::Box::<T>::into_raw",
        "alloc::boxed::Box::<T>::into_raw"
    ],
    box_as_ptr: &[
        "std::boxed::Box::<T, A>::as_ptr",
        "alloc::boxed::Box::<T, A>::as_ptr"
    ],
    box_as_mut_ptr: &[
        "std::boxed::Box::<T, A>::as_mut_ptr",
        "alloc::boxed::Box::<T, A>::as_mut_ptr"
    ],
    cstring_into_raw: &[
        "std::ffi::CString::into_raw",
        "alloc::ffi::CString::into_raw",
        "std::ffi::c_str::CString::into_raw",
        "alloc::ffi::c_str::CString::into_raw"
    ],
    arc_into_raw: &[
        "std::sync::Arc::<T>::into_raw",
        "alloc::sync::Arc::<T>::into_raw"
    ],
    arc_as_ptr: &[
        "std::sync::Arc::<T>::as_ptr",
        "alloc::sync::Arc::<T>::as_ptr",
        "std::sync::Arc::<T, A>::as_ptr",
        "alloc::sync::Arc::<T, A>::as_ptr"
    ],
    rc_into_raw: &[
        "std::rc::Rc::<T>::into_raw",
        "alloc::rc::Rc::<T>::into_raw"
    ],
    rc_as_ptr: &[
        "std::rc::Rc::<T>::as_ptr",
        "alloc::rc::Rc::<T>::as_ptr",
        "std::rc::Rc::<T, A>::as_ptr",
        "alloc::rc::Rc::<T, A>::as_ptr"
    ],
    vec_from_elem: &[
        "std::vec::from_elem",
        "alloc::vec::from_elem"
    ],
    vec_into_boxed_slice: &[
        "std::vec::Vec::<T, A>::into_boxed_slice",
        "alloc::vec::Vec::<T, A>::into_boxed_slice"
    ],
    slice_into_vec: &[
        "std::slice::<impl [T]>::into_vec",
        "alloc::slice::<impl [T]>::into_vec"
    ],
    slice_to_vec: &[
        "std::slice::<impl [T]>::to_vec_in::ConvertVec::to_vec",
        "alloc::slice::<impl [T]>::to_vec_in::ConvertVec::to_vec"
    ],
    #[cfg(rapx_ge_99)]
    box_assume_init_into_vec_unsafe: &[
        "std::boxed::box_assume_init_into_vec_unsafe",
        "alloc::boxed::box_assume_init_into_vec_unsafe"
    ],
    const_ptr_is_null: &[
        "std::ptr::const_ptr::<impl *const T>::is_null",
        "core::ptr::const_ptr::<impl *const T>::is_null"
    ],
    const_ptr_addr: &[
        "std::ptr::const_ptr::<impl *const T>::addr",
        "core::ptr::const_ptr::<impl *const T>::addr"
    ],
    const_ptr_cast: &[
        "std::ptr::const_ptr::<impl *const T>::cast",
        "core::ptr::const_ptr::<impl *const T>::cast"
    ],
    const_ptr_cast_mut: &[
        "std::ptr::const_ptr::<impl *const T>::cast_mut",
        "core::ptr::const_ptr::<impl *const T>::cast_mut"
    ],
    const_ptr_cast_array: &[
        "std::ptr::const_ptr::<impl *const T>::cast_array",
        "core::ptr::const_ptr::<impl *const T>::cast_array"
    ],
    const_ptr_slice_is_empty: &[
        "std::ptr::const_ptr::<impl *const [T]>::is_empty",
        "core::ptr::const_ptr::<impl *const [T]>::is_empty"
    ],
    const_ptr_slice_len: &[
        "std::ptr::const_ptr::<impl *const [T]>::len",
        "core::ptr::const_ptr::<impl *const [T]>::len"
    ],
    const_ptr_slice_as_ptr: &[
        "std::ptr::const_ptr::<impl *const [T]>::as_ptr",
        "core::ptr::const_ptr::<impl *const [T]>::as_ptr"
    ],
    mut_ptr_is_null: &[
        "std::ptr::mut_ptr::<impl *mut T>::is_null",
        "core::ptr::mut_ptr::<impl *mut T>::is_null"
    ],
    mut_ptr_addr: &[
        "std::ptr::mut_ptr::<impl *mut T>::addr",
        "core::ptr::mut_ptr::<impl *mut T>::addr"
    ],
    mut_ptr_cast: &[
        "std::ptr::mut_ptr::<impl *mut T>::cast",
        "core::ptr::mut_ptr::<impl *mut T>::cast"
    ],
    mut_ptr_cast_const: &[
        "std::ptr::mut_ptr::<impl *mut T>::cast_const",
        "core::ptr::mut_ptr::<impl *mut T>::cast_const"
    ],
    mut_ptr_cast_array: &[
        "std::ptr::mut_ptr::<impl *mut T>::cast_array",
        "core::ptr::mut_ptr::<impl *mut T>::cast_array"
    ],
    mut_ptr_slice_is_empty: &[
        "std::ptr::mut_ptr::<impl *mut [T]>::is_empty",
        "core::ptr::mut_ptr::<impl *mut [T]>::is_empty"
    ],
    mut_ptr_slice_len: &[
        "std::ptr::mut_ptr::<impl *mut [T]>::len",
        "core::ptr::mut_ptr::<impl *mut [T]>::len"
    ],
    mut_ptr_slice_as_mut_ptr: &[
        "std::ptr::mut_ptr::<impl *mut [T]>::as_mut_ptr",
        "core::ptr::mut_ptr::<impl *mut [T]>::as_mut_ptr"
    ],
    nonnull_addr: &[
        "std::ptr::NonNull::<T>::addr",
        "core::ptr::NonNull::<T>::addr",
        "std::ptr::non_null::NonNull::<T>::addr",
        "core::ptr::non_null::NonNull::<T>::addr"
    ],
    nonnull_cast: &[
        "std::ptr::NonNull::<T>::cast",
        "core::ptr::NonNull::<T>::cast",
        "std::ptr::non_null::NonNull::<T>::cast",
        "core::ptr::non_null::NonNull::<T>::cast"
    ],
    nonnull_as_ptr: &[
        "std::ptr::NonNull::<T>::as_ptr",
        "core::ptr::NonNull::<T>::as_ptr",
        "std::ptr::non_null::NonNull::<T>::as_ptr",
        "core::ptr::non_null::NonNull::<T>::as_ptr"
    ],
    nonnull_slice_is_empty: &[
        "std::ptr::NonNull::<[T]>::is_empty",
        "core::ptr::NonNull::<[T]>::is_empty",
        "std::ptr::non_null::NonNull::<[T]>::is_empty",
        "core::ptr::non_null::NonNull::<[T]>::is_empty"
    ],
    nonnull_slice_len: &[
        "std::ptr::NonNull::<[T]>::len",
        "core::ptr::NonNull::<[T]>::len",
        "std::ptr::non_null::NonNull::<[T]>::len",
        "core::ptr::non_null::NonNull::<[T]>::len"
    ],
    nonnull_slice_as_mut_ptr: &[
        "std::ptr::NonNull::<[T]>::as_mut_ptr",
        "core::ptr::NonNull::<[T]>::as_mut_ptr",
        "std::ptr::non_null::NonNull::<[T]>::as_mut_ptr",
        "core::ptr::non_null::NonNull::<[T]>::as_mut_ptr"
    ],
    slice_len: &[
        "std::slice::<impl [T]>::len",
        "core::slice::<impl [T]>::len"
    ],
    slice_is_empty: &[
        "std::slice::<impl [T]>::is_empty",
        "core::slice::<impl [T]>::is_empty"
    ],
    slice_as_ptr: &[
        "std::slice::<impl [T]>::as_ptr",
        "core::slice::<impl [T]>::as_ptr"
    ],
    slice_as_mut_ptr: &[
        "std::slice::<impl [T]>::as_mut_ptr",
        "core::slice::<impl [T]>::as_mut_ptr"
    ],
    str_len: &[
        "std::str::<impl str>::len",
        "core::str::<impl str>::len"
    ],
    str_is_empty: &[
        "std::str::<impl str>::is_empty",
        "core::str::<impl str>::is_empty"
    ],
    str_as_ptr: &[
        "std::str::<impl str>::as_ptr",
        "core::str::<impl str>::as_ptr"
    ],
    str_as_bytes: &[
        "std::str::<impl str>::as_bytes",
        "core::str::<impl str>::as_bytes"
    ],
    str_as_mut_ptr: &[
        "std::str::<impl str>::as_mut_ptr",
        "core::str::<impl str>::as_mut_ptr"
    ],
    vec_len: &[
        "std::vec::Vec::<T, A>::len",
        "alloc::vec::Vec::<T, A>::len"
    ],
    vec_is_empty: &[
        "std::vec::Vec::<T, A>::is_empty",
        "alloc::vec::Vec::<T, A>::is_empty"
    ],
    vec_as_ptr: &[
        "std::vec::Vec::<T, A>::as_ptr",
        "alloc::vec::Vec::<T, A>::as_ptr"
    ],
    vec_as_mut_ptr: &[
        "std::vec::Vec::<T, A>::as_mut_ptr",
        "alloc::vec::Vec::<T, A>::as_mut_ptr"
    ],
    string_len: &[
        "std::string::String::len",
        "alloc::string::String::len"
    ],
    string_is_empty: &[
        "std::string::String::is_empty",
        "alloc::string::String::is_empty"
    ],
    cstr_as_ptr: &[
        "std::ffi::CStr::as_ptr",
        "core::ffi::CStr::as_ptr",
        "std::ffi::c_str::CStr::as_ptr",
        "core::ffi::c_str::CStr::as_ptr"
    ],
    cstr_is_empty: &[
        "std::ffi::CStr::is_empty",
        "core::ffi::CStr::is_empty",
        "std::ffi::c_str::CStr::is_empty",
        "core::ffi::c_str::CStr::is_empty"
    ],
}

/// rustc_public DefId to internal DefId
pub fn to_internal<T: CrateDef>(val: &T, tcx: TyCtxt) -> DefId {
    rustc_internal::internal(tcx, val.def_id())
}

/// Find any drop fn. Any of these drop fns can be missing, e.g. for crates like no_std without
/// using alloc, dealloc doesn't exist.
pub fn is_drop_fn(target: DefId) -> bool {
    let drop_fn = [drop(), drop_in_place(), manually_drop(), dealloc()];
    contains(&drop_fn, target)
}

/// Whether the target `DefId` is in the given array.
pub fn contains(v: &[Option<DefId>], target: DefId) -> bool {
    v.contains(&Some(target))
}

pub(crate) fn matches_any(target: Option<DefId>, candidates: &[Option<DefId>]) -> bool {
    target.is_some_and(|id| contains(candidates, id))
}

mod classify {
    //! Standard-library API call classification helpers.
    //!
    //! Each classifier answers "what kind of operation is this call?" (pointer
    //! arithmetic, raw memory access, ownership transfer, …). Callers — the path
    //! graph, VM, alias/hazard scanner, and call-summary registry — use these to pick
    //! a modelling strategy or discharge a safety obligation.
    //!
    //! # Matching mechanism
    //!
    //! Every classifier takes a `DefId` — `fn(Option<DefId>) -> bool` for callee
    //! matching, or `fn(DefId) -> bool` for ADT *type* matching — and answers via
    //! exact set membership in [`crate::other_api`] rather than substring-matching a
    //! `def_path_str`. [`crate::other_api`] resolves the well-known `std`/`core`/`alloc`
    //! items (by lang/diagnostic item, explicit path, or — for the open-ended
    //! groups and the std-challenge suites' local re-implementations — by
    //! name-scanning `fn_defs()` at init), so a call site is matched by identity
    //! without the false positives of per-call-site name matching.

    use crate::intrinsic_api;
    use crate::other_api;
    use rustc_hir::def_id::DefId;
    use rustc_middle::ty::Ty;
    use rustc_middle::ty::TyCtxt;

    /// Whether `callee` is `Some` and matches any resolved DefId in the slice.
    fn any_def(callee: Option<DefId>, defs: &[DefId]) -> bool {
        callee.is_some_and(|c| defs.contains(&c))
    }

    // ── Ownership reconstruction ──────────────────────────────────────

    /// Whether `callee` reconstructs an owned value, taking ownership of the
    /// pointed-to memory: from a single raw pointer (`Box::from_raw`,
    /// `CString::from_raw`, `Arc::from_raw`, `Rc::from_raw`) or from a `Vec<u8>`
    /// (`CString::from_vec_with_nul_unchecked`). Distinct from
    /// [`is_from_raw_parts`], which builds a slice/`Vec` from `(ptr, len[, cap])`.
    pub fn is_ownership_reconstruction(callee: Option<DefId>) -> bool {
        other_api::matches_any(
            callee,
            &[
                other_api::box_from_raw(),
                other_api::cstring_from_raw(),
                other_api::arc_from_raw(),
                other_api::rc_from_raw(),
                other_api::box_from_raw_in(),
                other_api::arc_from_raw_in(),
                other_api::rc_from_raw_in(),
                other_api::cstring_from_vec_with_nul_unchecked(),
            ],
        )
    }

    /// Whether `callee` is `ManuallyDrop::<T>::drop` — the *manual* drop that frees
    /// the pointee's allocation without the `ManuallyDrop` wrapper's own (no-op)
    /// drop glue.
    pub fn is_manually_drop_drop(callee: Option<DefId>) -> bool {
        callee.is_some_and(|c| other_api::manually_drop() == Some(c))
    }

    /// Whether `callee` is `std::mem::drop` / `core::mem::drop` — the value drop
    /// that frees the argument's heap allocation.
    pub fn is_std_drop(callee: Option<DefId>) -> bool {
        callee.is_some_and(|c| other_api::drop() == Some(c))
    }

    /// Whether `callee` is `drop_in_place::<T>` — the MIR drop shim that drops the
    /// pointee in place and (for an owning pointee like `Box`/`Vec`) frees its
    /// heap allocation.
    pub fn is_drop_in_place(callee: Option<DefId>) -> bool {
        callee.is_some_and(|c| other_api::drop_in_place() == Some(c))
    }

    // ── Pointer extraction / cast ─────────────────────────────────────

    /// Whether `callee` produces a raw pointer (or `NonNull`) alias of its first
    /// argument: `as_ptr`/`as_mut_ptr`, `into_raw`, and pointer `cast` (incl.
    /// `cast_mut`/`cast_const`). `as_ptr_range`/`as_mut_ptr_range` are excluded
    /// because they return a `Range` of two pointers rather than a single pointer;
    /// `NonNull::new_unchecked`/`as_ref`/`as_mut` are excluded because they do not
    /// produce a raw pointer (and `new_unchecked` must not mark its result
    /// non-null, or it would hide `new_unchecked(null)` unsoundness).
    pub fn is_as_ptr(callee: Option<DefId>) -> bool {
        other_api::matches_any(
            callee,
            &[
                other_api::slice_as_ptr(),
                other_api::slice_as_mut_ptr(),
                other_api::str_as_ptr(),
                other_api::str_as_mut_ptr(),
                other_api::vec_as_ptr(),
                other_api::vec_as_mut_ptr(),
                other_api::cstr_as_ptr(),
                other_api::nonnull_as_ptr(),
                other_api::const_ptr_slice_as_ptr(),
                other_api::mut_ptr_slice_as_mut_ptr(),
                other_api::nonnull_slice_as_mut_ptr(),
                other_api::box_as_ptr(),
                other_api::box_as_mut_ptr(),
                other_api::maybe_uninit_as_ptr(),
                other_api::maybe_uninit_as_mut_ptr(),
                other_api::arc_as_ptr(),
                other_api::rc_as_ptr(),
                other_api::const_ptr_cast(),
                other_api::const_ptr_cast_mut(),
                other_api::const_ptr_cast_array(),
                other_api::mut_ptr_cast(),
                other_api::mut_ptr_cast_const(),
                other_api::mut_ptr_cast_array(),
                other_api::nonnull_cast(),
                other_api::box_into_raw(),
                other_api::cstring_into_raw(),
                other_api::arc_into_raw(),
                other_api::rc_into_raw(),
            ],
        )
    }

    /// Whether `callee` is a raw-pointer `cast`/`cast_mut`/`cast_const`. These only
    /// *reinterpret* the address — they preserve null-ness and provenance, but do
    /// not establish that the result is non-null, aligned, or points at initialized
    /// memory. Distinguished from [`is_as_ptr`] so [`is_as_ptr_valid`] can keep
    /// them on the MIR-inlining path rather than the `ReturnPointerFromArg` model
    /// (which asserts those facts).
    pub(crate) fn is_raw_ptr_cast(callee: Option<DefId>) -> bool {
        other_api::matches_any(
            callee,
            &[
                other_api::const_ptr_cast(),
                other_api::const_ptr_cast_mut(),
                other_api::const_ptr_cast_array(),
                other_api::mut_ptr_cast(),
                other_api::mut_ptr_cast_const(),
                other_api::mut_ptr_cast_array(),
            ],
        )
    }

    /// [`is_as_ptr`] restricted to the *pointer-validity-establishing* subset:
    /// `as_ptr`/`as_mut_ptr`, `into_raw`, and `NonNull::cast` — which expose a
    /// non-null, aligned, initialized backing pointer. Raw-pointer `cast`/
    /// `cast_mut`/`cast_const` are excluded because they only reinterpret the
    /// address (preserving null-ness) and are left to MIR inlining.
    pub fn is_as_ptr_valid(callee: Option<DefId>) -> bool {
        is_as_ptr(callee) && !is_raw_ptr_cast(callee)
    }

    /// `str::as_bytes`: reinterprets `&str` as `&[u8]` — same data pointer and
    /// byte length, so the result aliases the argument.
    pub fn is_str_as_bytes(callee: Option<DefId>) -> bool {
        other_api::matches_any(callee, &[other_api::str_as_bytes()])
    }

    /// The whole `assert_unsafe_precondition!` machinery: the `check_language_ub`
    /// gate, the generated `precondition_check` body, and the
    /// `#[cfg(debug_assertions)]` check helpers (`runtime_add_nowrap`,
    /// `maybe_is_aligned*`, `is_valid_allocation_size`, `maybe_is_nonoverlapping`).
    ///
    /// All of these are debug-only / ub-checks-gated and model release semantics
    /// (checks disabled), so they must be skipped rather than inlined: the gate
    /// folds to `false` (no check), and the body/helpers' divergence branches would
    /// otherwise leave pointer results uninitialized (e.g. `swap_unchecked`'s
    /// `ptr.add(b)` on the failed-check arm).
    pub fn is_ub_check(tcx: TyCtxt<'_>, callee: DefId) -> bool {
        let s = tcx.def_path_str(callee);
        s.contains("ub_checks::check_language_ub")
            || s.contains("::precondition_check")
            || s.contains("::runtime_add_nowrap")
            || s.contains("ub_checks::maybe_is_aligned")
            || s.contains("ub_checks::is_valid_allocation_size")
            || s.contains("ub_checks::maybe_is_nonoverlapping")
    }

    // ── Pointer arithmetic ────────────────────────────────────────────
    // Direction (`add` vs `sub`) and granularity (`element` vs `byte`) are two
    // orthogonal axes. Each of the four combinations is a first-class classifier
    // below; the aggregate predicates at the end are unions over a single axis,
    // for callers that only care about one dimension.

    /// Element-strided `add`/`wrapping_add` and signed `offset`/`wrapping_offset`
    /// (stride = `size_of::<T>()`). `offset_from`/`offset_from_unsigned` are *not*
    /// matched (they subtract two pointers into an `isize`).
    pub(crate) fn is_element_ptr_add(callee: Option<DefId>) -> bool {
        other_api::matches_any(
            callee,
            &[
                other_api::const_ptr_add(),
                other_api::const_ptr_wrapping_add(),
                other_api::const_ptr_offset(),
                other_api::const_ptr_wrapping_offset(),
                other_api::mut_ptr_add(),
                other_api::mut_ptr_wrapping_add(),
                other_api::mut_ptr_offset(),
                other_api::mut_ptr_wrapping_offset(),
                other_api::nonnull_add(),
                other_api::nonnull_offset(),
            ],
        )
    }

    /// Element-strided `sub`/`wrapping_sub` (stride = `size_of::<T>()`).
    pub(crate) fn is_element_ptr_sub(callee: Option<DefId>) -> bool {
        other_api::matches_any(
            callee,
            &[
                other_api::const_ptr_sub(),
                other_api::const_ptr_wrapping_sub(),
                other_api::mut_ptr_sub(),
                other_api::mut_ptr_wrapping_sub(),
                other_api::nonnull_sub(),
            ],
        )
    }

    /// Byte-granular `byte_add`/`wrapping_byte_add` and signed
    /// `byte_offset`/`wrapping_byte_offset` (stride 1).
    pub(crate) fn is_byte_ptr_add(callee: Option<DefId>) -> bool {
        other_api::matches_any(
            callee,
            &[
                other_api::const_ptr_byte_add(),
                other_api::const_ptr_wrapping_byte_add(),
                other_api::const_ptr_byte_offset(),
                other_api::const_ptr_wrapping_byte_offset(),
                other_api::mut_ptr_byte_add(),
                other_api::mut_ptr_wrapping_byte_add(),
                other_api::mut_ptr_byte_offset(),
                other_api::mut_ptr_wrapping_byte_offset(),
                other_api::nonnull_byte_add(),
                other_api::nonnull_byte_offset(),
            ],
        )
    }

    /// Byte-granular `byte_sub`/`wrapping_byte_sub` (stride 1).
    pub(crate) fn is_byte_ptr_sub(callee: Option<DefId>) -> bool {
        other_api::matches_any(
            callee,
            &[
                other_api::const_ptr_byte_sub(),
                other_api::const_ptr_wrapping_byte_sub(),
                other_api::mut_ptr_byte_sub(),
                other_api::mut_ptr_wrapping_byte_sub(),
                other_api::nonnull_byte_sub(),
            ],
        )
    }

    /// Any pointer `add` (element or byte). `offset`/`byte_offset` take a signed
    /// `isize`, so a negative offset is still classified here (the sign lives in
    /// the argument); see [`is_pointer_sub`] for the positive-count `sub` family.
    pub fn is_pointer_add(callee: Option<DefId>) -> bool {
        is_element_ptr_add(callee) || is_byte_ptr_add(callee)
    }

    /// Any pointer `sub` (element or byte): a positive count, `base - count * stride`.
    pub fn is_pointer_sub(callee: Option<DefId>) -> bool {
        is_element_ptr_sub(callee) || is_byte_ptr_sub(callee)
    }

    // ── Layout constants ──────────────────────────────────────────────

    /// Whether `callee` is the compile-time layout constant `size_of::<T>()` or
    /// `align_of::<T>()`. The runtime intrinsics (`size_of_val`, `align_of_val`,
    /// `pref_align_of`, `*_val_raw`, …) are *not* classified here.
    pub fn is_layout_constant(callee: Option<DefId>) -> bool {
        intrinsic_api::is_size_of(callee)
            || intrinsic_api::is_align_of(callee)
            || other_api::matches_any(
                callee,
                &[other_api::mem_size_of(), other_api::mem_align_of()],
            )
    }

    /// Whether `callee` is `ptr::align_offset` / `NonNull::align_offset` /
    /// `*const T::align_offset` / `*mut T::align_offset`.
    pub fn is_align_offset(callee: Option<DefId>) -> bool {
        other_api::matches_any(
            callee,
            &[
                other_api::ptr_align_offset(),
                other_api::nonnull_align_offset(),
                other_api::const_ptr_align_offset(),
                other_api::mut_ptr_align_offset(),
            ],
        )
    }

    // ── Raw pointer read / write ──────────────────────────────────────

    /// Whether `callee` writes through a raw pointer to its first argument
    /// (`ptr::write`, `write_bytes`, `write_unaligned`, `write_volatile`).
    pub fn is_ptr_write(callee: Option<DefId>) -> bool {
        other_api::matches_any(
            callee,
            &[
                other_api::ptr_write(),
                other_api::ptr_write_unaligned(),
                other_api::ptr_write_volatile(),
                other_api::ptr_write_bytes(),
            ],
        )
    }

    pub fn is_ptr_copy(callee: Option<DefId>) -> bool {
        intrinsic_api::is_copy(callee)
            || other_api::matches_any(
                callee,
                &[other_api::ptr_copy(), other_api::ptr_copy_nonoverlapping()],
            )
    }

    /// Whether `callee` reads through a raw pointer or copies memory
    /// (`ptr::read`/`read_unaligned`/`read_volatile`, `copy_to`/`copy_from`,
    /// `MaybeUninit::assume_init_read`, and intrinsics `copy`/`copy_nonoverlapping`).
    pub fn is_ptr_read(callee: Option<DefId>) -> bool {
        intrinsic_api::is_copy(callee)
            || other_api::matches_any(
                callee,
                &[
                    other_api::ptr_read(),
                    other_api::ptr_read_unaligned(),
                    other_api::ptr_read_volatile(),
                    other_api::copy_to(),
                    other_api::copy_to_nonoverlapping(),
                    other_api::copy_from(),
                    other_api::copy_from_nonoverlapping(),
                    other_api::assume_init_read(),
                ],
            )
    }

    // ── MaybeUninit ───────────────────────────────────────────────────

    /// Whether `callee` is `MaybeUninit::write`, which initializes the slot (unlike
    /// raw `ptr::write`, handled by [`is_mem_copy_or_write`]).
    pub fn is_maybe_uninit_write(callee: Option<DefId>) -> bool {
        other_api::matches_any(callee, &[other_api::maybe_uninit_write()])
    }

    /// Whether `callee` is `MaybeUninit::uninit` (a new uninitialized slot).
    pub fn is_maybe_uninit_uninit(callee: Option<DefId>) -> bool {
        other_api::matches_any(callee, &[other_api::maybe_uninit_uninit()])
    }

    /// Whether `callee` is a `MaybeUninit` "assume initialized" accessor
    /// (`assume_init`, `assume_init_read`, `assume_init_ref`, `assume_init_mut`).
    pub fn is_maybe_uninit_assume_init(callee: Option<DefId>) -> bool {
        other_api::matches_any(
            callee,
            &[
                other_api::maybe_uninit_assume_init(),
                other_api::assume_init_read(),
                other_api::maybe_uninit_assume_init_ref(),
                other_api::maybe_uninit_assume_init_mut(),
            ],
        )
    }

    /// Memory copy/write intrinsics that legitimately write through a raw pointer
    /// without requiring the target bytes to be pre-initialized (e.g. `ptr::write`,
    /// `write_bytes`, `copy_nonoverlapping`, `ptr::copy`). Used by the checker to
    /// discharge `Init`/`Typed` obligations on `MaybeUninit` targets.
    pub fn is_mem_copy_or_write(callee: Option<DefId>) -> bool {
        intrinsic_api::is_copy(callee)
            || other_api::matches_any(
                callee,
                &[
                    other_api::copy_from_nonoverlapping(),
                    other_api::copy_to_nonoverlapping(),
                    other_api::ptr_write(),
                    other_api::ptr_write_bytes(),
                ],
            )
    }

    // ── Queries and unwrap ────────────────────────────────────────────

    /// Whether `callee` is a `len` query method. Matched by `DefId` via
    /// [`crate::other_api::len_fns`], which resolves every `::len` `fn_def` in the std
    /// crates *and* the local crate — so the std-challenge suites' re-implemented
    /// `len` methods are modelled too, without substring-matching a `def_path_str`.
    pub fn is_len(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::len_fns())
    }

    // ── Slice / C-string ──────────────────────────────────────────────

    /// Whether `callee` is a `from_raw_parts` constructor (`slice`/`str`/`ptr`/
    /// `String`/`Vec`/`NonNull`). Matched by `DefId` via
    /// [`crate::other_api::from_raw_parts_fns`] (resolved from `fn_defs()`, including
    /// local re-implementations), instead of substring-matching `def_path_str`.
    pub fn is_from_raw_parts(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::from_raw_parts_fns())
    }

    /// `*const T::with_metadata_of` / `*mut T::with_metadata_of` (used by
    /// `byte_add`/`byte_offset`): re-attaches metadata onto a data address.  For a
    /// sized pointee it is a no-op cast and must preserve the pointer's provenance
    /// and non-nullness (rather than going through `from_raw_parts`, whose
    /// fresh-allocation effect would reset them).
    pub fn is_with_metadata_of(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::with_metadata_of_fns())
    }

    /// Whether `callee` is a `from_raw_parts_mut` constructor.
    pub fn is_from_raw_parts_mut(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::from_raw_parts_mut_fns())
    }

    pub fn is_cstr_from_ptr(callee: Option<DefId>) -> bool {
        other_api::matches_any(callee, &[other_api::cstr_from_ptr()])
    }

    /// `_unchecked` C-string constructors whose caller must guarantee NUL
    /// termination (`CStr::from_bytes_with_nul_unchecked`,
    /// `CString::from_vec_with_nul_unchecked`).
    pub fn is_cstr_unchecked_constructor(callee: Option<DefId>) -> bool {
        other_api::matches_any(
            callee,
            &[
                other_api::cstr_from_bytes_with_nul_unchecked(),
                other_api::cstring_from_vec_with_nul_unchecked(),
            ],
        )
    }

    // ── Vec constructors / methods ────────────────────────────────────

    pub fn is_vec_push_or_reserve(callee: Option<DefId>) -> bool {
        other_api::matches_any(
            callee,
            &[
                other_api::vec_push(),
                other_api::vec_reserve(),
                other_api::vec_reserve_exact(),
            ],
        )
    }
    pub fn is_vec_alloc_constructor(callee: Option<DefId>) -> bool {
        other_api::matches_any(callee, &[other_api::vec_from_elem()])
    }
    pub fn is_vec_from_box(callee: Option<DefId>) -> bool {
        other_api::matches_any(
            callee,
            &[
                other_api::slice_into_vec(),
                #[cfg(rapx_ge_99)]
                other_api::box_assume_init_into_vec_unsafe(),
            ],
        )
    }
    /// `alloc::alloc::exchange_malloc` (`Box::new`'s allocator on some toolchains).
    pub fn is_exchange_malloc(callee: Option<DefId>) -> bool {
        callee.is_some_and(|c| other_api::exchange_malloc() == Some(c))
    }
    /// `slice::to_vec` (`<[T]>::to_vec` via `to_vec_in::ConvertVec::to_vec`) —
    /// allocates a fresh buffer and copies the slice's elements.
    pub fn is_slice_to_vec(callee: Option<DefId>) -> bool {
        other_api::matches_any(callee, &[other_api::slice_to_vec()])
    }
    /// `Vec::with_capacity` — matched by `DefId` via
    /// [`crate::other_api::with_capacity_fns`].
    pub fn is_vec_with_capacity(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::with_capacity_fns())
    }
    /// `Box::new` / `new_in` / `new_uninit` / `new_uninit_in` (and `try_` variants)
    /// — fresh heap allocation constructors.
    pub fn is_box_alloc_ctor(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::box_alloc_ctors())
    }
    pub fn is_into_boxed_slice(callee: Option<DefId>) -> bool {
        other_api::matches_any(callee, &[other_api::vec_into_boxed_slice()])
    }

    // ── Alias-hazard classification ───────────────────────────────────
    // These are the single home for "what does this raw-pointer API do" used by the
    // alias/hazard scanner. `is_ownership_transfer` is the raw-pointer subset of
    // [`is_ownership_reconstruction`]: it excludes `from_vec_with_nul_unchecked`
    // (which consumes a `Vec<u8>` rather than a raw pointer). `Vec::from_raw_parts`
    // / `from_parts` ownership transfer is matched separately by
    // [`is_vec_ownership_transfer`].

    pub fn is_ownership_transfer(callee: Option<DefId>) -> bool {
        let Some(callee) = callee else { return false };
        is_ownership_reconstruction(Some(callee))
            && !other_api::contains(&[other_api::cstring_from_vec_with_nul_unchecked()], callee)
    }

    pub fn is_vec_ownership_transfer(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::vec_ownership_transfer_fns())
    }

    /// Whether `callee` is `NonNull::new` (the null-checked constructor).
    pub(crate) fn is_nonnull_checked_new(callee: Option<DefId>) -> bool {
        other_api::matches_any(callee, &[other_api::nonnull_new()])
    }

    /// Whether `callee` is `NonNull::new_unchecked` (the unchecked transparent
    /// wrapper). Modeled as a provenance-preserving alias so the pointer's element
    /// offset survives inlined iterator bodies (`post_inc_start`'s
    /// `new_unchecked(ptr.add(1))`); non-nullness is inherited from the source, not
    /// asserted, so `new_unchecked(null)` unsoundness is still caught.
    pub(crate) fn is_nonnull_new_unchecked(callee: Option<DefId>) -> bool {
        other_api::matches_any(callee, &[other_api::nonnull_new_unchecked()])
    }

    /// Whether `callee` is `NonNull::as_ref` or `NonNull::as_mut`.
    pub fn is_nonnull_as_ref_as_mut(callee: Option<DefId>) -> bool {
        other_api::matches_any(
            callee,
            &[other_api::nonnull_as_ref(), other_api::nonnull_as_mut()],
        )
    }

    /// Whether `callee` is `NonNull::as_mut` (produces an exclusive `&mut`).
    pub fn is_nonnull_as_mut(callee: Option<DefId>) -> bool {
        other_api::matches_any(callee, &[other_api::nonnull_as_mut()])
    }

    /// Whether `callee` is a `Vec` method that may reallocate (invalidating any
    /// outstanding raw pointers derived from it).
    pub fn is_vec_invalidating_method(callee: Option<DefId>) -> bool {
        other_api::matches_any(
            callee,
            &[
                other_api::vec_push(),
                other_api::vec_reserve(),
                other_api::vec_reserve_exact(),
                other_api::vec_shrink_to_fit(),
                other_api::vec_shrink_to(),
                other_api::vec_insert(),
                other_api::vec_remove(),
                other_api::vec_clear(),
                other_api::vec_truncate(),
                other_api::vec_set_len(),
            ],
        )
    }

    /// Whether `callee` returns ownership of an allocation as a raw pointer
    /// (`Box::into_raw`, `CString::into_raw`, `Arc::into_raw`, `Rc::into_raw`, ...).
    pub fn is_ownership_return(callee: Option<DefId>) -> bool {
        other_api::matches_any(
            callee,
            &[
                other_api::box_into_raw(),
                other_api::cstring_into_raw(),
                other_api::arc_into_raw(),
                other_api::rc_into_raw(),
            ],
        )
    }

    /// Whether `callee` is a benign, read-only use of a raw-pointer origin
    /// (`len`, `is_empty`, `is_null`, `addr`, `as_ptr`/`as_mut_ptr`, `cast`).
    pub fn is_benign_origin_use(callee: Option<DefId>) -> bool {
        other_api::matches_any(
            callee,
            &[
                other_api::const_ptr_is_null(),
                other_api::const_ptr_addr(),
                other_api::const_ptr_cast(),
                other_api::const_ptr_cast_mut(),
                other_api::const_ptr_slice_is_empty(),
                other_api::const_ptr_slice_len(),
                other_api::const_ptr_slice_as_ptr(),
                other_api::mut_ptr_is_null(),
                other_api::mut_ptr_addr(),
                other_api::mut_ptr_cast(),
                other_api::mut_ptr_cast_const(),
                other_api::mut_ptr_slice_is_empty(),
                other_api::mut_ptr_slice_len(),
                other_api::mut_ptr_slice_as_mut_ptr(),
                other_api::nonnull_addr(),
                other_api::nonnull_cast(),
                other_api::nonnull_as_ptr(),
                other_api::nonnull_slice_is_empty(),
                other_api::nonnull_slice_len(),
                other_api::nonnull_slice_as_mut_ptr(),
                other_api::slice_len(),
                other_api::slice_is_empty(),
                other_api::slice_as_ptr(),
                other_api::slice_as_mut_ptr(),
                other_api::str_len(),
                other_api::str_is_empty(),
                other_api::str_as_ptr(),
                other_api::str_as_mut_ptr(),
                other_api::vec_len(),
                other_api::vec_is_empty(),
                other_api::vec_as_ptr(),
                other_api::vec_as_mut_ptr(),
                other_api::string_len(),
                other_api::string_is_empty(),
                other_api::cstr_as_ptr(),
                other_api::cstr_is_empty(),
            ],
        )
    }

    // ── ADT type-name classifiers ─────────────────────────────────────
    // *Shape* recognizers used by the VM to model repr(transparent) wrappers and
    // fixed field layouts (`Vec` = ptr/cap/len, `slice::Iter` = ptr/end, …).
    // Matched by `DefId` (resolved in [`crate::other_api`]).

    pub fn is_std_vec(def_id: DefId) -> bool {
        other_api::vec_types().contains(&def_id)
    }
    pub fn is_std_box(def_id: DefId) -> bool {
        other_api::box_types().contains(&def_id)
    }
    pub fn is_std_cstring(def_id: DefId) -> bool {
        other_api::cstring_types().contains(&def_id)
    }
    pub fn is_std_nonnull(def_id: DefId) -> bool {
        other_api::nonnull_types().contains(&def_id)
    }
    pub fn is_maybe_uninit_type(def_id: DefId) -> bool {
        other_api::maybe_uninit_types().contains(&def_id)
    }

    /// Whether `ty` (peeling through `&` / `*mut` / `*const` / `[T]` / `[T; N]`) is
    /// `MaybeUninit<...>`, i.e. carries no validity invariant (any bit pattern is a
    /// valid value).  Shared by the VM (`init_parameters`) and the `Typed` checker.
    pub fn is_maybe_uninit_ty(ty: Ty<'_>) -> bool {
        use rustc_middle::ty::TyKind;
        let mut t = ty;
        loop {
            match t.kind() {
                TyKind::Slice(e) | TyKind::Array(e, _) => t = *e,
                TyKind::RawPtr(e, _) | TyKind::Ref(_, e, _) => t = *e,
                TyKind::Adt(adt, _) => return is_maybe_uninit_type(adt.did()),
                _ => return false,
            }
        }
    }
    pub fn is_std_iter_or_itermut(def_id: DefId) -> bool {
        other_api::iter_types().contains(&def_id)
    }
    pub fn is_std_ordering(def_id: DefId) -> bool {
        other_api::ordering_types().contains(&def_id)
    }

    // ── Arithmetic / collection-operation classifiers ─────────────────
    // Matched by `DefId` via [`other_api::OP_FNS`] (resolved from `fn_defs()`).
    // These were previously name-based in the call-summary registry; see
    // [`crate::other_api`] for the exact method-name patterns each group collects.

    pub fn is_integer_wrapping_sub_method(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::integer_wrapping_sub_fns())
    }
    pub fn is_checked_next_pow2(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::checked_next_pow2_fns())
    }
    pub fn is_layout_align(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::layout_align_fns())
    }
    pub fn is_split_at(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::split_at_fns())
    }

    // ── Open-ended operation classifiers ──────────────────────────────
    // These match the std-challenge suites' local `_ext` re-implementations and
    // generic trait-method patterns. They cannot be tied to a *closed* hard-coded
    // set, so they are resolved by name-scanning `fn_defs()` in [`crate::other_api`]
    // (which also collects the local crate's re-implementations) and matched by
    // `DefId` like the other classifiers.

    pub fn is_align_to_local(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::align_to_local_fns())
    }
    pub fn is_iter_position(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::iter_position_fns())
    }
    pub fn is_strlen(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::strlen_fns())
    }
    pub fn is_slice_get_unchecked(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::slice_get_unchecked_fns())
    }

    /// Whether `callee` is `<[T]>::get` / `<[T]>::get_mut` (the slice-side range
    /// getters returning `Option<&[T]>`).
    pub fn is_slice_get(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::slice_get_fns())
    }

    /// Whether `callee` is the `Index::index` / `IndexMut::index_mut` trait method
    /// (the `a[b]` indexing sugar).
    pub fn is_index_method(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::index_fns())
    }

    /// Whether `callee` is the `PartialEq::eq` comparison method.
    pub fn is_eq_call(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::eq_fns())
    }

    /// Whether `callee` is `SliceIndex::get_unchecked`/`get_unchecked_mut` (the
    /// trait method, whose receiver is the *index* and whose first argument is the
    /// slice pointer). Distinct from [`is_slice_get_unchecked`] (the slice-side
    /// methods whose receiver is the slice): the result aliases argument 1, not
    /// argument 0.
    pub fn is_sliceindex_get_unchecked(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::sliceindex_get_unchecked_fns())
    }

    /// Whether `callee` is `Range::next` / `RangeInclusive::next` (or their
    /// `spec_next` impls). Distinct from the slice-side getters above: the receiver
    /// is `&mut Range<A>`, and the returned element is the current `start`.
    pub fn is_range_next(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::range_next_fns())
    }

    /// Whether `callee` is a slice iterator's `next` (`Iter::next` /
    /// `IterMut::next`, or the `Iterator::next` trait method they forward to).
    pub fn is_iter_next(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::iter_next_fns())
    }

    /// Whether `callee` is a slice iterator's `len` (`Iter::len` / `IterMut::len`).
    pub fn is_iter_len(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::iter_len_fns())
    }

    /// Whether `callee` is a slice iterator's `is_empty`
    /// (`Iter::is_empty` / `IterMut::is_empty`).
    pub fn is_iter_is_empty(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::iter_is_empty_fns())
    }

    /// Whether `callee` is `<Option<T> as Try>::branch`.
    pub fn is_branch(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::branch_fns())
    }

    /// Whether `callee` is a `gcd` const fn.
    pub fn is_gcd(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::gcd_fns())
    }

    /// Whether `def_id` is `core::range::IndexRange` (or a local re-implementation).
    pub fn is_index_range(def_id: DefId) -> bool {
        other_api::index_range_types().contains(&def_id)
    }

    /// Whether `callee` is `slice::range(range, bounds)` — the range normalizer that
    /// returns `Range { start, end }` with `0 <= start <= end <= bounds.end`.
    pub fn is_slice_range(callee: Option<DefId>) -> bool {
        any_def(callee, other_api::slice_range_fns())
    }

    /// Whether `callee` is `mem::replace(dest, src)` — returns `*dest` (the old
    /// value), so the summary must deref the reference argument.
    pub fn is_mem_replace(callee: Option<DefId>) -> bool {
        other_api::matches_any(callee, &[other_api::replace()])
    }
}

pub(crate) use classify::*;
