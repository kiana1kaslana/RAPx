//! Container layout, length, and backing-allocation queries.

use rustc_middle::mir::Local;
use rustc_middle::ty::{Ty, TyKind};
use z3::ast::{Ast, Int};

use crate::helpers::mir_utils;
use crate::verify::api_classify;

use super::state::{AllocId, OffsetKind, Provenance, ValueFacts, ValueSource, VmState, VmValue};

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    /// The slice/array element count for an allocation: the materialized
    /// `slice_len`, or `size / elem_size` as a fallback for allocations created
    /// before materialization (e.g. some call effects).  Uses the symbolic
    /// element size (`size_sym_read`) so `len = (len·S) / S` cancels to `len`
    /// for a generic element type — mirroring `set_len_from_alloc`.  Returns
    /// `None` when the element type is unknown.
    pub(crate) fn slice_len_of_alloc(&self, alloc_id: AllocId) -> Option<Int<'z3>> {
        let alloc = self.alloc(alloc_id);
        if let Some(len) = alloc.slice_len() {
            return Some(len.clone());
        }
        let elem_ty = alloc.element_ty.as_ty()?;
        let elem_term = self.size_sym_read(elem_ty);
        if elem_term.simplify().as_u64() == Some(1) {
            return Some(alloc.size.clone());
        }
        Some(alloc.size.div(&elem_term))
    }

    /// The slice length of a `&[T]` / `&mut [T]` value, resolved through its
    /// provenance allocation (see [`Self::slice_len_of_alloc`]).
    pub(crate) fn slice_len_from_value(&self, val: &VmValue<'z3, 'tcx>) -> Option<Int<'z3>> {
        self.slice_len_of_alloc(val.provenance_alloc_id()?)
    }

    /// Resolve `x.len()` for a pointer whose pointee ADT carries a `len` field
    /// (e.g. `NodeRef<LeafNode>`: `len()` reads `(*ptr).len`).  Returns the
    /// pointee's `len` field term, or `None` when the pointee has no such field.
    pub(crate) fn try_adt_len_field(&self, val: &VmValue<'z3, 'tcx>) -> Option<Int<'z3>> {
        let alloc_id = val.provenance_alloc_id()?;
        let elem_ty = self.alloc(alloc_id).element_ty.as_ty()?;
        self.try_adt_len_field_at(alloc_id, elem_ty, elem_ty, &[])
    }

    /// Resolve a `len` field on `ty`, recursing into ADT sub-fields when there is
    /// no direct `len` (e.g. `String { vec: Vec { ptr, len, cap } }` resolves
    /// `String.len()` to `vec.len`).  `root_ty` stays fixed as the allocation's
    /// element type, which is how `decompose_pointee_fields` keys `MemoryContent::values`.
    fn try_adt_len_field_at(
        &self,
        alloc_id: AllocId,
        ty: Ty<'tcx>,
        root_ty: Ty<'tcx>,
        prefix: &[usize],
    ) -> Option<Int<'z3>> {
        let rustc_middle::ty::TyKind::Adt(adt_def, substs) = ty.kind() else {
            return None;
        };
        if !adt_def.is_struct() {
            return None;
        }
        let variant = adt_def.non_enum_variant();
        if let Some(len_idx) = variant
            .fields
            .iter()
            .position(|f| f.ident(self.tcx).name.to_string() == "len")
        {
            let mut path = prefix.to_vec();
            path.push(len_idx);
            return self.units[alloc_id.0].content.values
                .get(&(root_ty, path))
                .map(|v| v.z3_term.clone());
        }
        for (idx, field_def) in variant.fields.iter().enumerate() {
            let field_ty = mir_utils::field_ty(self.tcx, field_def, substs);
            if matches!(field_ty.kind(), rustc_middle::ty::TyKind::Adt(_, _)) {
                let mut path = prefix.to_vec();
                path.push(idx);
                if let Some(len) = self.try_adt_len_field_at(alloc_id, field_ty, root_ty, &path) {
                    return Some(len);
                }
            }
        }
        None
    }

    /// Resolve `len()` for `core::ops::IndexRange` (a private `{ start, end }`
    /// struct): `len() = end - start`.  The `len` field lookup above misses it
    /// because `IndexRange` has no `len` field — its `len()` computes the
    /// difference of its two private fields.
    pub(crate) fn try_index_range_len(&self, val: &VmValue<'z3, 'tcx>) -> Option<Int<'z3>> {
        let rustc_middle::ty::TyKind::Adt(adt_def, _) = val.ty.kind() else {
            return None;
        };
        if !api_classify::is_index_range(adt_def.did()) {
            return None;
        }
        let alloc_id = val.provenance_alloc_id()?;
        let view_ty = mir_utils::pointee_ty(val.ty).unwrap_or(val.ty);
        let start = self
            .units[alloc_id.0].content.values
            .get(&(view_ty, vec![0]))?
            .z3_term
            .clone();
        let end = self
            .units[alloc_id.0].content.values
            .get(&(view_ty, vec![1]))?
            .z3_term
            .clone();
        Some(Int::sub(self.z3_ctx, &[&end, &start]))
    }

    /// Resolve `len()` of a slice/ADT value: the pointee ADT's `len` field, then
    /// the materialized slice length, then `size / elem_size`.  Shared by the
    /// exec- and checker-side `Len` evaluators so the fallback chain is defined
    /// once.
    pub(crate) fn len_from_value(&self, val: &VmValue<'z3, 'tcx>) -> Option<Int<'z3>> {
        if let Some(len) = self.try_adt_len_field(val) {
            return Some(len);
        }
        if let Some(len) = self.try_index_range_len(val) {
            return Some(len);
        }
        self.slice_len_from_value(val)
    }

    /// Resolve `x.len()` for a struct `x` (e.g. `NodeRef`) whose `len()` method
    /// reads `(*x.field).len` through a `NonNull`/raw-pointer field.  Follows
    /// that field to its pointee allocation and reads the pointee's `len` field.
    pub(crate) fn try_struct_nn_len_field(
        &self,
        local: Local,
        field_path: &[usize],
        ty: Ty<'tcx>,
    ) -> Option<Int<'z3>> {
        let rustc_middle::ty::TyKind::Adt(adt_def, substs) = ty.kind() else {
            return None;
        };
        if !adt_def.is_struct() {
            return None;
        }
        let variant = adt_def.non_enum_variant();
        let mut found: Option<(usize, Ty<'tcx>)> = None;
        for (idx, field_def) in variant.fields.iter().enumerate() {
            let fty = mir_utils::field_ty(self.tcx, field_def, substs);
            if let Some(pointee) = self.find_nn_pointee(fty) {
                found = Some((idx, pointee));
                break;
            }
        }
        let (nn_idx, pointee) = found?;
        let mut path = field_path.to_vec();
        path.push(nn_idx);
        let nn_val = self.field_value(local, &path)?;
        let alloc_id = nn_val.provenance_alloc_id()?;
        let rustc_middle::ty::TyKind::Adt(pointee_adt, _) = pointee.kind() else {
            return None;
        };
        let pvariant = pointee_adt.non_enum_variant();
        let len_idx = pvariant
            .fields
            .iter()
            .position(|f| f.ident(self.tcx).name.to_string() == "len")?;
        self.units[alloc_id.0].content.values
            .get(&(pointee, vec![len_idx]))
            .map(|v| v.z3_term.clone())
    }

    /// Resolve the type of a place (`local` + field path) by walking the ADT
    /// field definitions.
    pub(crate) fn field_type_at(&self, local: Local, field_path: &[usize]) -> Option<Ty<'tcx>> {
        let mut ty = self.body().local_decls[local].ty;
        for &idx in field_path {
            let rustc_middle::ty::TyKind::Adt(adt_def, substs) = ty.kind() else {
                return None;
            };
            let variant = adt_def.non_enum_variant();
            let field_def = variant.fields.get(rustc_abi::FieldIdx::from_usize(idx))?;
            ty = mir_utils::field_ty(self.tcx, field_def, substs);
        }
        Some(ty)
    }

    /// Extract the pointee type if `ty` is a `#[repr(transparent)]`
    /// single-field raw-pointer wrapper (`NonNull<P>`) or wrapped in
    /// `Option<NonNull<P>>`. Returns `Some(P)`.
    ///
    /// Detected structurally (via `#[repr(transparent)]` + a raw-pointer field)
    /// rather than by name, so re-implemented std types in the challenge
    /// suites are modelled identically to their std counterparts.
    pub(crate) fn find_nn_pointee(&self, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
        use rustc_middle::ty::TyKind;
        match ty.kind() {
            TyKind::Adt(adt_def, substs) => {
                if let Some(pointee) = self.transparent_ptr_pointee(adt_def, substs) {
                    return Some(pointee);
                }
                if self
                    .tcx
                    .is_diagnostic_item(rustc_span::sym::Option, adt_def.did())
                    && let Some(inner) = substs.first().and_then(|s| s.as_type())
                        && let TyKind::Adt(ia, is_) = inner.kind() {
                            return self.transparent_ptr_pointee(ia, is_);
                        }
                None
            }
            _ => None,
        }
    }

    /// Pointee type of a `#[repr(transparent)]` single-field raw-pointer
    /// wrapper such as `NonNull<T>` (`struct NonNull<T> { pointer: *const T }`).
    fn transparent_ptr_pointee(
        &self,
        adt_def: &rustc_middle::ty::AdtDef,
        substs: rustc_middle::ty::GenericArgsRef<'tcx>,
    ) -> Option<Ty<'tcx>> {
        if !adt_def.repr().transparent() {
            return None;
        }
        let field = adt_def.non_enum_variant().fields.iter().next()?;
        let field_ty = mir_utils::field_ty(self.tcx, field, substs);
        match field_ty.kind() {
            rustc_middle::ty::TyKind::RawPtr(pointee, _) => Some(*pointee),
            // NonNull's field is a pattern type `*const T is !null` on newer
            // toolchains; unwrap it to the underlying raw pointer.
            rustc_middle::ty::TyKind::Pat(inner, _) => match inner.kind() {
                rustc_middle::ty::TyKind::RawPtr(pointee, _) => Some(*pointee),
                _ => None,
            },
            _ => None,
        }
    }

    /// Whether `ty` is a `#[repr(transparent)]` newtype (a single non-zero-sized
    /// field whose value *is* that field, e.g. `MaybeUninit<T>`, `ManuallyDrop<T>`,
    /// `Wrapping<T>`, `NonNull<T>`).  Construction and field reads are modelled
    /// transparently: the wrapper value is the field value itself.
    pub(crate) fn is_transparent_newtype(&self, ty: Ty<'tcx>) -> bool {
        match ty.kind() {
            rustc_middle::ty::TyKind::Adt(adt_def, _) => adt_def.repr().transparent(),
            _ => false,
        }
    }

    pub(crate) fn container_ptr_field(&self, ty: Ty<'tcx>) -> Option<Vec<usize>> {
        self.container_ptr_field_inner(ty, Vec::new(), 0)
    }

    fn container_ptr_field_inner(
        &self,
        ty: Ty<'tcx>,
        prefix: Vec<usize>,
        depth: usize,
    ) -> Option<Vec<usize>> {
        use rustc_middle::ty::TyKind;
        if depth > 4 {
            return None;
        }
        match ty.kind() {
            TyKind::Adt(adt, substs) => {
                if adt.is_enum() {
                    return None;
                }
                for (idx, field_def) in adt.non_enum_variant().fields.iter().enumerate() {
                    let field_ty =
                        mir_utils::field_ty(self.tcx, field_def, substs);
                    let mut path = prefix.clone();
                    path.push(idx);
                    if let TyKind::RawPtr(..) = field_ty.kind() {
                        return Some(path);
                    }
                    if self.find_nn_pointee(field_ty).is_some() {
                        return Some(path);
                    }
                    if let Some(found) =
                        self.container_ptr_field_inner(field_ty, path, depth + 1)
                    {
                        return Some(found);
                    }
                }
                None
            }
            _ => None,
        }
    }

    pub(crate) fn container_data_alloc(
        &self,
        header: AllocId,
        ty: Ty<'tcx>,
    ) -> Option<AllocId> {
        use rustc_middle::ty::TyKind;
        let mut view_ty = ty;
        while let TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) = view_ty.kind() {
            view_ty = *inner;
        }
        if !matches!(view_ty.kind(), TyKind::Adt(..)) {
            return None;
        }
        let path = self.container_ptr_field(view_ty)?;
        self.load_value(header, view_ty, &path)?.provenance_alloc_id()
    }

    /// The data allocation behind a container header or a slice view's header.
    /// Tries the type-driven owning field first, then falls back to scanning the
    /// header's materialized fields for the first owning pointer (covers slice
    /// views whose header `AllocId` no longer carries a type key).
    pub(crate) fn data_alloc_of(&self, header: AllocId, ty: Ty<'tcx>) -> Option<AllocId> {
        let mut data_ty = ty;
        while let TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) = data_ty.kind() {
            data_ty = *inner;
        }
        let element_ty = match data_ty.kind() {
            TyKind::Slice(element) | TyKind::Array(element, _) => Some(*element),
            _ => None,
        };
        if element_ty.is_some_and(|element| self.alloc(header).element_ty.as_ty() == Some(element)) {
            return None;
        }
        self.container_data_alloc(header, ty).or_else(|| {
            // The header → data fallback is only for local (non-external) slice
            // views. An external parameter's header carries an `i64::MAX`
            // "unbounded" size that already discharges `Allocated`, so do not
            // redirect it to the (symbolic-sized) pointee.
            if self.alloc(header).is_external() {
                None
            } else {
                self.header_data_alloc(header)
            }
        })
    }

    /// Scan a header allocation's materialized fields for the owning pointer
    /// (its provenance names the data allocation). This is the header → data
    /// fallback for slice views (whose provenance names the container header,
    /// not the data), replacing the old `slice_data` edge.
    ///
    /// Returns the provenance only when the header has *exactly one* owning
    /// pointer field. A multi-owning-pointer header (e.g. a linked list's
    /// `head`/`tail`) is ambiguous, so fall back to `None` rather than guess.
    fn header_data_alloc(&self, header: AllocId) -> Option<AllocId> {
        let mut result = None;
        for ((_, p), v) in self.units[header.0].content.values.iter() {
            if p.is_empty() {
                continue;
            }
            let Some(prov) = v.provenance_alloc_id() else {
                continue;
            };
            if result.is_some() {
                return None;
            }
            result = Some(prov);
        }
        result
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn set_container_data_field(
        &mut self,
        header: AllocId,
        ty: Ty<'tcx>,
        data_alloc: AllocId,
        base: Int<'z3>,
        elem_ty: Ty<'tcx>,
    ) -> bool {
        use rustc_middle::ty::TyKind;
        let mut view_ty = ty;
        while let TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) = view_ty.kind() {
            view_ty = *inner;
        }
        if !matches!(view_ty.kind(), TyKind::Adt(..)) {
            return false;
        }
        let Some(path) = self.container_ptr_field(view_ty) else {
            return false;
        };
        let ptr_field = VmValue {
            z3_term: base,
            ty: elem_ty,
            provenance: Some(Provenance {
                alloc_id: data_alloc,
                offset: Int::from_u64(self.z3_ctx, 0),
                offset_kind: None,
            }),
            facts: ValueFacts {
                non_null: true,
                init: true,
                in_bounds: true,
                ..ValueFacts::default()
            },
            source: ValueSource::None,
        };
        self.store_value(header, view_ty, path, ptr_field);
        true
    }

    /// The two pointer fields of an Iter/IterMut local (`[0]` = ptr, `[1]` =
    /// end_or_len), which share the same allocation.  Returns `None` when
    /// either field is missing or the two point into different allocations.
    pub(crate) fn iter_ptr_end(&self, local: Local) -> Option<(VmValue<'z3, 'tcx>, VmValue<'z3, 'tcx>)> {
        for (ptr_path, end_path) in [(&[0][..], &[1][..]), (&[0, 0][..], &[0, 1][..])] {
            let (Some(ptr), Some(end)) =
                (self.field_value(local, ptr_path), self.field_value(local, end_path))
            else {
                continue;
            };
            if ptr
                .provenance
                .as_ref()
                .zip(end.provenance.as_ref())
                .is_some_and(|(pp, ep)| pp.alloc_id == ep.alloc_id)
            {
                return Some((ptr.clone(), end.clone()));
            }
        }
        None
    }

    /// Element size of the type iterated by an Iter/IterMut pointer, symbolic
    /// (`sizeof_T`) for a generic element type so `size / elem_size` cancels.
    pub(crate) fn iter_elem_size(&self, ptr: &VmValue<'z3, 'tcx>) -> Int<'z3> {
        let elem_ty = match ptr.ty.kind() {
            TyKind::Adt(_, substs) => substs.first().and_then(|s| s.as_type()),
            TyKind::RawPtr(ty, _) | TyKind::Ref(_, ty, _) => Some(*ty),
            _ => None,
        };
        if elem_ty.is_some_and(|ty| matches!(ty.kind(), TyKind::Param(_)))
            && let Some(alloc_id) = ptr.provenance_alloc_id()
            && let Some(concrete) = self.alloc(alloc_id).element_ty.as_ty()
            && !matches!(concrete.kind(), TyKind::Param(_))
        {
            return self.size_sym_read(concrete);
        }
        match elem_ty {
            Some(t) => self.size_sym_read(t),
            None => Int::from_u64(self.z3_ctx, 1),
        }
    }

    /// Element count from two pointer fields sharing the same allocation:
    /// `(end.offset - ptr.offset) / elem_size`. When both pointers carry an
    /// element-structured offset (`OffsetKind::Element`, or the base), the
    /// count is computed element-wise (`end_elem - ptr_elem`) so the
    /// `(end·S - ptr·S)/S` division is avoided for a generic element size `S`.
    pub(crate) fn iter_len_from_ptrs(
        &self,
        ptr: &VmValue<'z3, 'tcx>,
        end: &VmValue<'z3, 'tcx>,
    ) -> Option<Int<'z3>> {
        let pp = ptr.provenance.as_ref()?;
        let ep = end.provenance.as_ref()?;
        if pp.alloc_id != ep.alloc_id {
            return None;
        }
        let elem_of = |p: &Provenance<'z3>| -> Option<Int<'z3>> {
            match &p.offset_kind {
                Some(OffsetKind::Element { index, .. }) => Some(index.clone()),
                Some(OffsetKind::Field) | None => Some(Int::from_u64(self.z3_ctx, 0)),
                _ => None,
            }
        };
        if let (Some(pe), Some(ee)) = (elem_of(pp), elem_of(ep)) {
            return Some(Int::sub(self.z3_ctx, &[&ee, &pe]));
        }
        let sz = self.iter_elem_size(ptr);
        let diff = Int::sub(self.z3_ctx, &[&ep.offset, &pp.offset]);
        Some(diff.div(&sz))
    }

    /// Remaining element count of an Iter/IterMut from its two pointer fields.
    /// When a tracked pointer offset exists (`iter_ptr_offset`), prefers the
    /// compact `base_len - offset` form; otherwise falls back to
    /// `(end.offset - ptr.offset) / elem_size`.
    pub(crate) fn iter_remaining_len_from_ptrs(
        &self,
        ptr: &VmValue<'z3, 'tcx>,
        end: &VmValue<'z3, 'tcx>,
        iter_owner: Option<&(AllocId, Int<'z3>)>,
    ) -> Option<Int<'z3>> {
        let ep = end.provenance.as_ref()?;
        let sz = self.iter_elem_size(ptr);
        if let Some((_, offset, base_len_elem)) = iter_owner
            .and_then(|id| self.constraints.term_caches.iter_ptr_offset.get(id))
        {
            let base_len = base_len_elem.clone().unwrap_or_else(|| ep.offset.div(&sz));
            let zero = Int::from_u64(self.z3_ctx, 0);
            Some(
                offset
                    .gt(&base_len)
                    .ite(&zero, &Int::sub(self.z3_ctx, &[&base_len, offset])),
            )
        } else {
            self.iter_len_from_ptrs(ptr, end)
        }
    }

    /// Apply a `ReturnRange` effect: model `slice::range(range, bounds)`
    /// returning `Range { start, end }` with `0 <= start <= end <= bounds.end`.
    /// The `bounds` argument is a `RangeTo<usize>` whose field 0 carries the
    /// slice length; the returned `Range<usize>` fields are fresh symbols bound
    /// by the range invariant.
    pub(crate) fn apply_range_effect(
        &mut self,
        bounds_arg: usize,
        args: &[VmValue<'z3, 'tcx>],
        caller_arg_locals: &[Option<Local>],
        dest: Local,
    ) {
        let dest_ty = self.body().local_decls[dest].ty;
        let TyKind::Adt(adt, substs) = dest_ty.kind() else {
            return;
        };
        let variant = adt.non_enum_variant();
        let field_ty = |idx: usize| -> Ty<'tcx> {
            variant
                .fields
                .iter()
                .nth(idx)
                .map(|f| mir_utils::field_ty(self.tcx, f, substs))
                .unwrap_or(dest_ty)
        };

        // Resolve `bounds.end` (the slice length): prefer the materialized
        // field 0 of the `RangeTo<usize>` argument, falling back to the
        // argument's own term.
        let mut len_term = None;
        if let Some(l) = caller_arg_locals.get(bounds_arg).copied().flatten()
            && let Some(fv) = self.field_value(l, &[0]) {
                len_term = Some(fv.z3_term.clone());
            }
        let len_term = len_term.or_else(|| args.get(bounds_arg).map(|v| v.z3_term.clone()));
        let Some(len_term) = len_term else {
            return;
        };

        let start = self.fresh_int(&format!("range_start_{}", dest.as_usize()));
        let end = self.fresh_int(&format!("range_end_{}", dest.as_usize()));
        let zero = Int::from_u64(self.z3_ctx, 0);
        self.constraints.assertions.push(start.ge(&zero));
        self.constraints.assertions.push(start.le(&end));
        self.constraints.assertions.push(end.le(&len_term));

        let start_val = VmValue::new(start, field_ty(0));
        let end_val = VmValue::new(end, field_ty(1));
        self.set_field_value(dest, vec![0], start_val);
        self.set_field_value(dest, vec![1], end_val);
    }
}
