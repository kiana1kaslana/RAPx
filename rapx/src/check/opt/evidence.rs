//! Conservative, body-local evidence for optimization candidates.
//!
//! A graph ancestor is not a value proof. Track single-definition MIR values
//! instead, and reject writes, mutable/raw aliases, joins and unknown callees.
//! Facts describe *all* bytes of a value; UTF-8 does not survive arbitrary slicing.
use crate::compat::Spanned;
use rustc_abi::Size;
use rustc_hir::def_id::DefId;
#[cfg(rapx_const_ext)]
use rustc_middle::ty::consts::ConstExt;
use rustc_middle::{
    mir::{
        AggregateKind, Body, BorrowKind, ConstOperand, ConstValue, Local, Operand, Place,
        ProjectionElem, Rvalue, StatementKind, TerminatorKind,
        interpret::{AllocId, GlobalAlloc, alloc_range},
    },
    ty::{self, Ty, TyCtxt, TypingEnv},
};
use rustc_span::Span;

crate::def_paths! {
    str_as_bytes: "str::as_bytes",
    string_as_bytes: "std::string::String::as_bytes",
    string_into_bytes: "std::string::String::into_bytes",
    slice_to_vec: "slice::to_vec",
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ByteFact {
    Unknown,
    Ascii,
    Utf8,
}

impl ByteFact {
    fn from_bytes(bytes: &[u8]) -> Self {
        if bytes.is_ascii() {
            Self::Ascii
        } else if std::str::from_utf8(bytes).is_ok() {
            Self::Utf8
        } else {
            Self::Unknown
        }
    }

    pub fn valid_utf8(self) -> bool {
        matches!(self, Self::Ascii | Self::Utf8)
    }
}

#[derive(Clone, Copy)]
enum Definition<'a, 'tcx> {
    Value(&'a Rvalue<'tcx>),
    Call(DefId, &'a [Spanned<Operand<'tcx>>]),
}

pub struct ByteEvidence<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    env: TypingEnv<'tcx>,
    definitions: Vec<Vec<Definition<'a, 'tcx>>>,
    invalidated: Vec<bool>,
    visiting: Vec<bool>,
    cache: Vec<Option<ByteFact>>,
    as_bytes: [DefId; 2],
    into_bytes: DefId,
    to_vec: DefId,
}

impl<'a, 'tcx> ByteEvidence<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId, body: &'a Body<'tcx>) -> Self {
        let n = body.local_decls.len();
        let paths = DEFPATHS.get_or_init(|| DefPaths::new(&tcx));
        let mut this = Self {
            tcx,
            body,
            env: TypingEnv::post_analysis(tcx, def_id),
            definitions: vec![Vec::new(); n],
            invalidated: vec![false; n],
            visiting: vec![false; n],
            cache: vec![None; n],
            as_bytes: [
                paths.str_as_bytes.last_def_id(),
                paths.string_as_bytes.last_def_id(),
            ],
            into_bytes: paths.string_into_bytes.last_def_id(),
            to_vec: paths.slice_to_vec.last_def_id(),
        };
        for block in body.basic_blocks.iter() {
            if matches!(
                block.terminator().kind,
                TerminatorKind::InlineAsm { .. } | TerminatorKind::Yield { .. }
            ) {
                this.invalidated.fill(true);
            }
            for statement in &block.statements {
                if let StatementKind::Assign(assignment) = &statement.kind {
                    let (place, value) = &**assignment;
                    if place.projection.is_empty() {
                        this.definitions[place.local.as_usize()].push(Definition::Value(value));
                    } else {
                        this.invalidated[place.local.as_usize()] = true;
                    }
                    match value {
                        Rvalue::Ref(_, BorrowKind::Mut { .. }, place)
                        | Rvalue::RawPtr(_, place) => {
                            this.invalidated[place.local.as_usize()] = true;
                        }
                        _ => {}
                    }
                }
            }
            if let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &block.terminator().kind
            {
                let idx = destination.local.as_usize();
                if !destination.projection.is_empty() {
                    this.invalidated[idx] = true;
                } else if let ty::FnDef(id, _) = func.ty(&body.local_decls, tcx).kind() {
                    this.definitions[idx].push(Definition::Call(*id, args));
                } else {
                    this.invalidated[idx] = true;
                }
            }
        }
        this
    }

    pub fn operand(&mut self, operand: &Operand<'tcx>) -> ByteFact {
        match operand {
            Operand::Constant(c) => self.constant(c),
            Operand::Copy(place) | Operand::Move(place) => self.place(*place),
            _ => ByteFact::Unknown,
        }
    }

    fn place(&mut self, place: Place<'tcx>) -> ByteFact {
        let fact = self.local(place.local);
        if place
            .projection
            .iter()
            .all(|p| matches!(p, ProjectionElem::Deref))
        {
            fact
        } else if place.projection.iter().all(|p| {
            matches!(
                p,
                ProjectionElem::Deref
                    | ProjectionElem::Index(_)
                    | ProjectionElem::ConstantIndex { .. }
                    | ProjectionElem::Subslice { .. }
            )
        }) && fact == ByteFact::Ascii
        {
            // An arbitrary byte subset of ASCII is still ASCII. This is NOT
            // true for UTF-8 (e.g. taking one byte of a multibyte code point).
            ByteFact::Ascii
        } else {
            ByteFact::Unknown
        }
    }

    fn local(&mut self, local: Local) -> ByteFact {
        let idx = local.as_usize();
        if self.invalidated[idx] || self.visiting[idx] {
            return ByteFact::Unknown;
        }
        if let Some(fact) = self.cache[idx] {
            return fact;
        }
        self.visiting[idx] = true;
        let defs = self.definitions[idx].clone();
        let mut fact = match defs.as_slice() {
            [Definition::Value(value)] => self.value(value),
            [Definition::Call(id, args)]
                if self.as_bytes.contains(id) || *id == self.into_bytes =>
            {
                args.first().map_or(ByteFact::Unknown, |arg| {
                    let fact = self.operand(&arg.node);
                    if fact == ByteFact::Ascii {
                        fact
                    } else {
                        ByteFact::Utf8
                    }
                })
            }
            [Definition::Call(id, args)] if *id == self.to_vec => args
                .first()
                .map_or(ByteFact::Unknown, |arg| self.operand(&arg.node)),
            _ => ByteFact::Unknown,
        };
        // Rust's str invariant supplies UTF-8, but never ASCII.
        if fact == ByteFact::Unknown && is_string(self.body.local_decls[local].ty) {
            fact = ByteFact::Utf8;
        }
        self.visiting[idx] = false;
        self.cache[idx] = Some(fact);
        fact
    }

    fn value(&mut self, value: &Rvalue<'tcx>) -> ByteFact {
        match value {
            Rvalue::Use(op, ..) => self.operand(op),
            Rvalue::Ref(_, BorrowKind::Shared, place) => self.place(*place),
            Rvalue::Cast(_, op, target)
                if is_byte_ref(op.ty(&self.body.local_decls, self.tcx)) && is_byte_ref(*target) =>
            {
                self.operand(op)
            }
            Rvalue::Repeat(op, _) => {
                if self.operand(op) == ByteFact::Ascii {
                    ByteFact::Ascii
                } else {
                    ByteFact::Unknown
                }
            }
            Rvalue::Aggregate(kind, operands) if matches!(**kind, AggregateKind::Array(_)) => {
                // Validate the complete ordered sequence when all elements are
                // constants; otherwise only the compositional ASCII fact holds.
                let bytes: Option<Vec<_>> = operands
                    .iter()
                    .map(|op| {
                        if let Operand::Constant(c) = op {
                            self.constant_byte(c)
                        } else {
                            None
                        }
                    })
                    .collect();
                if let Some(bytes) = bytes {
                    ByteFact::from_bytes(&bytes)
                } else if operands
                    .iter()
                    .all(|op| self.operand(op) == ByteFact::Ascii)
                {
                    ByteFact::Ascii
                } else {
                    ByteFact::Unknown
                }
            }
            _ => ByteFact::Unknown,
        }
    }

    fn constant_byte(&self, c: &ConstOperand<'tcx>) -> Option<u8> {
        if c.const_.ty() != self.tcx.types.u8 {
            return None;
        }
        u8::try_from(c.const_.try_eval_bits(self.tcx, self.env)?).ok()
    }

    fn constant(&self, c: &ConstOperand<'tcx>) -> ByteFact {
        if let Some(byte) = self.constant_byte(c) {
            return if byte.is_ascii() {
                ByteFact::Ascii
            } else {
                ByteFact::Unknown
            };
        }
        self.constant_bytes(c)
            .map_or(ByteFact::Unknown, ByteFact::from_bytes)
    }

    fn constant_bytes(&self, c: &ConstOperand<'tcx>) -> Option<&'tcx [u8]> {
        let ty = c.const_.ty();
        let value = c.const_.eval(self.tcx, self.env, c.span).ok()?;
        match (ty.kind(), value) {
            (ty::Ref(_, inner, ty::Mutability::Not), ConstValue::Slice { alloc_id, meta })
                if is_byte_slice(*inner) =>
            {
                self.read_bytes(alloc_id, Size::ZERO, meta)
            }
            (ty::Ref(_, inner, ty::Mutability::Not), ConstValue::Scalar(ptr)) => {
                let ty::Array(element, len) = inner.kind() else {
                    return None;
                };
                if *element != self.tcx.types.u8 {
                    return None;
                }
                #[cfg(rapx_scalar_to_pointer_interp_result)]
                let ptr = ptr.to_pointer(&self.tcx).discard_err()?;
                #[cfg(not(rapx_scalar_to_pointer_interp_result))]
                let ptr = ptr.to_pointer(&self.tcx);
                let (prov, offset) = ptr.into_pointer_or_addr().ok()?.prov_and_relative_offset();
                self.read_bytes(prov.alloc_id(), offset, len.try_to_target_usize(self.tcx)?)
            }
            (ty::Array(element, len), ConstValue::Indirect { alloc_id, offset })
                if *element == self.tcx.types.u8 =>
            {
                self.read_bytes(alloc_id, offset, len.try_to_target_usize(self.tcx)?)
            }
            // Unknown layouts and unresolved/static allocations are deliberately
            // not inspected using the diagnostic-only pretty-printing helpers.
            _ => None,
        }
    }

    fn read_bytes(&self, id: AllocId, offset: Size, len: u64) -> Option<&'tcx [u8]> {
        let GlobalAlloc::Memory(memory) = self.tcx.global_alloc(id) else {
            return None;
        };
        let allocation = memory.inner();
        if offset.bytes().checked_add(len)? > allocation.size().bytes() {
            return None;
        }
        allocation
            .get_bytes_strip_provenance(&self.tcx, alloc_range(offset, Size::from_bytes(len)))
            .ok()
    }
}

fn is_byte_slice(ty: Ty<'_>) -> bool {
    matches!(ty.kind(), ty::Str)
        || matches!(ty.kind(), ty::Slice(element) if matches!(element.kind(), ty::Uint(ty::UintTy::U8)))
}

fn is_byte_ref(ty: Ty<'_>) -> bool {
    matches!(ty.kind(), ty::Ref(_, inner, ty::Mutability::Not)
        if is_byte_slice(*inner)
        || matches!(inner.kind(), ty::Array(element, _) if matches!(element.kind(), ty::Uint(ty::UintTy::U8))))
}

fn is_string(ty: Ty<'_>) -> bool {
    match ty.kind() {
        ty::Str => true,
        ty::Ref(_, inner, ty::Mutability::Not) => is_string(*inner),

        _ => false,
    }
}

/// Inspect the actual arguments of one MIR call, rather than reconstructing
/// them from a destination local that may aggregate several assignments.
pub fn direct_call<'a, 'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    block: &'a rustc_middle::mir::BasicBlockData<'tcx>,
) -> Option<(DefId, &'a [Spanned<Operand<'tcx>>], Span)> {
    let terminator = block.terminator();
    let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
        return None;
    };
    let ty::FnDef(id, _) = func.ty(&body.local_decls, tcx).kind() else {
        return None;
    };
    Some((*id, args, terminator.source_info.span))
}
