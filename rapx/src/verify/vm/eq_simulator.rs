//! Exact `PartialEq::eq` models for calls whose MIR is unavailable.
//!
//! A model must describe the returned boolean on both branches. In particular,
//! equality never writes its operands or makes a fact true unconditionally.

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BinOp, Local, Operand, Rvalue, StatementKind};
use rustc_middle::ty::TyKind;
use z3::ast::{Ast, Bool, Int};

use super::state::{AllocKind, ValueSource, VmState, VmValue};
use crate::helpers::mir_utils;

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    pub(crate) fn try_simulate_eq(
        &mut self,
        callee: Option<DefId>,
        args: &[VmValue<'z3, 'tcx>],
        destination: Local,
    ) -> bool {
        let Some(callee) = callee else { return false };
        if !matches!(
            self.tcx.def_path_str(callee).as_str(),
            "core::cmp::PartialEq::eq" | "std::cmp::PartialEq::eq"
        ) || args.len() != 2
            || !matches!(self.body().local_decls[destination].ty.kind(), TyKind::Bool)
        {
            return false;
        }

        let Some(condition) = self
            .scalar_eq(&args[0], &args[1])
            .or_else(|| self.byte_slice_eq(&args[0], &args[1]))
        else {
            return false;
        };
        let one = Int::from_u64(self.z3_ctx, 1);
        let zero = Int::from_u64(self.z3_ctx, 0);
        let mut result = VmValue::new(condition.ite(&one, &zero), self.tcx.types.bool);
        result.source = ValueSource::Comparison {
            lhs: None,
            rhs: None,
            op: BinOp::Eq,
            cond: condition,
        };
        self.set_local(destination, result);
        true
    }

    /// A reference to a primitive scalar compares its stored value, not its
    /// address. Float equality is excluded because NaN is not equal to itself.
    fn scalar_eq(
        &self,
        left: &VmValue<'z3, 'tcx>,
        right: &VmValue<'z3, 'tcx>,
    ) -> Option<Bool<'z3>> {
        let left_prov = left.provenance.as_ref()?;
        let right_prov = right.provenance.as_ref()?;
        if left_prov.offset.simplify().as_u64() != Some(0)
            || right_prov.offset.simplify().as_u64() != Some(0)
        {
            return None;
        }
        let ty = self.alloc(left_prov.alloc_id).element_ty.as_ty()?;
        if ty != self.alloc(right_prov.alloc_id).element_ty.as_ty()?
            || !matches!(
                ty.kind(),
                TyKind::Uint(_) | TyKind::Int(_) | TyKind::Bool | TyKind::Char
            )
        {
            return None;
        }
        let left_value = self.load_value(left_prov.alloc_id, ty, &[])?;
        let right_value = self.load_value(right_prov.alloc_id, ty, &[])?;
        Some(left_value.z3_term._eq(&right_value.z3_term))
    }

    /// Compare a tracked `[u8]` view with a fully materialized constant byte
    /// array. The result is `len == N && bytes[0..N] == constant`.
    fn byte_slice_eq(
        &self,
        left: &VmValue<'z3, 'tcx>,
        right: &VmValue<'z3, 'tcx>,
    ) -> Option<Bool<'z3>> {
        self.byte_slice_const_eq(left, right)
            .or_else(|| self.byte_slice_const_eq(right, left))
    }

    fn byte_slice_const_eq(
        &self,
        slice: &VmValue<'z3, 'tcx>,
        constant: &VmValue<'z3, 'tcx>,
    ) -> Option<Bool<'z3>> {
        let slice_id = slice.provenance_alloc_id()?;
        let slice_alloc = self.alloc(slice_id);
        if slice_alloc.element_ty.as_ty() != Some(self.tcx.types.u8)
            || !matches!(slice_alloc.kind, AllocKind::Slice { .. })
            || slice.provenance.as_ref()?.offset.simplify().as_u64() != Some(0)
        {
            return None;
        }
        let bytes = self.constant_bytes(constant)?;
        let byte_len = bytes.len();
        let len = self.slice_len_of_alloc(slice_id)?;
        let mut conditions = vec![len._eq(&Int::from_u64(self.z3_ctx, byte_len as u64))];
        for (offset, byte) in bytes.iter().enumerate() {
            if !self.is_byte_init(slice_id, offset) {
                return None;
            }
            let index = Int::from_u64(self.z3_ctx, offset as u64);
            conditions.push(
                self.byte_read(slice_id, &index)
                    ._eq(&Int::from_u64(self.z3_ctx, *byte as u64)),
            );
        }
        Some(Bool::and(
            self.z3_ctx,
            &conditions.iter().collect::<Vec<_>>(),
        ))
    }

    fn constant_bytes(&self, value: &VmValue<'z3, 'tcx>) -> Option<Vec<u8>> {
        if let ValueSource::ConstBytes(bytes) = &value.source {
            return Some(bytes.clone());
        }
        // Sliced paths can bind a promoted constant as a symbolic call
        // argument, bypassing the `Use` transfer that carries ConstBytes.
        // Recover it only by matching that exact symbolic constant to its MIR
        // operand in a live caller frame.
        let bodies = std::iter::once(self.root_body()).chain(
            self.caller_frames
                .iter()
                .chain(std::iter::once(&self.current_frame))
                .filter_map(|frame| {
                    frame.body.or_else(|| {
                        self.tcx
                            .is_mir_available(frame.current_def_id)
                            .then(|| self.tcx.optimized_mir(frame.current_def_id))
                    })
                }),
        );
        for body in bodies {
            for block in body.basic_blocks.iter() {
                for statement in &block.statements {
                    let StatementKind::Assign(assign) = &statement.kind else {
                        continue;
                    };
                    let Rvalue::Use(Operand::Constant(constant), ..) = &assign.1 else {
                        continue;
                    };
                    if self.symbolic_const_term(&constant.const_) == value.z3_term
                        && let Some(bytes) = mir_utils::const_operand_bytes(
                            self.tcx,
                            &Operand::Constant(constant.clone()),
                        )
                    {
                        return Some(bytes);
                    }
                }
            }
        }
        None
    }
}
