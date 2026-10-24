//! Symbolic arithmetic and layout constraints used by MIR transfer rules.

use rustc_middle::mir::{BinOp, Operand, UnOp};
use z3::ast::{Ast, Bool, Int};

use crate::helpers::mir_utils;
use crate::other_api;

use super::state::{VmState, VmValue};

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    /// Inject layout constraints (>= 1) for generic AlignOf/SizeOf constants.
    pub(crate) fn inject_layout_constraints(&mut self, operand: &Operand<'tcx>, val: &VmValue<'z3, 'tcx>) {
        if let Operand::Constant(constant) = operand {
            let text = format!("{:?}", constant.const_);
            if mir_utils::const_int_from_debug(&text).is_none() {
                let is_align_or_size = text.starts_with("AlignOf(") || text.starts_with("SizeOf(");
                if is_align_or_size {
                    let one = Int::from_u64(self.z3_ctx, 1);
                    self.constraints.assertions.push(val.z3_term.ge(&one));
                }
            }
        }
    }

    /// HACK: `slice::align_to_offsets` computes its element split via
    /// `const { gcd(size_of::<T>(), size_of::<U>()) }`. The recursive `gcd`
    /// const fn cannot be inlined, so the VM would otherwise model the result as
    /// a fresh, unconstrained constant and lose the one fact that makes the
    /// proof go through: the gcd *divides* both sizes. That divisibility is
    /// what turns `us = sizeof_T / gcd` / `ts = sizeof_U / gcd` into exact
    /// divisions, giving `us * sizeof_U == ts * sizeof_T` (both the lcm) and
    /// hence `us_len * sizeof_U <= len * sizeof_T`. Detect the `gcd` const
    /// block and re-establish `gcd`'s key consequences as path conditions. This
    /// is a targeted workaround for a missing general property of recursive
    /// const fns, not an `align_to`-specific effect.
    pub(crate) fn try_emit_gcd_divisibility(&mut self, operand: &Operand<'tcx>, val: &VmValue<'z3, 'tcx>) {
        let Operand::Constant(constant) = operand else {
            return;
        };
        let rustc_middle::mir::Const::Unevaluated(uneval, _) = constant.const_ else {
            return;
        };
        // Cheap gate: only a *promoted* const block can be a `gcd` const.
        let def_name = self.tcx.def_path_str(uneval.def);
        if !def_name.contains("::{constant") {
            return;
        }
        let body = self.tcx.mir_for_ctfe(uneval.def);
        let is_gcd = body.basic_blocks.iter().any(|bb| {
            if let rustc_middle::mir::TerminatorKind::Call { func, .. } = &bb.terminator().kind
                && let Some(did) = mir_utils::dep_callee_def_id(func) {
                    return other_api::is_gcd(Some(did));
                }
            false
        });
        if !is_gcd || uneval.args.len() < 2 {
            return;
        }
        let a = self.size_sym(uneval.args.type_at(0));
        let b = self.size_sym(uneval.args.type_at(1));
        let g = &val.z3_term;
        let zero = Int::from_u64(self.z3_ctx, 0);
        // `g = gcd(a, b)`:
        // 1. g divides both a and b.
        self.constraints.assertions.push(a.rem(g)._eq(&zero));
        self.constraints.assertions.push(b.rem(g)._eq(&zero));
        // 2. the lcm identity `(a / g) * b == (b / g) * a`. Emitting it directly
        //    (rather than letting Z3 derive it from the divisibility, which its
        //    incomplete nonlinear-integer solver cannot do reliably) is what
        //    makes `us * sizeof_U == ts * sizeof_T` — and hence
        //    `us_len * sizeof_U <= len * sizeof_T` — provable.
        let a_div_g = a.div(g);
        let b_div_g = b.div(g);
        let lhs = Int::mul(self.z3_ctx, &[&a_div_g, &b]);
        let rhs = Int::mul(self.z3_ctx, &[&b_div_g, &a]);
        self.constraints.assertions.push(lhs._eq(&rhs));
    }

    /// `Some(align)` when `align` is non-trivial (≠ 1); `None` for a byte
    /// alignment, which carries no alignment guarantee.
    pub(crate) fn non_trivial_align(align: Int<'z3>) -> Option<Int<'z3>> {
        (align.simplify().as_u64() != Some(1)).then_some(align)
    }

    /// The provenance allocation's alignment, when it is non-trivial (≠ 1).
    pub(crate) fn alloc_align_of(&self, val: &VmValue<'z3, 'tcx>) -> Option<Int<'z3>> {
        val.provenance
            .as_ref()
            .map(|p| self.alloc(p.alloc_id).align.clone())
            .and_then(Self::non_trivial_align)
    }

    /// Assert the Euclidean division identity and its bounds for `Div`/`Rem`:
    ///   `lhs == (lhs/rhs)*rhs + lhs%rhs  ∧  lhs%rhs >= 0`
    /// plus `(lhs/rhs)*rhs <= lhs` directly for robustness.  This lets later
    /// checks prove `(x/N)*N <= x` and `x%N >= 0`.
    ///
    /// `term` must be the *same* Z3 term returned by `eval_binary_op` (the
    /// quotient), not a separate `lhs.div(rhs)` call, so the axiom constrains
    /// the term used in subsequent operations.
    pub(crate) fn emit_div_rem_axioms(
        &mut self,
        op: BinOp,
        term: &Int<'z3>,
        lhs: &Int<'z3>,
        rhs: &Int<'z3>,
    ) {
        let quot = if matches!(op, BinOp::Div) {
            term
        } else {
            &lhs.div(rhs)
        };
        let rem = lhs.rem(rhs);
        let mul_term = Int::mul(self.z3_ctx, &[quot, rhs]);
        let sum_term = Int::add(self.z3_ctx, &[&mul_term, &rem]);
        self.constraints.assertions.push(lhs._eq(&sum_term));
        let zero = Int::from_u64(self.z3_ctx, 0);
        self.constraints.assertions.push(rem.ge(&zero));
        // Remainder and quotient bounds help prove length constraints involving
        // % and / in the SMT solver.
        if rhs.as_u64().is_none_or(|r| r >= 1) {
            self.constraints.assertions.push(rem.lt(rhs));
        }
        self.constraints.assertions.push(rem.le(lhs));
        self.constraints.assertions.push(quot.ge(&zero));
        // Direct inequality: (lhs/rhs)*rhs <= lhs
        self.constraints.assertions.push(mul_term.le(lhs));
        // Quotient strict bound: for rhs >= 2 and lhs >= 2,
        // quot + 1 <= lhs (hence quot < lhs). E.g. X/2 < X for X>1.
        if rhs.as_u64().is_some_and(|r| r >= 2) {
            let one = Int::from_u64(self.z3_ctx, 1);
            let qp1 = Int::add(self.z3_ctx, &[quot, &one]);
            // qp1 <= lhs is equivalent to quot < lhs for integers
            self.constraints.assertions.push(qp1.le(lhs));
        } else {
            // For rhs >= 1: quot <= lhs
            if rhs.as_u64().is_some_and(|r| r >= 1) {
                self.constraints.assertions.push(quot.le(lhs));
            }
        }
    }


    /// Encode a boolean condition as the integer `1`/`0`.
    fn bool_as_int(&self, cond: &Bool<'z3>) -> Int<'z3> {
        cond.ite(&Int::from_u64(self.z3_ctx, 1), &Int::from_u64(self.z3_ctx, 0))
    }

    /// Negate a Z3 integer (`0 - val`).
    fn negate(&self, val: &Int<'z3>) -> Int<'z3> {
        let zero = Int::from_u64(self.z3_ctx, 0);
        Int::sub(self.z3_ctx, &[&zero, val])
    }

    pub(crate) fn eval_binary_op(&mut self, op: BinOp, lhs: &Int<'z3>, rhs: &Int<'z3>) -> Int<'z3> {
        match op {
            BinOp::Add | BinOp::AddWithOverflow | BinOp::AddUnchecked => {
                Int::add(self.z3_ctx, &[lhs, rhs])
            }
            BinOp::Sub | BinOp::SubWithOverflow | BinOp::SubUnchecked => {
                // `intrinsics::unchecked_sub(0, n)` lowers to `0 - n`; normalize it
                // to a unary negation `-n` so `apply_pointer_add`'s single-child
                // detection recovers the positive count (`ptr.sub(n)`).
                if lhs.as_u64() == Some(0) {
                    -rhs.clone()
                } else {
                    Int::sub(self.z3_ctx, &[lhs, rhs])
                }
            }
            BinOp::Mul | BinOp::MulWithOverflow | BinOp::MulUnchecked => {
                // `us_len = (len / ts) * us`: a non-exact division result times
                // an exact gcd quotient.  Model the product as a fresh symbol
                // and emit its byte bound `us_len * sizeof_U <= len * sizeof_T`
                // directly, so the later `from_raw_parts_mut` InBound check
                // (`us_len * sizeof_U`) stays degree-2 rather than the
                // degree-3 `div * us * sizeof_U` that Z3's NIA cannot rewrite.
                if let Some((div_lhs, div_rhs)) = self.constraints.term_caches.div_roots.get(lhs)
                    && let Some(us_dividend) = self.constraints.term_caches.exact_div_roots.get(rhs)
                        && let Some(ts_dividend) = self.constraints.term_caches.exact_div_roots.get(div_rhs)
                        {
                            let us_len = self.fresh_int("us_len");
                            self.constraints
                                .assertions
                                .push(us_len._eq(&Int::mul(self.z3_ctx, &[lhs, rhs])));
                            let byte_len = Int::mul(self.z3_ctx, &[&us_len, ts_dividend]);
                            let byte_bound = Int::mul(self.z3_ctx, &[div_lhs, us_dividend]);
                            self.constraints.assertions.push(byte_len.le(&byte_bound));
                            return us_len;
                        }
                Int::mul(self.z3_ctx, &[lhs, rhs])
            }
            BinOp::Div => {
                // An *exact* division (`lhs % rhs == 0` known) is represented as
                // a fresh variable rather than the `lhs / rhs` term. The caller
                // still emits the Euclidean identity `lhs == quot*rhs + rem`
                // (with `rem == 0` from the divisibility), so the fresh variable
                // satisfies `quot*rhs == lhs` linearly. This avoids the *nested*
                // division (`x / (b/gcd)`) that Z3's nonlinear solver can't
                // handle, leaving only degree-2 products that `nlsat` handles
                // far more reliably. General (any exact division), not a
                // per-function effect.
                let zero = Int::from_u64(self.z3_ctx, 0);
                let exact = self
                    .constraints
                    .assertions
                    .iter()
                    .any(|c| *c == lhs.rem(rhs)._eq(&zero));
                if exact {
                    let q = self.fresh_int("exact_div");
                    self.constraints.term_caches.exact_div_roots.insert(q.clone(), lhs.clone());
                    q
                } else {
                    // A *non-exact* division is likewise a fresh variable (the
                    // caller's Euclidean identity `lhs == q*rhs + rem` links it
                    // back), so a later `(len/ts) * us` product stays a degree-2
                    // product of two symbols instead of a `div` term that Z3's
                    // nonlinear solver cannot combine with a multiplier.
                    let q = self.fresh_int("div");
                    self.constraints.term_caches.div_roots.insert(q.clone(), (lhs.clone(), rhs.clone()));
                    q
                }
            }
            BinOp::Rem => lhs.rem(rhs),
            BinOp::Eq => self.bool_as_int(&lhs._eq(rhs)),
            BinOp::Ne => self.bool_as_int(&lhs._eq(rhs).not()),
            BinOp::Lt => self.bool_as_int(&lhs.lt(rhs)),
            BinOp::Le => self.bool_as_int(&lhs.le(rhs)),
            BinOp::Gt => self.bool_as_int(&lhs.gt(rhs)),
            BinOp::Ge => self.bool_as_int(&lhs.ge(rhs)),
            BinOp::Offset => Int::add(self.z3_ctx, &[lhs, rhs]),
            BinOp::BitAnd => {
                let result = self.fresh_int("binop");
                // BitAnd only clears bits, so it never increases a non-negative
                // value: result <= lhs.
                self.constraints.assertions.push(result.le(lhs));
                // When the mask (rhs) is a non-negative constant, the result is
                // also bounded by it: `x & c <= c` (e.g. `rhs & 31 <= 31`).
                // This lets `(rhs & (BITS - 1)) < BITS` be discharged. The
                // mask may be a folded expression (`SubWithOverflow(BITS, 1)`),
                // so `simplify()` is used to recover its constant value.
                if rhs.simplify().as_u64().is_some() {
                    self.constraints.assertions.push(result.le(rhs));
                }
                if self.constraints.term_caches.not_mask_terms.contains(rhs) {
                    // rhs is a two's-complement mask `!(align-1) == -align`,
                    // so `align = -rhs`. The result of `x & !(align-1)` is
                    // `x` rounded down to a multiple of `align` (i.e. align_up
                    // of the pre-incremented value).
                    let zero = Int::from_u64(self.z3_ctx, 0);
                    let align = Int::sub(self.z3_ctx, &[&zero, rhs]);
                    self.constraints.assertions.push(result.rem(&align)._eq(&zero));
                    let one = Int::from_u64(self.z3_ctx, 1);
                    let addr = Int::add(self.z3_ctx, &[lhs, rhs, &one]);
                    self.constraints.assertions.push(result.ge(&addr));
                }
                result
            }
            BinOp::BitOr => {
                let result = self.fresh_int("binop");
                let zero = Int::from_u64(self.z3_ctx, 0);
                // Bitwise OR only sets bits, so the result is non-zero whenever
                // either operand is non-zero.  Emit an implication (rather than
                // `result >= lhs`, which is only valid for non-negative values)
                // so `NonZero` bit-or methods discharge their `!= 0` obligation
                // for both signed and unsigned instantiations.
                self.constraints.assertions
                    .push(lhs._eq(&zero).not().implies(&result._eq(&zero).not()));
                self.constraints.assertions
                    .push(rhs._eq(&zero).not().implies(&result._eq(&zero).not()));
                result
            }
            _ => self.fresh_int("binop"),
        }
    }

    pub(crate) fn eval_unary_op(&mut self, op: UnOp, val: &Int<'z3>, is_bool: bool) -> Int<'z3> {
        match op {
            UnOp::Not => {
                if is_bool {
                    let zero = Int::from_u64(self.z3_ctx, 0);
                    let one = Int::from_u64(self.z3_ctx, 1);
                    val._eq(&zero).ite(&one, &zero)
                } else {
                    // Two's-complement bitwise NOT: !x == -x - 1.
                    let one = Int::from_u64(self.z3_ctx, 1);
                    let result = Int::sub(self.z3_ctx, &[&self.negate(val), &one]);
                    self.constraints.term_caches.not_mask_terms.insert(result.clone());
                    result
                }
            }
            UnOp::Neg => self.negate(val),
            UnOp::PtrMetadata => self.fresh_int("ptr_metadata"),
        }
    }

}
