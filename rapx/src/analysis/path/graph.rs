use super::PathTree;
use crate::compat::{FxHashMap, FxHashSet};
use crate::def_ids::other_api;
use crate::helpers::mir_utils;
use crate::graphs::{
    cfg::{CfgBlock, ControlFlowGraph},
    scc::{Scc, SccInfo},
};
use rustc_middle::{
    mir::{
        AggregateKind, BasicBlock, BinOp, Body, Local, Operand, ProjectionElem, Rvalue,
        StatementKind, SwitchTargets, Terminator, TerminatorKind, UnOp, UnwindAction,
    },
    ty::{Instance, TyCtxt, TyKind, TypingEnv},
};
use rustc_span::def_id::DefId;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use crate::limit::{
    LOCAL_INLINE_BLOCK_LIMIT, SCC_MAX_DEPTH, SCC_MAX_PATH_LEN, SCC_MAX_SEEN_PATHS,
    SCC_PATH_CACHE_LIMIT, WHOLE_CFG_PATH_DEPTH_LIMIT,
};

/// Check whether the current entry→entry sub-path introduces a new block
/// *sequence* (not just new blocks).  Different branch choices inside the SCC
/// produce different sequences even when all block IDs have already been seen,
/// e.g. `if i % 2 == 0 { A } else { B }` alternates between two paths through
/// the same set of blocks on successive loop iterations.
fn check_postfix_segment(
    path: &[usize],
    enter: usize,
    segment_counts: &mut FxHashMap<Vec<usize>, usize>,
    max_repeats: usize,
) -> bool {
    let segment = extract_segment(path, enter);
    let count = segment_counts.entry(segment).or_insert(0);
    *count += 1;
    *count == 1 || *count - 1 <= max_repeats
}

fn extract_segment(path: &[usize], enter: usize) -> Vec<usize> {
    let prev_pos = path[..path.len() - 1]
        .iter()
        .rposition(|&node| node == enter)
        .unwrap_or(0);
    path[prev_pos + 1..path.len() - 1].to_vec()
}

#[derive(Clone, Debug)]
/// A single enumerated acyclic path through an SCC region.
///
/// `blocks` is the ordered sequence of MIR block indices from the SCC entry
/// to the last block before exiting. The last block may have multiple CFG
/// successors outside the SCC (e.g. a `SwitchInt` branching to different
/// out-of-SCC targets), which are stored in `exit_successors`.
///
/// For example, in a loop with `switch x { A => loop_body, B => done1, C => done2 }`,
/// the corresponding `SccPath` would have `exit_successors = [done1, done2]`
/// — the DFS forks recursively into each of these when constructing whole-CFG paths.
pub struct SccPath {
    pub blocks: Vec<usize>,
    pub exit_successors: Vec<usize>,
}

/// Per-block facts collected during construction for path reachability
/// analysis: which locals are assigned, and the origin of each local's value.
#[derive(Clone, Debug, Default)]
pub struct BlockFacts {
    pub assigned_locals: Vec<usize>,
    /// Maps a local to the origin of its value.
    pub origin: FxHashMap<usize, LocalOrigin>,
}
/// The right-hand operand of a sum/comparison: a constant or a local.
#[derive(Clone, Copy, Debug)]
pub enum Rhs {
    /// A compile-time constant.
    Const(usize),
    /// A local.
    Local(usize),
}

/// The single MIR expression that defined a local's value.
#[derive(Clone, Debug)]
pub enum Expr {
    /// `dest = lhs + rhs`.
    Add { lhs: usize, rhs: Rhs },
    /// `dest = src % divisor`.
    Rem { src: usize, divisor: usize },
    /// `dest = !src`.
    Not { src: usize },
    /// `dest = lhs & rhs` (a boolean conjunction).
    And { lhs: usize, rhs: usize },
    /// `dest = lhs <op> rhs` (`Lt`/`Le`/`Gt`/`Ge`/`Eq`/`Ne`).
    Cmp { op: BinOp, lhs: usize, rhs: Rhs },
}

/// The origin of a local's value: a constant, a copy of another local, an
/// expression result, or a provably non-null pointer.
#[derive(Clone, Debug)]
pub enum LocalOrigin {
    /// `dest` is the given constant value.
    Const(usize),
    /// `dest` is a copy of another local.
    Copy(usize),
    /// `dest` is an expression result.
    Expr(Expr),
    /// `dest` is a provably non-null pointer.
    NonNull,
}

impl LocalOrigin {
    /// The copied-from local, if this is a copy origin.
    fn as_copy(&self) -> Option<&usize> {
        match self {
            LocalOrigin::Copy(src) => Some(src),
            _ => None,
        }
    }

    /// The constant value, if this is a constant origin.
    fn as_const(&self) -> Option<&usize> {
        match self {
            LocalOrigin::Const(val) => Some(val),
            _ => None,
        }
    }
}

/// Encode a `(local, field_index)` pair into a single `usize`.
const AGGREGATE_FIELD_MULT: usize = 256;
const AGGREGATE_FIELD_SENTINEL: usize = 1 << (usize::BITS as usize - 1);

fn encode_aggregate_field(local: usize, field: usize) -> usize {
    debug_assert!(field < AGGREGATE_FIELD_MULT);
    AGGREGATE_FIELD_SENTINEL | (local * AGGREGATE_FIELD_MULT + field)
}

fn decode_aggregate_field(encoded: usize) -> Option<(usize, usize)> {
    if encoded & AGGREGATE_FIELD_SENTINEL == 0 {
        return None;
    }
    let raw = encoded & !AGGREGATE_FIELD_SENTINEL;
    Some((raw / AGGREGATE_FIELD_MULT, raw % AGGREGATE_FIELD_MULT))
}

fn first_field_projection(place: &rustc_middle::mir::Place<'_>) -> Option<usize> {
    for proj in place.projection.iter() {
        if let rustc_middle::mir::ProjectionElem::Field(field, _) = proj {
            return Some(field.as_usize());
        }
    }
    None
}

/// Enum discriminant metadata used by [`check_switch_transition`].
///
/// `source_of` maps a discriminant local to the ADT local it was read from
/// (via `Rvalue::Discriminant`).  `variant_count_of` tracks the number of
/// variants for each ADT local, used to determine whether a `SwitchInt`
/// otherwise-target is uniquely determined.
#[derive(Clone, Debug, Default)]
pub struct DiscriminantInfo {
    pub source_of: FxHashMap<usize, usize>,
    pub variant_count_of: FxHashMap<usize, usize>,
}

/// Path-sensitive facts (constant values, relational bounds, slice lengths)
/// tracked while enumerating a single path.
#[derive(Clone, Default)]
pub(crate) struct ConstraintSet {
    /// `local -> concrete value` (or `usize::MAX` for the known-nonnull sentinel).
    consts: FxHashMap<usize, usize>,
    /// `lhs -> [(rhs, strict)]`: `lhs < rhs` when `strict`, else `lhs <= rhs`.
    bounds: FxHashMap<usize, Vec<(usize, bool)>>,
    /// `len_local -> (start, end)`: `len_local == end - start`.
    lengths: FxHashMap<usize, (usize, usize)>,
}

/// CFG augmented with per-block facts and discriminant metadata
/// for path reachability analysis.
///
/// `PathGraph` wraps a `ControlFlowGraph` and adds block-indexed data
/// that track assignments, constants, and copy chains.  These are used by
/// [`check_transition`](PathGraph::check_transition) to update a set of
/// discriminant constraints while traversing the CFG, enabling early
/// pruning of infeasible `SwitchInt` branches during path enumeration.
#[derive(Clone)]
pub struct PathGraph<'tcx> {
    pub cfg: ControlFlowGraph<'tcx>,
    pub block_info: Vec<BlockFacts>,
    pub disc_info: DiscriminantInfo,
    /// Global store: maps encoded `(local, field_idx)` to source local from Aggregates.
    pub aggregate_field_sources: FxHashMap<usize, usize>,
    /// Global store: maps `dest` to `src` for pointer-cast chains.
    pub cast_chains: FxHashMap<usize, usize>,
    /// Global store: maps `_dest` to the referent local of `_dest = &*referent`.
    pub reborrow_referents: FxHashMap<usize, usize>,
    /// Global store: maps `_dest` to encoded `(base, field_idx)` from field-projection copies.
    pub field_projection_source: FxHashMap<usize, usize>,
    /// Per-inlined-callee argument binding: maps the callee's entry block
    /// (global index) to the caller's argument locals and destination local.
    pub inline_bindings: FxHashMap<usize, InlineBinding>,
    /// Per-inlined-callee parent: entry block (global index) → the `DefId` of
    /// the caller whose `Call` was inlined at that entry.
    pub inline_parents: FxHashMap<usize, DefId>,
    /// Caller blocks whose `Call` terminator was inlined (their successor edge
    /// now leads into a callee). The slicer skips these calls.
    pub inlined_call_blocks: FxHashSet<usize>,
    /// Per-function local-index namespace: `def_id` → base offset. The root
    /// caller uses base `0`; every inlined callee gets a fresh base so its MIR
    /// locals do not clash with the caller's in the flat constraint maps
    /// (`block_info`, `disc_info`, `cast_chains`, …). A constraint key `k` in
    /// the namespace of `def_id` denotes MIR local `k - base`.
    local_bases: FxHashMap<DefId, usize>,
    /// Next unused local-namespace base (monotonic counter).
    next_local_base: usize,
}

/// Argument/return binding recorded when a callee CFG is inlined.
#[derive(Clone, Debug)]
pub struct InlineBinding {
    /// Caller argument locals (callee param `_i+1` ← `arg_locals[i]`).
    pub arg_locals: Vec<usize>,
    /// Constant argument values: `(param, value)` for a `Const` argument that
    /// has no local (`callee param `_param` ← const `value``).
    pub arg_consts: Vec<(usize, u64)>,
    /// Callee parameters bound to an `offset_of!` const argument (a symbolic
    /// field offset, not a concrete `u64`).  Preserved so the VM can mark the
    /// value as a `FieldOffset` (keeping `Align` dischargeable) instead of
    /// leaving the parameter as a fresh `unknown`.
    pub arg_field_offsets: Vec<usize>,
    /// Caller destination local (receives the callee's `_0`).
    pub dest_local: usize,
}

/// Scan a function's MIR and collect its per-block constant/discriminant
/// metadata and global source maps, remapping every MIR local `l` to
/// `local_base + l`. The root caller uses base `0`; inlined callees use a
/// fresh base so their locals never collide with the caller's in the flat
/// constraint maps (see [`PathGraph::local_bases`]).
#[allow(clippy::type_complexity)]
fn build_function_info<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    local_base: usize,
    body: &Body<'tcx>,
) -> (
    Vec<BlockFacts>,
    DiscriminantInfo,
    FxHashMap<usize, usize>,
    FxHashMap<usize, usize>,
    FxHashMap<usize, usize>,
    FxHashMap<usize, usize>,
) {
    let basicblocks = &body.basic_blocks;
    let mut block_info = Vec::new();
    let mut disc_info = DiscriminantInfo::default();
    let mut aggregate_field_sources: FxHashMap<usize, usize> = FxHashMap::default();
    let mut field_projection_source: FxHashMap<usize, usize> = FxHashMap::default();
    let mut cast_chains: FxHashMap<usize, usize> = FxHashMap::default();
    let mut reborrow_referents: FxHashMap<usize, usize> = FxHashMap::default();

    for i in 0..basicblocks.len() {
        let bb = &basicblocks[BasicBlock::from(i)];
        let mut info = BlockFacts::default();

        for stmt in &bb.statements {
            if let StatementKind::Assign(assign) = &stmt.kind {
                let (place, rvalue) = &**assign;
                let dest = local_base + place.local.as_usize();
                // Writing through (*ptr).field doesn't reassign ptr itself,
                // so ptr's constraint should not be cleared.
                let is_deref = place
                    .projection
                    .iter()
                    .any(|p| matches!(p, ProjectionElem::Deref));
                if !is_deref
                    && !info.assigned_locals.contains(&dest) {
                        info.assigned_locals.push(dest);
                    }
                match rvalue {
                    Rvalue::Use(Operand::Constant(c), ..) => {
                        let typing_env = TypingEnv::post_analysis(tcx, def_id);
                        let val = match c.const_.ty().kind() {
                            TyKind::Bool => c
                                .const_
                                .try_eval_bool(tcx, typing_env)
                                .map(|b| if b { 1 } else { 0 }),
                            TyKind::Int(_) | TyKind::Uint(_) => {
                                c.const_.try_eval_bits(tcx, typing_env).map(|v| v as usize)
                            }
                            _ => None,
                        };
                        if let Some(val) = val {
                            info.origin.insert(dest, LocalOrigin::Const(val));
                        }
                    }
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..) => {
                        let src_local = local_base + src.local.as_usize();
                        if let Some(field_proj) = first_field_projection(src) {
                            let encoded = encode_aggregate_field(src_local, field_proj);
                            field_projection_source.insert(dest, encoded);
                        }
                        info.origin.insert(dest, LocalOrigin::Copy(src_local));
                    }
                    Rvalue::Discriminant(rv_place) => {
                        let src_local = local_base + rv_place.local.as_usize();
                        disc_info.source_of.insert(dest, src_local);
                        if let std::collections::hash_map::Entry::Vacant(e) = disc_info.variant_count_of.entry(src_local) {
                            let src_ty = body.local_decls[rv_place.local].ty;
                            if let TyKind::Adt(adt_def, _) = src_ty.kind() {
                                let num = adt_def.variants().len();
                                if num > 0 {
                                    e.insert(num);
                                }
                            }
                        }
                    }
                    Rvalue::Aggregate(kind, operands) => {
                        if let AggregateKind::Adt(_, _, _, _, _) = kind.as_ref() {
                            let agg_local = local_base + place.local.as_usize();
                            for (field_idx, operand) in operands.iter().enumerate() {
                                if let Operand::Copy(src) | Operand::Move(src) = operand {
                                    let key = encode_aggregate_field(agg_local, field_idx);
                                    let src_local = local_base + src.local.as_usize();
                                    aggregate_field_sources.insert(key, src_local);
                                }
                            }
                        }
                        let discr = match kind.as_ref() {
                            AggregateKind::Adt(_, variant_idx, _, _, _) => Some(variant_idx.as_usize()),
                            _ => None,
                        };
                        if let Some(discr) = discr {
                            info.origin.insert(dest, LocalOrigin::Const(discr));
                            if let std::collections::hash_map::Entry::Vacant(e) = disc_info.variant_count_of.entry(dest) {
                                let dest_ty = body.local_decls[place.local].ty;
                                if let TyKind::Adt(adt_def, _) = dest_ty.kind() {
                                    let num = adt_def.variants().len();
                                    if num > 0 {
                                        e.insert(num);
                                    }
                                }
                            }
                        }
                    }
                    Rvalue::BinaryOp(BinOp::AddWithOverflow, operands) => {
                        let (lhs, rhs): (&Operand<'_>, &Operand<'_>) =
                            (&operands.0, &operands.1);
                        if let Some(lhs_local) = match lhs {
                            Operand::Copy(l) | Operand::Move(l) if l.projection.is_empty() => {
                                Some(local_base + l.local.as_usize())
                            }
                            Operand::Copy(l) | Operand::Move(l) => first_field_projection(l)
                                .map(|f| encode_aggregate_field(local_base + l.local.as_usize(), f)),
                            _ => None,
                        } {
                            let rhs_kind = match rhs {
                                Operand::Constant(c) => {
                                    let typing_env = TypingEnv::post_analysis(tcx, def_id);
                                    c.const_
                                        .try_eval_bits(tcx, typing_env)
                                        .map(|v| Rhs::Const(v as usize))
                                }
                                Operand::Copy(r) | Operand::Move(r)
                                    if r.projection.is_empty() =>
                                {
                                    Some(Rhs::Local(local_base + r.local.as_usize()))
                                }
                                _ => None,
                            };
                            if let Some(rhs_kind) = rhs_kind {
                                info.origin.insert(dest, LocalOrigin::Expr(Expr::Add { lhs: lhs_local, rhs: rhs_kind }));
                            }
                        }
                    }
                    Rvalue::BinaryOp(op, operands)
                        if matches!(
                            op,
                            BinOp::Lt
                                | BinOp::Le
                                | BinOp::Gt
                                | BinOp::Ge
                                | BinOp::Eq
                                | BinOp::Ne
                                | BinOp::BitAnd
                        ) =>
                    {
                        let (lhs, rhs): (&Operand<'_>, &Operand<'_>) =
                            (&operands.0, &operands.1);
                        let lhs_local = match lhs {
                            Operand::Copy(l) | Operand::Move(l) if l.projection.is_empty() => {
                                Some(local_base + l.local.as_usize())
                            }
                            _ => None,
                        };
                        if let Some(lhs_local) = lhs_local {
                            let rhs_kind = match rhs {
                                Operand::Constant(c) => {
                                    let typing_env = TypingEnv::post_analysis(tcx, def_id);
                                    c.const_
                                        .try_eval_bits(tcx, typing_env)
                                        .map(|v| Rhs::Const(v as usize))
                                }
                                Operand::Copy(r) | Operand::Move(r)
                                    if r.projection.is_empty() =>
                                {
                                    Some(Rhs::Local(local_base + r.local.as_usize()))
                                }
                                _ => None,
                            };
                            let Some(rhs_kind) = rhs_kind else {
                                continue;
                            };
                            if matches!(op, BinOp::BitAnd) {
                                // `dest = lhs & rhs`: only a boolean conjunction
                                // (and thus resolvable) when `dest` is a bool and
                                // `rhs` is a local.
                                if let Rhs::Local(rhs_local) = rhs_kind
                                    && matches!(body.local_decls[place.local].ty.kind(), TyKind::Bool)
                                {
                                    info.origin.insert(dest, LocalOrigin::Expr(Expr::And { lhs: lhs_local, rhs: rhs_local }));
                                }
                            } else {
                                info.origin.insert(
                                    dest,
                                    LocalOrigin::Expr(Expr::Cmp {
                                        op: *op,
                                        lhs: lhs_local,
                                        rhs: rhs_kind,
                                    }),
                                );
                            }
                        }
                    }
                    Rvalue::BinaryOp(BinOp::Rem, operands) => {
                        let (lhs, rhs): (&Operand<'_>, &Operand<'_>) =
                            (&operands.0, &operands.1);
                        if let Some(lhs_local) = match lhs {
                            Operand::Copy(l) | Operand::Move(l) if l.projection.is_empty() => {
                                Some(local_base + l.local.as_usize())
                            }
                            _ => None,
                        } {
                            let divisor = match rhs {
                                Operand::Constant(c) => {
                                    let typing_env = TypingEnv::post_analysis(tcx, def_id);
                                    c.const_.try_eval_bits(tcx, typing_env).map(|v| v as usize)
                                }
                                _ => None,
                            };
                            if let Some(divisor) = divisor
                                && divisor != 0 {
                                    info.origin.insert(dest, LocalOrigin::Expr(Expr::Rem { src: lhs_local, divisor }));
                                }
                        }
                    }
                    Rvalue::UnaryOp(unop, operand) => {
                        if matches!(unop, UnOp::Not)
                            && let Operand::Copy(src) | Operand::Move(src) = operand
                        {
                            info.origin
                                .insert(dest, LocalOrigin::Expr(Expr::Not { src: local_base + src.local.as_usize() }));
                        }
                    }
                    Rvalue::Cast(_, operand, _) => {
                        if let Operand::Copy(src) | Operand::Move(src) = operand
                            && matches!(
                                body.local_decls[place.local].ty.kind(),
                                TyKind::RawPtr(..) | TyKind::Int(..) | TyKind::Uint(..)
                            )
                        {
                            cast_chains.insert(dest, local_base + src.local.as_usize());
                        }
                    }
                    Rvalue::Ref(_, _, referent) => {
                        // `_x = &*_y` reborrows `_y`; link them for length tracking.
                        if referent
                            .projection
                            .iter()
                            .any(|p| matches!(p, ProjectionElem::Deref))
                        {
                            reborrow_referents
                                .insert(dest, local_base + referent.local.as_usize());
                        }
                    }
                    _ => {} // close match rvalue
                }
            }
        }

        if let Some(terminator) = &bb.terminator
            && let TerminatorKind::Call {
                destination,
                ref func,
                ..
            } = terminator.kind
                && let Some(did) = mir_utils::dep_callee_def_id(func) {
                    if other_api::known_nonnull_fns().contains(&did) {
                        info.origin
                            .insert(local_base + destination.local.as_usize(), LocalOrigin::NonNull);
                    }
                    if other_api::null_ptr_fns().contains(&did) {
                        info.origin
                            .insert(local_base + destination.local.as_usize(), LocalOrigin::Const(0));
                    }
                }

        block_info.push(info);
    }

    (
        block_info,
        disc_info,
        aggregate_field_sources,
        field_projection_source,
        cast_chains,
        reborrow_referents,
    )
}

impl<'tcx> PathGraph<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId) -> PathGraph<'tcx> {
        let body = tcx.optimized_mir(def_id);
        Self::new_with_body(tcx, def_id, body)
    }

    /// Build a path graph from an explicit MIR body (rather than
    /// `optimized_mir(def_id)`). Used to verify a monomorphized body whose
    /// `def_id` is still the generic function.
    pub fn new_with_body(tcx: TyCtxt<'tcx>, def_id: DefId, body: &Body<'tcx>) -> PathGraph<'tcx> {
        let basicblocks = &body.basic_blocks;
        let mut cfg_blocks = Vec::<CfgBlock>::new();

        for i in 0..basicblocks.len() {
            let bb = &basicblocks[BasicBlock::from(i)];
            let mut cfg_block = CfgBlock::new(def_id, i, bb.is_cleanup);

            let Some(terminator) = &bb.terminator else {
                cfg_blocks.push(cfg_block);
                continue;
            };

            match terminator.kind.clone() {
                TerminatorKind::Goto { ref target, .. } => {
                    cfg_block.add_next(target.as_usize());
                }
                TerminatorKind::SwitchInt {
                    discr: _,
                    ref targets,
                } => {
                    for (_, ref target) in targets.iter() {
                        cfg_block.add_next(target.as_usize());
                    }
                    cfg_block.add_next(targets.otherwise().as_usize());
                }
                TerminatorKind::Drop {
                    place: _,
                    target,
                    unwind,
                    replace: _,
                    drop: _,
                    #[cfg(not(rapx_ge_99))]
                        async_fut: _,
                } => {
                    cfg_block.add_next(target.as_usize());
                    if let UnwindAction::Cleanup(target) = unwind {
                        cfg_block.add_next(target.as_usize());
                    }
                }
                TerminatorKind::Call {
                    ref target,
                    ref unwind,
                    ..
                } => {
                    if let Some(tt) = target {
                        cfg_block.add_next(tt.as_usize());
                    }
                    if let UnwindAction::Cleanup(tt) = unwind {
                        cfg_block.add_next(tt.as_usize());
                    }
                }
                TerminatorKind::Assert {
                    cond: _,
                    expected: _,
                    msg: _,
                    ref target,
                    ref unwind,
                } => {
                    cfg_block.add_next(target.as_usize());
                    if let UnwindAction::Cleanup(target) = unwind {
                        cfg_block.add_next(target.as_usize());
                    }
                }
                TerminatorKind::Yield {
                    value: _,
                    ref resume,
                    resume_arg: _,
                    ref drop,
                } => {
                    cfg_block.add_next(resume.as_usize());
                    if let Some(target) = drop {
                        cfg_block.add_next(target.as_usize());
                    }
                }
                TerminatorKind::FalseEdge {
                    ref real_target,
                    imaginary_target: _,
                } => {
                    cfg_block.add_next(real_target.as_usize());
                }
                TerminatorKind::FalseUnwind {
                    ref real_target,
                    unwind: _,
                } => {
                    cfg_block.add_next(real_target.as_usize());
                }
                TerminatorKind::InlineAsm {
                    template: _,
                    operands: _,
                    options: _,
                    line_spans: _,
                    ref unwind,
                    targets,
                    asm_macro: _,
                } => {
                    for target in targets {
                        cfg_block.add_next(target.as_usize());
                    }
                    if let UnwindAction::Cleanup(target) = unwind {
                        cfg_block.add_next(target.as_usize());
                    }
                }
                _ => {}
            }

            cfg_blocks.push(cfg_block);
        }

        let mut cfg = ControlFlowGraph::new(def_id, tcx, cfg_blocks);
        // Back the root blocks with the supplied body so terminator lookups use
        // it (rather than `optimized_mir(def_id)`) — essential when the body is a
        // monomorphized instance whose trait-method calls carry concrete types.
        cfg.set_monomorphized(def_id, body.clone());
        let (
            block_info,
            disc_info,
            aggregate_field_sources,
            field_projection_source,
            cast_chains,
            reborrow_referents,
        ) = build_function_info(tcx, def_id, 0, body);

        let mut local_bases = FxHashMap::default();
        local_bases.insert(def_id, 0);

        PathGraph {
            cfg,
            block_info,
            disc_info,
            aggregate_field_sources,
            field_projection_source,
            cast_chains,
            reborrow_referents,
            inline_bindings: FxHashMap::default(),
            inline_parents: FxHashMap::default(),
            inlined_call_blocks: FxHashSet::default(),
            local_bases,
            next_local_base: body.local_decls.len(),
        }
    }

    /// Inline the CFG of inlinable callees into this graph so that path
    /// enumeration covers the callee's branches.
    ///
    /// Inlining is recursive *within the local crate*: a local callee's own
    /// calls are inlined too. Cross-crate callees are inlined only at the level
    /// where a local function calls them — their bodies are not recursed into,
    /// so the standard library's internal branchy precondition machinery
    /// (`is_aligned_to`, `ub_checks`, …) is not pulled in, which would blow up
    /// path enumeration with branches that have no constraint tracking.
    ///
    /// Each callee is otherwise subject to the same shape constraints as
    /// before: cross-crate callees with MIR are always inlined, and a local
    /// callee is inlined only when it is small (at most
    /// [`LOCAL_INLINE_BLOCK_LIMIT`](crate::limit::LOCAL_INLINE_BLOCK_LIMIT) basic
    /// blocks), so branch-free accessors
    /// (`get`, `count_ones`, …) also land in the CFG and their field
    /// provenance is reconstructed element-by-element. Intrinsics
    /// have no MIR; callees with a builtin model are kept opaque because their
    /// summary is more precise than their body.
    ///
    /// Recursion is bounded by an `expanded` set so that (mutually) recursive
    /// local functions do not grow the CFG without bound — a back-edge to an
    /// already-inlined callee is left as an ordinary call edge for the VM's
    /// fallback handling.
    ///
    /// Opt-in — callers that assume a single-function block space (e.g. alias
    /// analysis) must not call this.
    pub fn inline_callees(&mut self) {
        let tcx = self.tcx();
        let caller_def_id = self.def_id();

        let mut expanded: FxHashSet<DefId> = FxHashSet::default();
        expanded.insert(caller_def_id);

        loop {
            let mut pending: Vec<(usize, DefId, Option<Instance<'tcx>>)> = Vec::new();
            for i in 0..self.cfg.blocks.len() {
                let Some(term) = self.terminator(i) else {
                    continue;
                };
                let TerminatorKind::Call { func, target, .. } = &term.kind else {
                    continue;
                };
                // A diverging call (`panic!` / `unreachable!`) has no normal
                // successor to reconnect through the inlined body, so it is
                // never inlined.
                if target.is_none() {
                    continue;
                }
                // Cross-crate callees keep their raw trait-method def_id (trait
                // methods have no MIR and are left to builtin models). Local
                // callees are resolved to the concrete impl so a user trait
                // method (e.g. `<MyIter as Iterator>::next`) inlines against its
                // actual MIR.
                let Some(base_callee) = mir_utils::dep_callee_def_id(func) else {
                    continue;
                };
                let cross_crate = base_callee.as_local().is_none();
                let is_trait_method = tcx
                    .opt_associated_item(base_callee)
                    .and_then(|a| a.trait_container(tcx))
                    .is_some();
                // Resolve a cross-crate trait method to its impl only when the
                // VM has no symbolic model for it (e.g. `Iterator::next`).
                let resolve_to_impl = !cross_crate
                    || !is_trait_method
                    || !crate::verify::call_summary::effects::is_symbolically_modeled(Some(
                        base_callee,
                    ));
                // Cross-crate bodies are scanned only for resolvable trait
                // methods (e.g. `slice::get` delegating to `SliceIndex::get`).
                if self.cfg.block(i).def_id.as_local().is_none() && !(is_trait_method && resolve_to_impl)
                {
                    continue;
                }
                let callee = if resolve_to_impl {
                    mir_utils::dep_callee_resolved_def_id(
                        tcx,
                        self.cfg.block(i).def_id,
                        func,
                    )
                    .unwrap_or(base_callee)
                } else {
                    base_callee
                };
                // A trait-object call (`&dyn Bound`) has no single target:
                // enumerate every impl and inline up to `trait_impl_limit` of
                // them. Generic `T: Bound` never reaches here — caller
                // monomorphization gives it a concrete `Self`, so it falls
                // through to the normal inline path below.
                if is_trait_method {
                    let is_virtual = mir_utils::resolve_callee_instance(
                        tcx,
                        self.cfg.block(i).def_id,
                        func,
                    )
                    .is_some_and(|inst| mir_utils::instance_def_id(tcx, inst).1);
                    if is_virtual {
                        if !crate::verify::call_summary::effects::is_symbolically_modeled(Some(base_callee)) {
                            let candidates = mir_utils::trait_impl_candidates(tcx, base_callee);
                            for cand in candidates.into_iter().take(crate::limit::trait_impl_limit())
                            {
                                if tcx.is_mir_available(cand) && !expanded.contains(&cand) {
                                    pending.push((i, cand, None));
                                }
                            }
                        }
                        continue;
                    }
                }
                let instance = if cross_crate
                    && crate::def_ids::other_api::is_slice_get(Some(base_callee))
                {
                    mir_utils::resolve_callee_instance(tcx, self.cfg.block(i).def_id, func)
                } else {
                    None
                };
                let has_fn_sim =
                    crate::verify::call_summary::effects::is_symbolically_modeled(Some(callee));
                let is_ub_check = crate::def_ids::other_api::is_ub_check(tcx, callee);
                // Skip cross-crate trait methods with a default body (they call a
                // further required method whose effect we can't attribute).
                let cross_crate_trait_method = cross_crate
                    && is_trait_method
                    && tcx.is_mir_available(base_callee);
                if crate::def_ids::intrinsic_api::is_intrinsic(tcx, callee)
                    || !tcx.is_mir_available(callee)
                    || expanded.contains(&callee)
                    || has_fn_sim
                    || is_ub_check
                    || cross_crate_trait_method
                {
                    continue;
                }
                // A local callee is inlined only when it is small (a transitive
                // shape bound that keeps path enumeration tractable; see
                // `LOCAL_INLINE_BLOCK_LIMIT`). Branch-free accessors are no
                // longer excluded: their bodies land in the CFG and the backward
                // slicer/VM reconstruct field provenance through the inlined
                // call chain.
                let small_local = !cross_crate && {
                    let body = tcx.optimized_mir(callee);
                    body.basic_blocks.len() <= LOCAL_INLINE_BLOCK_LIMIT
                };
                if cross_crate || small_local {
                    pending.push((i, callee, instance));
                }
            }

            if pending.is_empty() {
                break;
            }

            // Mark every pending callee as expanded *before* inlining so a
            // callee that (transitively) calls itself or another pending callee
            // is not inlined again on a later iteration.
            for (_, callee, _) in &pending {
                expanded.insert(*callee);
            }

            for (caller_idx, callee, instance) in pending {
                self.inline_one(caller_idx, callee, instance);
            }
        }
    }

    /// Inline a single callee into `caller_idx`, reconnecting the caller's
    /// normal successor edge through the callee body.
    fn inline_one(
        &mut self,
        caller_idx: usize,
        callee: DefId,
        instance: Option<Instance<'tcx>>,
    ) {
        let tcx = self.tcx();
        // The caller block may itself be an inlined callee (nested inlining), so
        // its MIR successor indices must be shifted into the global block space.
        let caller_base = caller_idx - self.cfg.block(caller_idx).local_index;
        let (caller_target, caller_unwind, arg_locals, arg_consts, arg_field_offsets, dest_local) = match self.terminator(caller_idx)
        {
            Some(term) => match &term.kind {
                TerminatorKind::Call {
                    target,
                    unwind,
                    args,
                    destination,
                    ..
                } => {
                    let target = target.map(|t| caller_base + t.as_usize());
                    let unwind = match unwind {
                        UnwindAction::Cleanup(t) => Some(caller_base + t.as_usize()),
                        _ => None,
                    };
                    let arg_locals: Vec<usize> = args
                        .iter()
                        .filter_map(|a| a.node.place().map(|p| p.local.as_usize()))
                        .collect();
                    let arg_consts: Vec<(usize, u64)> = args
                        .iter()
                        .enumerate()
                        .filter_map(|(i, a)| {
                            mir_utils::operand_const_u64(&a.node).map(|v| (i + 1, v))
                        })
                        .collect();
                    let arg_field_offsets: Vec<usize> = args
                        .iter()
                        .enumerate()
                        .filter_map(|(i, a)| {
                            let Operand::Constant(c) = &a.node else {
                                return None;
                            };
                            mir_utils::offset_of_container(self.tcx(), &c.const_)
                                .map(|_| i + 1)
                        })
                        .collect();
                    (
                        target,
                        unwind,
                        arg_locals,
                        arg_consts,
                        arg_field_offsets,
                        destination.local.as_usize(),
                    )
                }
                _ => (None, None, Vec::new(), Vec::new(), Vec::new(), 0),
            },
            None => (None, None, Vec::new(), Vec::new(), Vec::new(), 0),
        };
        let Some(target) = caller_target else {
            return;
        };

        let body = match instance {
            Some(inst) => {
                let caller = self.cfg.block(caller_idx).def_id;
                let mir = tcx.optimized_mir(inst.def_id());
                inst.instantiate_mir_and_normalize_erasing_regions(
                    tcx,
                    TypingEnv::post_analysis(tcx, caller),
                    rustc_middle::ty::EarlyBinder::bind(tcx, mir.clone()),
                )
            }
            None => tcx.optimized_mir(callee).clone(),
        };
        if instance.is_some() {
            // Back the inlined blocks with the monomorphized body so terminator
            // lookups see the concrete callee, not the generic trait method.
            self.cfg.set_monomorphized(callee, body.clone());
        }
        let base = self.cfg.blocks.len();
        let block_count = body.basic_blocks.len();

        // Build the callee's constant/discriminant metadata under its own local
        // namespace so its constraint tracking doesn't clash with the caller's.
        let local_base = self.assign_local_base(callee);
        let (callee_info, callee_disc, callee_agg, callee_fproj, callee_cast, callee_reborrow) =
            build_function_info(tcx, callee, local_base, &body);

        for i in 0..block_count {
            let bb = &body.basic_blocks[BasicBlock::from(i)];
            let mut cb = CfgBlock {
                index: base + i,
                def_id: callee,
                local_index: i,
                is_cleanup: bb.is_cleanup,
                next: FxHashSet::default(),
                scc: SccInfo::new(base + i),
            };
            if let Some(term) = &bb.terminator {
                match &term.kind {
                    TerminatorKind::Goto { target: t, .. } => {
                        cb.add_next(base + t.as_usize());
                    }
                    TerminatorKind::SwitchInt { targets, .. } => {
                        for (_, t) in targets.iter() {
                            cb.add_next(base + t.as_usize());
                        }
                        cb.add_next(base + targets.otherwise().as_usize());
                    }
                    TerminatorKind::Return => {
                        cb.add_next(target);
                    }
                    TerminatorKind::TailCall { .. } => {
                        cb.add_next(target);
                        if let Some(u) = caller_unwind {
                            cb.add_next(u);
                        }
                    }
                    TerminatorKind::UnwindResume => {
                        // A callee that unwinds re-enters the caller at its
                        // unwind/cleanup block (the caller's `Cleanup` target of
                        // the inlined call), never at the normal return target.
                        if let Some(u) = caller_unwind {
                            cb.add_next(u);
                        }
                    }
                    TerminatorKind::Call {
                        target: t,
                        unwind,
                        ..
                    } => {
                        if let Some(t) = t {
                            cb.add_next(base + t.as_usize());
                        }
                        if let UnwindAction::Cleanup(tt) = unwind {
                            cb.add_next(base + tt.as_usize());
                        }
                    }
                    TerminatorKind::Drop {
                        target: t, unwind, ..
                    } => {
                        cb.add_next(base + t.as_usize());
                        if let UnwindAction::Cleanup(tt) = unwind {
                            cb.add_next(base + tt.as_usize());
                        }
                    }
                    TerminatorKind::Assert {
                        target: t,
                        unwind,
                        ..
                    } => {
                        cb.add_next(base + t.as_usize());
                        if let UnwindAction::Cleanup(tt) = unwind {
                            cb.add_next(base + tt.as_usize());
                        }
                    }
                    TerminatorKind::FalseEdge { real_target, .. }
                    | TerminatorKind::FalseUnwind { real_target, .. } => {
                        cb.add_next(base + real_target.as_usize());
                    }
                    _ => {}
                }
            }
            self.cfg.blocks.push(cb);
        }

        // Append the callee's per-block metadata and merge its global source
        // maps (all keyed in the callee's own local namespace).
        self.block_info.extend(callee_info);
        self.disc_info.source_of.extend(callee_disc.source_of);
        self.disc_info.variant_count_of.extend(callee_disc.variant_count_of);
        self.aggregate_field_sources.extend(callee_agg);
        self.field_projection_source.extend(callee_fproj);
        self.cast_chains.extend(callee_cast);
        self.reborrow_referents.extend(callee_reborrow);

        // Record the argument binding for the callee entry.
        self.inline_bindings.insert(
            base,
            InlineBinding {
                arg_locals,
                arg_consts,
                arg_field_offsets,
                dest_local,
            },
        );
        self.inline_parents
            .insert(base, self.cfg.block(caller_idx).def_id);
        self.inlined_call_blocks.insert(caller_idx);

        // Reconnect the caller's normal successor edge through the callee entry.
        let caller_block = self.cfg.block_mut(caller_idx);
        caller_block.next.remove(&target);
        caller_block.next.insert(base);
    }

    pub fn find_scc(&mut self) {
        self.cfg.find_scc();
        self.populate_all_child_sccs();
    }

    pub fn def_id(&self) -> DefId {
        self.cfg.def_id
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.cfg.tcx
    }

    pub fn cfg_block(&self, index: usize) -> &CfgBlock {
        self.cfg.block(index)
    }

    pub fn cfg_block_mut(&mut self, index: usize) -> &mut CfgBlock {
        self.cfg.block_mut(index)
    }

    /// Retrieve the MIR terminator for the block at `index` on demand.
    pub fn terminator(&self, index: usize) -> Option<&Terminator<'tcx>> {
        self.cfg.terminator(index)
    }

    pub fn is_cleanup_block(&self, index: usize) -> bool {
        self.cfg
            .blocks
            .get(index)
            .map(|b| b.is_cleanup)
            .unwrap_or(false)
    }

    /// The local-index base of `def_id`'s MIR locals in the flat constraint
    /// maps. The root caller is base `0`; inlined callees get a fresh base.
    fn local_base_of(&self, def_id: DefId) -> usize {
        self.local_bases.get(&def_id).copied().unwrap_or(0)
    }

    /// Remap `def_id`'s MIR local `local` into the global constraint namespace.
    fn remap_local(&self, def_id: DefId, local: usize) -> usize {
        self.local_base_of(def_id) + local
    }

    /// Assign a fresh local-namespace base for `def_id` (or return its existing
    /// base if the function has already been inlined).
    fn assign_local_base(&mut self, def_id: DefId) -> usize {
        if let Some(&base) = self.local_bases.get(&def_id) {
            return base;
        }
        let base = self.next_local_base;
        let local_count = self.tcx().optimized_mir(def_id).local_decls.len();
        self.local_bases.insert(def_id, base);
        self.next_local_base = base + local_count;
        base
    }

    /// Get the number of variants for a constraint local (in `def_id`'s local
    /// namespace). First checks the pre-populated `variant_count_of` hashmap,
    /// then falls back to the local's declared type (for ADT locals that gained
    /// their type through field projections in nested destructuring patterns
    /// rather than explicit construction).
    fn get_variant_count(&self, local: usize, def_id: DefId) -> Option<usize> {
        if let Some(&count) = self.disc_info.variant_count_of.get(&local) {
            return Some(count);
        }
        let body = self.cfg.tcx.optimized_mir(def_id);
        let original = local - self.local_base_of(def_id);
        let mut ty = body.local_decls[Local::from_usize(original)].ty;
        while let TyKind::Ref(_, inner_ty, _) | TyKind::RawPtr(inner_ty, _) = ty.kind() {
            ty = *inner_ty;
        }
        match ty.kind() {
            TyKind::Adt(adt_def, _) if adt_def.is_enum() => Some(adt_def.variants().len()),
            _ => None,
        }
    }

    /// Check a single transition `cur -> next` for reachability and update
    /// discriminant constraints. Returns `false` if the transition is
    /// provably unreachable.
    pub(crate) fn check_transition(
        &self,
        cur: usize,
        next: usize,
        cs: &mut ConstraintSet,
    ) -> bool {
        if cur >= self.cfg.blocks.len() || next >= self.cfg.blocks.len() {
            return false;
        }

        if let Some(info) = self.block_info.get(cur) {
            for local in &info.assigned_locals {
                // Clear both the local and its canonical form (a loop counter
                // `i = (_add).0` canonicalizes to `(_add, 0)`).
                cs.bounds.remove(local);
                cs.bounds.remove(&self.canonical_field(*local));
                cs.lengths.remove(local);
                cs.lengths.remove(&self.canonical_field(*local));
                if let Some(&src) = info.origin.get(local).and_then(LocalOrigin::as_copy) {
                    if let Some(val) = self.resolve_local_value(src, cs) {
                        cs.consts.insert(*local, val);
                        continue;
                    }
                    if let Some(&dst_val) = cs.consts.get(local) {
                        cs.consts.insert(src, dst_val);
                        cs.consts.insert(*local, dst_val);
                        continue;
                    }
                }
                if let Some(&val) = info.origin.get(local).and_then(LocalOrigin::as_const) {
                    cs.consts.insert(*local, val);
                    continue;
                }
                cs.consts.remove(local);
            }
            for (local, origin) in &info.origin {
                if matches!(origin, LocalOrigin::NonNull) {
                    cs.consts.insert(*local, usize::MAX);
                }
            }
            for local in &info.assigned_locals {
                self.derive_increment_bound(*local, cs);
            }
        }

        // Also clear constraints for locals assigned by the terminator
        // (e.g. _13 = Iterator::next() in a Call terminator). The block's
        // assigned_locals only covers statement-level assignments, so
        // terminator-side assignments are handled here.
        if let Some(terminator) = self.terminator(cur) {
            let local_base = self.local_base_of(self.cfg.block(cur).def_id);
            let assigned = match &terminator.kind {
                TerminatorKind::Call { destination, .. } => {
                    Some(local_base + destination.local.as_usize())
                }
                TerminatorKind::Yield { resume_arg, .. } => {
                    Some(local_base + resume_arg.local.as_usize())
                }
                _ => None,
            };
            if let Some(local) = assigned {
                cs.bounds.remove(&local);
                cs.lengths.remove(&local);
                if let Some(block_info) = self.block_info.get(cur) {
                    if let Some(&val) = block_info.origin.get(&local).and_then(LocalOrigin::as_const) {
                        cs.consts.insert(local, val);
                    } else if matches!(block_info.origin.get(&local), Some(LocalOrigin::NonNull)) {
                        cs.consts.insert(local, usize::MAX);
                    } else {
                        cs.consts.remove(&local);
                    }
                } else {
                    cs.consts.remove(&local);
                }
            }
        }

        if self.terminator(cur).is_some_and(|t| {
            matches!(t.kind, TerminatorKind::Return | TerminatorKind::TailCall { .. })
        }) {
            let entry = cur - self.cfg.block(cur).local_index;
            if let (Some(binding), Some(parent)) = (
                self.inline_bindings.get(&entry),
                self.inline_parents.get(&entry),
            ) {
                let return_ty = self.tcx().optimized_mir(self.cfg.block(cur).def_id)
                    .local_decls[Local::from_usize(0)].ty;
                let is_branch_enum = matches!(return_ty.kind(), TyKind::Adt(adt, _)
                    if self.tcx().is_diagnostic_item(rustc_span::sym::Result, adt.did())
                        || self.tcx().is_diagnostic_item(rustc_span::sym::Option, adt.did())
                        || self.tcx().def_path_str(adt.did()).ends_with("::ControlFlow"));
                if is_branch_enum {
                    let return_local = self.remap_local(self.cfg.block(cur).def_id, 0);
                    let destination = self.remap_local(*parent, binding.dest_local);
                    if let Some(value) = cs.consts.get(&return_local).copied() {
                        cs.consts.insert(destination, value);
                    } else {
                        cs.consts.remove(&destination);
                    }
                }
            }
        }

        // Track slice lengths from `slice::get`/`slice::len`/`Try::branch`.
        if let Some(terminator) = self.terminator(cur)
            && let TerminatorKind::Call { func, args, destination, .. } = &terminator.kind
            && let Some(callee) = mir_utils::dep_callee_def_id(func)
        {
            let dest = self.remap_local(self.cfg.block(cur).def_id, destination.local.as_usize());
            if self.tcx().def_path_str(callee).ends_with("::branch")
                && let Some(source) = args.first().and_then(|arg| arg.node.place())
            {
                let source_local = self.remap_local(self.cfg.block(cur).def_id, source.local.as_usize());
                let source_ty = self.tcx().optimized_mir(self.cfg.block(cur).def_id).local_decls[source.local].ty;
                if let TyKind::Adt(adt, _) = source_ty.kind()
                    && let Some(value) = cs.consts.get(&source_local).copied()
                {
                    let branch = if self.tcx().is_diagnostic_item(rustc_span::sym::Option, adt.did()) {
                        match value {
                            0 => Some(1),
                            1 => Some(0),
                            _ => None,
                        }
                    } else if self.tcx().is_diagnostic_item(rustc_span::sym::Result, adt.did()) {
                        (value <= 1).then_some(value)
                    } else {
                        None
                    };
                    if let Some(branch) = branch {
                        cs.consts.insert(dest, branch);
                    }
                }
            }
            if crate::def_ids::other_api::is_slice_get(Some(callee)) {
                if let Some(range) = args.get(1)
                    && let Some(range_local) =
                        range.node.place().map(|p| p.local.as_usize())
                {
                    let start = self
                        .aggregate_field_sources
                        .get(&encode_aggregate_field(range_local, 0))
                        .copied();
                    let end = self
                        .aggregate_field_sources
                        .get(&encode_aggregate_field(range_local, 1))
                        .copied();
                    if let (Some(start), Some(end)) = (start, end) {
                        cs.lengths.insert(dest, (start, end));
                    }
                }
            } else if crate::def_ids::other_api::is_len(Some(callee)) {
                // `slice::len(slice)` -> resolve the slice's length.
                if let Some(slice) = args.get(0)
                    && let Some(slice_local) =
                        slice.node.place().map(|p| p.local.as_usize())
                {
                    let slice_local =
                        self.remap_local(self.cfg.block(cur).def_id, slice_local);
                    if let Some(len) = self.resolve_length(slice_local, cs) {
                        cs.lengths.insert(dest, len);
                    }
                }
            } else if self.tcx().def_path_str(callee).ends_with("::branch") {
                // `Try::branch(option)` -> the `Continue` payload carries the
                // same length as the input `Some` payload.
                if let Some(opt) = args.get(0)
                    && let Some(opt_local) =
                        opt.node.place().map(|p| p.local.as_usize())
                {
                    let opt_local =
                        self.remap_local(self.cfg.block(cur).def_id, opt_local);
                    if let Some(len) = self.resolve_length(opt_local, cs) {
                        cs.lengths.insert(dest, len);
                    }
                }
            }
        }

        // Carry bounds from a field's source to the constructed aggregate field.
        for (&encoded, &src) in &self.aggregate_field_sources {
            let canon = self.canonical_field(src);
            if let Some(src_bounds) = cs.bounds.get(&canon).cloned() {
                let entry = cs.bounds.entry(encoded).or_default();
                for (r, s) in src_bounds {
                    if !entry.iter().any(|&(rr, ss)| rr == r && ss == s) {
                        entry.push((r, s));
                    }
                }
            }
        }

        // Carry a callee's return-payload bounds to the caller's destination.
        if let Some(terminator) = self.terminator(cur)
            && matches!(
                terminator.kind,
                TerminatorKind::Return | TerminatorKind::TailCall { .. }
            )
        {
            let callee = self.cfg.block(cur).def_id;
            for (&entry, binding) in &self.inline_bindings {
                if self.cfg.block(entry).def_id == callee {
                    let ret_local = self.local_base_of(callee);
                    if let Some(bounds) =
                        cs.bounds.get(&encode_aggregate_field(ret_local, 0)).cloned()
                    {
                        let dst = encode_aggregate_field(binding.dest_local, 0);
                        let dst_entry = cs.bounds.entry(dst).or_default();
                        for (r, s) in bounds {
                            if !dst_entry.iter().any(|&(rr, ss)| rr == r && ss == s) {
                                dst_entry.push((r, s));
                            }
                        }
                    }
                }
            }
        }

        let successors = &self.cfg.block(cur).next;
        if !successors.contains(&next)
            && !self.is_unwind_target(cur, next) {
                return false;
            }

        if !self.check_switch_transition(cur, next, cs) {
            return false;
        }

        if !self.check_assert_transition(cur, next, cs) {
            return false;
        }

        // Propagate known-nonzero facts across an inlined-callee boundary: the
        // callee's parameter `_i+1` inherits the caller's argument `arg_locals[i]`.
        if let Some(binding) = self.inline_bindings.get(&next).cloned() {
            let caller_def_id = self.cfg.block(cur).def_id;
            let callee_def_id = self.cfg.block(next).def_id;
            let return_ty = self.tcx().optimized_mir(callee_def_id)
                .local_decls[Local::from_usize(0)].ty;
            if matches!(return_ty.kind(), TyKind::Adt(adt, _)
                if self.tcx().is_diagnostic_item(rustc_span::sym::Result, adt.did())
                    || self.tcx().is_diagnostic_item(rustc_span::sym::Option, adt.did())
                    || self.tcx().def_path_str(adt.did()).ends_with("::ControlFlow")) {
                cs.consts.remove(&self.remap_local(callee_def_id, 0));
            }
            for (i, &arg_local) in binding.arg_locals.iter().enumerate() {
                let caller_arg = self.remap_local(caller_def_id, arg_local);
                if self.local_is_known_nonnull(cs, caller_arg) {
                    cs.consts.insert(self.remap_local(callee_def_id, i + 1), usize::MAX);
                }
                if let Some(len) = self.resolve_length(caller_arg, cs) {
                    cs.lengths.insert(self.remap_local(callee_def_id, i + 1), len);
                }
            }
        }

        true
    }

    fn check_assert_transition(
        &self,
        cur: usize,
        next: usize,
        cs: &mut ConstraintSet,
    ) -> bool {
        let Some(terminator) = self.cfg.terminator(cur) else {
            return true;
        };
        let TerminatorKind::Assert { cond, expected, target, .. } = &terminator.kind else {
            return true;
        };
        let base = cur - self.cfg.block(cur).local_index;
        if next != base + target.as_usize() {
            return true;
        }
        // On the assert-passed path the condition holds: if it is a comparison
        // like `x > 0` / `x != 0`, mark `x` as known-nonzero so a downstream
        // `x == 0` branch (e.g. `RawVec::allocate_in`'s zero-capacity path) is
        // pruned.
        self.mark_assert_nonzero(cur, cond, *expected, cs);
        let cond_local = match cond {
            Operand::Copy(p) | Operand::Move(p) => {
                self.remap_local(self.cfg.block(cur).def_id, p.local.as_usize())
            }
            Operand::Constant(c) => {
                let typing_env =
                    rustc_middle::ty::TypingEnv::post_analysis(self.cfg.tcx, self.cfg.def_id);
                return c
                    .const_
                    .try_eval_bool(self.cfg.tcx, typing_env)
                    .unwrap_or(true);
            }
            #[cfg(rapx_ge_95)]
            Operand::RuntimeChecks(_) => return true,
        };
        self.resolve_bool_local(cond_local, cs)
            .is_none_or(|v| v == 1)
    }

    /// Mark `lhs` as non-zero when the assert condition is `lhs > 0` / `!= 0`.
    fn mark_assert_nonzero(
        &self,
        cur: usize,
        cond: &Operand<'_>,
        expected: bool,
        cs: &mut ConstraintSet,
    ) {
        if !expected {
            return;
        }
        let (Operand::Copy(p) | Operand::Move(p)) = cond else {
            return;
        };
        let cond_local = self.remap_local(self.cfg.block(cur).def_id, p.local.as_usize());
        let Some(LocalOrigin::Expr(Expr::Cmp { op, lhs, rhs })) = self
            .block_info
            .iter()
            .find_map(|info| info.origin.get(&cond_local).cloned())
        else {
            return;
        };
        let nonzero = matches!(
            (op, rhs),
            (BinOp::Gt, Rhs::Const(0)) | (BinOp::Ge, Rhs::Const(1)) | (BinOp::Ne, Rhs::Const(0))
        );
        if nonzero {
            cs.consts.insert(lhs, usize::MAX);
        }
    }

    /// Record the relational fact `lhs < rhs` (strict) or `lhs <= rhs` (non-strict).
    fn record_bound(cs: &mut ConstraintSet, lhs: usize, rhs: usize, strict: bool) {
        let entry = cs.bounds.entry(lhs).or_default();
        if !entry.iter().any(|&(r, s)| r == rhs && s == strict) {
            entry.push((rhs, strict));
        }
    }

    /// Is `lhs <= rhs` known (either `lhs < rhs` or `lhs <= rhs` recorded)?
    fn bound_le_known(&self, lhs: usize, rhs: usize, cs: &ConstraintSet) -> bool {
        cs.bounds
            .get(&lhs)
            .is_some_and(|v| v.iter().any(|&(r, _)| r == rhs))
    }

    /// Is `lhs < rhs` known (a strict bound recorded)?
    fn bound_lt_known(&self, lhs: usize, rhs: usize, cs: &ConstraintSet) -> bool {
        cs.bounds
            .get(&lhs)
            .is_some_and(|v| v.iter().any(|&(r, s)| r == rhs && s))
    }

    /// Resolve an order comparison to `Some(true)` / `Some(false)` from the
    /// recorded relational bounds, or `None` when undetermined.
    fn relation_status(&self, op: BinOp, lhs: usize, rhs: Rhs, cs: &ConstraintSet) -> Option<bool> {
        let l = self.canonical_field(lhs);
        let r = match rhs {
            Rhs::Const(v) => v,
            Rhs::Local(l) => self.canonical_field(l),
        };
        match op {
            BinOp::Lt => {
                if self.bound_lt_known(l, r, cs) {
                    return Some(true);
                }
                if self.bound_le_known(r, l, cs) {
                    return Some(false);
                }
                None
            }
            BinOp::Le => {
                if self.bound_le_known(l, r, cs) {
                    return Some(true);
                }
                if self.bound_lt_known(r, l, cs) {
                    return Some(false);
                }
                None
            }
            BinOp::Gt => {
                if self.bound_lt_known(r, l, cs) {
                    return Some(true);
                }
                if self.bound_le_known(l, r, cs) {
                    return Some(false);
                }
                None
            }
            BinOp::Ge => {
                if self.bound_le_known(r, l, cs) {
                    return Some(true);
                }
                if self.bound_lt_known(l, r, cs) {
                    return Some(false);
                }
                None
            }
            _ => None,
        }
    }

    /// Canonicalize a local to a stable key, following field projections and
    /// whole-place copies.
    fn canonical_field(&self, local: usize) -> usize {
        let mut cur = local;
        let mut seen = FxHashSet::default();
        loop {
            if !seen.insert(cur) {
                return cur;
            }
            if let Some(&encoded) = self.field_projection_source.get(&cur) {
                cur = encoded;
                continue;
            }
            let mut next: Option<usize> = None;
            for info in &self.block_info {
                if let Some(&src) = info.origin.get(&cur).and_then(LocalOrigin::as_copy) {
                    next = Some(src);
                    break;
                }
            }
            match next {
                Some(src) => cur = src,
                None => return cur,
            }
        }
    }

    /// Resolve a slice-length fact `(start, end)` for `local`, following copies,
    /// field projections, and reborrows.
    fn resolve_length(&self, local: usize, cs: &ConstraintSet) -> Option<(usize, usize)> {
        let mut stack = vec![local];
        let mut seen = FxHashSet::default();
        while let Some(cur) = stack.pop() {
            if !seen.insert(cur) {
                continue;
            }
            if let Some(&len) = cs.lengths.get(&cur) {
                return Some(len);
            }
            for info in &self.block_info {
                if let Some(&src) = info.origin.get(&cur).and_then(LocalOrigin::as_copy) {
                    stack.push(src);
                }
            }
            if let Some(&encoded) = self.field_projection_source.get(&cur) {
                if let Some((agg, field)) = decode_aggregate_field(encoded)
                    && let Some(&actual) = self
                        .aggregate_field_sources
                        .get(&encode_aggregate_field(agg, field))
                {
                    stack.push(actual);
                }
            }
            if let Some(&ref_src) = self.reborrow_referents.get(&cur) {
                stack.push(ref_src);
            }
        }
        None
    }

    /// Resolve `local` to `(base, index, k)` where `local == base + index + k`;
    /// `index` is `usize::MAX` when there is no secondary variable.
    fn resolve_sum(&self, local: usize) -> Option<(usize, usize, usize)> {
        let mut cur = local;
        let mut seen = FxHashSet::default();
        loop {
            if !seen.insert(cur) {
                return None;
            }
            // A field projection is not an integer sum.
            if self.field_projection_source.contains_key(&cur) {
                return None;
            }
            let mut next: Option<usize> = None;
            for info in &self.block_info {
                if let Some(&src) = info.origin.get(&cur).and_then(LocalOrigin::as_copy) {
                    next = Some(src);
                    break;
                }
            }
            match next {
                Some(src) => cur = src,
                None => break,
            }
        }
        for info in &self.block_info {
            if let Some(LocalOrigin::Expr(Expr::Add { lhs, rhs })) = info.origin.get(&cur) {
                return match rhs {
                    Rhs::Local(r) => {
                        let (r_base, r_k) = self.resolve_rhs_sum(*r);
                        Some((*lhs, r_base, r_k))
                    }
                    Rhs::Const(k) => Some((*lhs, usize::MAX, *k)),
                };
            }
        }
        Some((cur, usize::MAX, 0))
    }

    /// Resolve the `rhs` of an add to `(base, k)` (`rhs == base + k`),
    /// following field projections and copies to the underlying increment.
    fn resolve_rhs_sum(&self, rhs: usize) -> (usize, usize) {
        let mut cur = rhs;
        let mut seen = FxHashSet::default();
        loop {
            if !seen.insert(cur) {
                return (cur, 0);
            }
            if let Some(&encoded) = self.field_projection_source.get(&cur) {
                if let Some((agg, _)) = decode_aggregate_field(encoded) {
                    cur = agg;
                    continue;
                }
            }
            let mut next: Option<usize> = None;
            for info in &self.block_info {
                if let Some(&src) = info.origin.get(&cur).and_then(LocalOrigin::as_copy) {
                    next = Some(src);
                    break;
                }
            }
            match next {
                Some(src) => cur = src,
                None => break,
            }
        }
        for info in &self.block_info {
            if let Some(LocalOrigin::Expr(Expr::Add { lhs, rhs: Rhs::Const(k) })) = info.origin.get(&cur) {
                return (*lhs, *k);
            }
        }
        (cur, 0)
    }

    /// Derive `local <= end` from `local = base + index + k`, a bound
    /// `index < len`/`index <= len`, and a length `len == end - base`.
    fn derive_increment_bound(&self, local: usize, cs: &mut ConstraintSet) {
        let Some((base, index, k)) = self.resolve_sum(local) else {
            return;
        };
        if index == usize::MAX {
            return;
        }
        let canonical = self.canonical_field(index);
        let mut bounds: Vec<(usize, bool)> = Vec::new();
        if let Some(b) = cs.bounds.get(&index) {
            bounds.extend_from_slice(b);
        }
        if canonical != index
            && let Some(b) = cs.bounds.get(&canonical)
        {
            bounds.extend_from_slice(b);
        }
        for &(len, strict) in &bounds {
            let Some(&(start, end)) = cs.lengths.get(&len) else {
                continue;
            };
            if self.canonical_field(start) != base {
                continue;
            }
            let out = if strict {
                match k {
                    0 => Some((end, true)),
                    1 => Some((end, false)),
                    _ => None,
                }
            } else if k == 0 {
                Some((end, false))
            } else {
                None
            };
            if let Some((rhs, s)) = out {
                Self::record_bound(cs, base, self.canonical_field(rhs), s);
            }
        }
    }

    fn resolve_simple_bool(
        &self,
        local: usize,
        cs: &ConstraintSet,
    ) -> Option<usize> {
        if let Some(&val) = cs.consts.get(&local)
            && val <= 1
        {
            return Some(val);
        }
        for info in &self.block_info {
            if let Some(&val) = info.origin.get(&local).and_then(LocalOrigin::as_const)
                && val <= 1
            {
                return Some(val);
            }
            if let Some(LocalOrigin::Expr(Expr::Cmp { op, lhs, rhs })) =
                info.origin.get(&local).cloned()
                && matches!(op, BinOp::Eq | BinOp::Ne)
            {
                let is_eq = matches!(op, BinOp::Eq);
                if let Rhs::Const(rhs_val) = rhs {
                    if let Some(lhs_val) = self.resolve_local_value(lhs, cs) {
                        return Some(if is_eq {
                            if lhs_val == rhs_val { 1 } else { 0 }
                        } else {
                            if lhs_val != rhs_val { 1 } else { 0 }
                        });
                    }
                } else if let Rhs::Local(rhs_local) = rhs {
                    let lhs_val = self.resolve_local_value(lhs, cs);
                    let rhs_val = self.resolve_local_value(rhs_local, cs);
                    if let Some(lhs_val) = lhs_val {
                        if let Some(rhs_val) = rhs_val {
                            return Some(if is_eq {
                                if lhs_val == rhs_val { 1 } else { 0 }
                            } else {
                                if lhs_val != rhs_val { 1 } else { 0 }
                            });
                        }
                    } else if let Some(rhs_val) = rhs_val {
                        return Some(if is_eq {
                            if lhs == rhs_val { 1 } else { 0 }
                        } else {
                            if lhs != rhs_val { 1 } else { 0 }
                        });
                    }
                }
            }
        }
        None
    }

    fn resolve_bool_local(
        &self,
        local: usize,
        cs: &ConstraintSet,
    ) -> Option<usize> {
        let mut stack = vec![(local, false)];
        let mut seen = FxHashSet::default();
        while let Some((cur, negated)) = stack.pop() {
            let key = if negated { cur | (1 << 31) } else { cur };
            if !seen.insert(key) {
                continue;
            }
            if let Some(v) = self.resolve_simple_bool(cur, cs) {
                return Some(if negated { 1 - v } else { v });
            }
            for info in &self.block_info {
                if let Some(&src) = info.origin.get(&cur).and_then(LocalOrigin::as_copy) {
                    stack.push((src, negated));
                }
                if let Some(LocalOrigin::Expr(Expr::Not { src })) = info.origin.get(&cur) {
                    stack.push((*src, !negated));
                }
                if let Some(LocalOrigin::Expr(Expr::And { lhs, rhs })) = info.origin.get(&cur) {
                    let a = self.resolve_simple_bool(*lhs, cs);
                    let b = self.resolve_simple_bool(*rhs, cs);
                    if let (Some(a), Some(b)) = (a, b) {
                        let r = if a == 1 && b == 1 { 1 } else { 0 };
                        return Some(if negated { 1 - r } else { r });
                    }
                }
            }
            if let Some(&src) = self.cast_chains.get(&cur) {
                stack.push((src, negated));
            }
        }
        None
    }

    /// Check whether `cur → next` is a valid `SwitchInt` transition given
    /// current discriminant constraints. Returns `false` when the transition
    /// contradicts a known discriminant value. Also records newly learned
    /// constraints from the taken branch into `constraints`.
    fn check_switch_transition(
        &self,
        cur: usize,
        next: usize,
        cs: &mut ConstraintSet,
    ) -> bool {
        let Some(terminator) = self.cfg.terminator(cur) else {
            return true;
        };
        // Base offset of the function owning `cur` (0 for the caller, the
        // callee's global start for inlined blocks). Switch targets are local
        // MIR block indices, so they must be shifted into the global space.
        let base = cur - self.cfg.block(cur).local_index;

        match &terminator.kind {
            TerminatorKind::SwitchInt { discr, targets } => {
                // The discriminant local is remapped into its function's
                // namespace so it matches `disc_info`/`constraints` keys.
                let discr_local = discr
                    .place()
                    .map(|p| self.remap_local(self.cfg.block(cur).def_id, p.local.as_usize()));
                let constraint_local = discr_local
                    .and_then(|l| self.disc_info.source_of.get(&l).copied())
                    .or(discr_local);

                // Collect all possible successor blocks for this switch.
                let all_targets: FxHashSet<usize> = targets
                    .iter()
                    .map(|(_, bb)| base + bb.as_usize())
                    .chain(std::iter::once(base + targets.otherwise().as_usize()))
                    .collect();

                if !all_targets.contains(&next) {
                    return false;
                }

                // Try to evaluate a concrete constant for the discriminant.
                let const_val = match discr {
                    Operand::Constant(c) => c
                        .const_
                        .try_eval_target_usize(
                            self.cfg.tcx,
                            TypingEnv::post_analysis(self.cfg.tcx, self.cfg.def_id),
                        )
                        .map(|v| v as usize),
                    _ => None,
                };

                // `T::IS_ZST` for a generic `T` is unevaluated; fold it to
                // `false` (non-ZST).  The `IS_ZST` guard in pointer arithmetic
                // (`add`/`sub`/`offset`) only skips redundant arithmetic (a ZST
                // pointee makes the offset a no-op), so the non-ZST path is
                // correct for ZST too and avoids the ZST branch returning `self`
                // with a stale element offset (e.g. `reverse`'s `end.sub(half_len)`
                // would otherwise return `end` unchanged and fail the downstream
                // `from_raw_parts_mut` `InBound`).
                let mut is_zst_guard = false;
                match discr {
                    Operand::Constant(c) => {
                        if let rustc_middle::mir::Const::Unevaluated(uneval, _) = c.const_
                            && mir_utils::is_sized_type_property(
                                self.cfg.tcx,
                                uneval.def,
                                "IS_ZST",
                            )
                        {
                            is_zst_guard = true;
                        }
                    }
                    Operand::Copy(p) | Operand::Move(p) => {
                        let body = self.cfg.tcx.optimized_mir(self.cfg.block(cur).def_id);
                        for bbd in body.basic_blocks.iter() {
                            for stmt in bbd.statements.iter() {
                                let rustc_middle::mir::StatementKind::Assign(assign) =
                                    &stmt.kind
                                else {
                                    continue;
                                };
                                let (dest, rvalue) = &**assign;
                                if dest != p {
                                    continue;
                                }
                                if let rustc_middle::mir::Rvalue::Use(operand, ..) = rvalue
                                    && let Operand::Constant(constant) = operand
                                    && let rustc_middle::mir::Const::Unevaluated(uneval, _) =
                                        constant.const_
                                    && mir_utils::is_sized_type_property(
                                        self.cfg.tcx,
                                        uneval.def,
                                        "IS_ZST",
                                    )
                                {
                                    is_zst_guard = true;
                                }
                            }
                        }
                    }
                    _ => {}
                }
                if is_zst_guard {
                    // Only the non-ZST (`false`) arm is reachable.
                    let expected = base + resolve_switch_target(targets, 0);
                    if next != expected {
                        return false;
                    }
                    if let Some(local) = constraint_local {
                        cs.consts.insert(local, 0);
                    }
                    return true;
                }

                if let Some(val) = const_val {
                    // Discriminant is a literal constant — only one target is
                    // reachable.
                    let expected = resolve_switch_target(targets, val as u128);
                    if next != base + expected {
                        return false;
                    }
                    if let Some(local) = constraint_local {
                        cs.consts.insert(local, val);
                    }
                    return true;
                }

                if let Some(local) = constraint_local
                    && let Some(&known_val) = cs.consts.get(&local) {
                        let expected = resolve_switch_target(targets, known_val as u128);
                        if next != base + expected {
                            return false;
                        }
                        return true;
                    }

                // A `switchInt` on `ptr as usize` (lowered `!ptr.is_null()`): the
                // `0` arm is unreachable when the pointer is known non-null.
                if let Some(discr_local) = discr_local
                    && self.local_is_known_nonnull(cs, discr_local)
                    && targets.iter().any(|(v, _)| v == 0)
                {
                    let zero_target = base + resolve_switch_target(targets, 0);
                    if next == zero_target {
                        return false;
                    }
                    return true;
                }

                // If the discriminant is a comparison like `x > 0` / `x != 0`
                // and this transition takes the branch where the comparison
                // holds (`otherwise`), mark `x` as known-nonzero so a downstream
                // `x == 0` switch branch (e.g. `RawVec::allocate_in`'s
                // zero-capacity path) is pruned.
                if let Some(discr_local) = discr_local
                    && let Some(info) = self.block_info.get(cur)
                    && let Some(LocalOrigin::Expr(Expr::Cmp { op, lhs, rhs })) =
                        info.origin.get(&discr_local).cloned()
                    && matches!(
                        (op, rhs),
                        (BinOp::Gt, Rhs::Const(0)) | (BinOp::Ge, Rhs::Const(1)) | (BinOp::Ne, Rhs::Const(0))
                    )
                    && next == base + targets.otherwise().as_usize()
                {
                    cs.consts.insert(lhs, usize::MAX);
                }

                // Try to infer the discriminant from a comparison source
                // (e.g. `_X = Ne(ptr, 0)`) when we know whether `ptr` is null.
                if let Some(discr_local) = discr_local
                    && let Some(info) = self.block_info.get(cur)
                    && let Some(LocalOrigin::Expr(Expr::Cmp { op, lhs, rhs })) =
                        info.origin.get(&discr_local).cloned()
                    && matches!(op, BinOp::Ne | BinOp::Eq)
                {
                    let is_ne = matches!(op, BinOp::Ne);
                    let pointer_is_nonnull = self.local_is_known_nonnull(cs, lhs);
                    let pointer_is_null = self.local_is_known_null(cs, lhs);
                    if pointer_is_nonnull {
                        let expected_val = if is_ne { 1 } else { 0 };
                        let expected = resolve_switch_target(targets, expected_val);
                        let val = expected_val as usize;
                        cs.consts.insert(discr_local, val);
                        if let Some(local) = constraint_local {
                            cs.consts.insert(local, val);
                        }
                        if next != base + expected {
                            return false;
                        }
                        return true;
                    }
                    if pointer_is_null {
                        let expected_val = if is_ne { 0 } else { 1 };
                        let expected = resolve_switch_target(targets, expected_val);
                        let val = expected_val as usize;
                        cs.consts.insert(discr_local, val);
                        if let Some(local) = constraint_local {
                            cs.consts.insert(local, val);
                        }
                        if next != base + expected {
                            return false;
                        }
                        return true;
                    }

                    // General Eq/Ne integer comparison: resolve both operands
                    // and prune the infeasible branch when both are known.
                    let is_eq = matches!(op, BinOp::Eq);
                    let lhs_val = self.resolve_local_value(lhs, cs);
                    let rhs_val = match rhs {
                        Rhs::Const(v) => Some(v),
                        Rhs::Local(l) => self.resolve_local_value(l, cs),
                    };
                    if let (Some(lhs_val), Some(rhs_val)) = (lhs_val, rhs_val) {
                        let val = if is_eq {
                            if lhs_val == rhs_val { 1 } else { 0 }
                        } else {
                            if lhs_val != rhs_val { 1 } else { 0 }
                        };
                        let expected = resolve_switch_target(targets, val as u128);
                        if let Some(local) = constraint_local {
                            cs.consts.insert(local, val);
                        }
                        if next != base + expected {
                            return false;
                        }
                        return true;
                    }
                }

                // Try to resolve a boolean comparison with concrete-value
                // reasoning (handles Lt/Le/Gt/Ge with fully known operands).
                // Only filter when the discriminant resolves to a definite value
                // from a comparison with BOTH operands as known constants
                // (not derived via add increments, which may be imprecise across
                // SCC boundaries).
                if let Some(discr_local) = discr_local
                    && let Some(info) = self.block_info.get(cur)
                    && let Some(LocalOrigin::Expr(Expr::Cmp { op, lhs, rhs })) =
                        info.origin.get(&discr_local).cloned()
                    && matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge)
                {
                    // Resolve LHS directly from constants (no increment chains)
                    let lhs_val = self.resolve_local_value_direct(lhs, cs);
                    let rhs_val = match rhs {
                        Rhs::Const(v) => Some(v),
                        Rhs::Local(l) => self.resolve_local_value_direct(l, cs),
                    };
                    if let (Some(lhs), Some(rhs)) = (lhs_val, rhs_val) {
                        let val = match op {
                            BinOp::Lt => {
                                if lhs < rhs {
                                    1
                                } else {
                                    0
                                }
                            }
                            BinOp::Le => {
                                if lhs <= rhs {
                                    1
                                } else {
                                    0
                                }
                            }
                            BinOp::Gt => {
                                if lhs > rhs {
                                    1
                                } else {
                                    0
                                }
                            }
                            BinOp::Ge => {
                                if lhs >= rhs {
                                    1
                                } else {
                                    0
                                }
                            }
                            _ => unreachable!(),
                        };
                        let expected = resolve_switch_target(targets, val as u128);
                        if let Some(local) = constraint_local {
                            cs.consts.insert(local, val);
                        }
                        if next != base + expected {
                            return false;
                        }
                        return true;
                    }
                }

                // Record and consult relational bounds (`lhs < rhs` /
                // `lhs <= rhs`) for order comparisons over symbolic operands.
                // An inlined `while i < bytes.len()` loop guard establishes
                // `i < bytes.len()` on the body branch, which later prunes an
                // infeasible `i >= bytes.len()` branch.
                if let Some(discr_local) = discr_local
                    && let Some(info) = self.block_info.get(cur)
                    && let Some(LocalOrigin::Expr(Expr::Cmp { op, lhs, rhs })) =
                        info.origin.get(&discr_local).cloned()
                    && matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge)
                {
                    let taken_true = next == base + resolve_switch_target(targets, 1);
                    if let Rhs::Local(rhs_local) = rhs {
                        // Canonicalize to `a < b` (strict) / `a <= b` and record
                        // the branch actually taken (its negation on the false arm).
                        let (a, b, strict) = match op {
                            BinOp::Lt => (lhs, rhs_local, true),
                            BinOp::Le => (lhs, rhs_local, false),
                            BinOp::Gt => (rhs_local, lhs, true),
                            BinOp::Ge => (rhs_local, lhs, false),
                            _ => unreachable!(),
                        };
                        if taken_true {
                            Self::record_bound(
                                cs,
                                self.canonical_field(a),
                                self.canonical_field(b),
                                strict,
                            );
                        } else {
                            Self::record_bound(
                                cs,
                                self.canonical_field(b),
                                self.canonical_field(a),
                                !strict,
                            );
                        }
                    }
                    if let Some(holds) = self.relation_status(op, lhs, rhs, cs) {
                        let expected = resolve_switch_target(targets, holds as u128);
                        if let Some(local) = constraint_local {
                            cs.consts.insert(local, holds as usize);
                        }
                        if next != base + expected {
                            return false;
                        }
                        return true;
                    }
                }

                // No prior constraint — conservatively allow any valid target
                // and record the newly learned constraint from the taken branch.
                if next == base + targets.otherwise().as_usize()
                    && let Some(local) = constraint_local
                        && let Some(num_variants) =
                            self.get_variant_count(local, self.cfg.block(cur).def_id)
                        {
                            let all_covered = (0..num_variants)
                                .all(|v| targets.iter().any(|(tv, _)| tv == v as u128));
                            if all_covered {
                                return false;
                            }
                        }

                self.learn_constraint_with_backprop(
                    cur,
                    constraint_local,
                    targets,
                    next,
                    cs,
                );

                true
            }
            _ => true,
        }
    }

    /// After learning a constraint for a discriminant local, propagate the
    /// constraint backward through the copy chain so that source locals also
    /// receive the value. This prevents losing track of the constraint when
    /// the destination temporary is reassigned on loop back-edges.
    fn learn_constraint_with_backprop(
        &self,
        cur: usize,
        constraint_local: Option<usize>,
        targets: &SwitchTargets,
        next: usize,
        cs: &mut ConstraintSet,
    ) {
        let Some(local) = constraint_local else {
            return;
        };
        let Some((val, _)) = targets.iter().find(|(_, bb)| bb.as_usize() == next) else {
            if let Some(inferred) = self.infer_otherwise_value(cur, targets, local) {
                cs.consts.insert(local, inferred);
                self.backprop_constraint(cur, local, inferred, cs);
            }
            return;
        };
        let val = val as usize;
        cs.consts.insert(local, val);
        self.backprop_constraint(cur, local, val, cs);
    }

    fn backprop_constraint(
        &self,
        cur: usize,
        local: usize,
        val: usize,
        cs: &mut ConstraintSet,
    ) {
        let Some(info) = self.block_info.get(cur) else {
            return;
        };
        let mut current = local;
        while let Some(&src) = info.origin.get(&current).and_then(LocalOrigin::as_copy) {
            if current == src {
                break;
            }
            cs.consts.insert(src, val);
            current = src;
        }
    }

    /// Recursively resolve a local's value through constraint copies,
    /// cast chains, field projections, and aggregate sources (global maps).
    /// Like `resolve_local_value` but does NOT follow increment chains.
    /// Used in conservative path filtering where we need high confidence.
    fn resolve_local_value_direct(
        &self,
        local: usize,
        cs: &ConstraintSet,
    ) -> Option<usize> {
        let mut stack = vec![local];
        let mut seen = FxHashSet::default();
        while let Some(cur) = stack.pop() {
            if !seen.insert(cur) {
                continue;
            }
            if let Some(&val) = cs.consts.get(&cur)
                && val != usize::MAX {
                    return Some(val);
                }
            for info in &self.block_info {
                if let Some(&src) = info.origin.get(&cur).and_then(LocalOrigin::as_copy) {
                    stack.push(src);
                }
                if let Some(&val) = info.origin.get(&cur).and_then(LocalOrigin::as_const) {
                    return Some(val);
                }
            }
            if let Some(&cast_src) = self.cast_chains.get(&cur) {
                stack.push(cast_src);
            }
        }
        None
    }

    fn resolve_local_value(
        &self,
        local: usize,
        cs: &ConstraintSet,
    ) -> Option<usize> {
        let mut stack = vec![(local, 0isize)];
        let mut seen = FxHashSet::default();
        while let Some((cur, offset)) = stack.pop() {
            if !seen.insert(cur) {
                continue;
            }
            if let Some(&val) = cs.consts.get(&cur) {
                if val == usize::MAX {
                    // Sentinel for known-nonnull; not a concrete integer value.
                } else if offset >= 0 {
                    return Some(val + offset as usize);
                } else {
                    return val.checked_sub((-offset) as usize);
                }
            }
            // Follow constraint copies in any block (per-block metadata).
            for info in &self.block_info {
                if let Some(&src) = info.origin.get(&cur).and_then(LocalOrigin::as_copy) {
                    stack.push((src, offset));
                }
                if let Some(&val) = info.origin.get(&cur).and_then(LocalOrigin::as_const) {
                    if offset >= 0 {
                        return Some(val + offset as usize);
                    } else {
                        return val.checked_sub((-offset) as usize);
                    }
                }
                // Follow a constant add: if cur = src + incr, the effective value
                // of cur is value_of(src) + incr + offset.
                if let Some(LocalOrigin::Expr(Expr::Add { lhs, rhs: Rhs::Const(incr_amt) })) = info.origin.get(&cur)
                {
                    stack.push((*lhs, offset + *incr_amt as isize));
                }
                // Follow remainder: cur = rem_src % rem_div.
                // Resolve rem_src recursively, compute remainder, then apply offset.
                if let Some(LocalOrigin::Expr(Expr::Rem { src: rem_src, divisor: rem_div })) = info.origin.get(&cur)
                    && let Some(src_val) = self.resolve_local_value(*rem_src, cs) {
                        let rem = src_val % *rem_div;
                        let result = if offset >= 0 {
                            Some(rem + offset as usize)
                        } else {
                            rem.checked_sub((-offset) as usize)
                        };
                        if let Some(v) = result {
                            return Some(v);
                        }
                    }
            }
            // Follow global cast chains.
            if let Some(&cast_src) = self.cast_chains.get(&cur) {
                stack.push((cast_src, offset));
            }
            // Follow field projection -> aggregate source.
            if let Some(&encoded) = self.field_projection_source.get(&cur)
                && let Some((agg_local, field_idx)) = decode_aggregate_field(encoded) {
                    let key = encode_aggregate_field(agg_local, field_idx);
                    if let Some(&source) = self.aggregate_field_sources.get(&key) {
                        stack.push((source, offset));
                    }
                }
        }
        None
    }

    /// For the "otherwise" branch of a `SwitchInt`, try to infer the single
    /// concrete value that the discriminant must have (because all other
    /// possible values are covered by explicit targets).
    fn infer_otherwise_value(
        &self,
        cur: usize,
        targets: &SwitchTargets,
        discr_local: usize,
    ) -> Option<usize> {
        let body = self.cfg.tcx.optimized_mir(self.cfg.block(cur).def_id);
        let def_id = self.cfg.block(cur).def_id;
        let original = discr_local - self.local_base_of(def_id);
        let mut discr_ty = body.local_decls[Local::from_usize(original)].ty;
        while let TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) = discr_ty.kind() {
            discr_ty = *inner;
        }

        let possible_values: Vec<usize> = match discr_ty.kind() {
            TyKind::Bool => vec![0, 1],
            TyKind::Adt(adt_def, _) if adt_def.is_enum() => (0..adt_def.variants().len()).collect(),
            _ => return None,
        };

        let explicit_values: FxHashSet<usize> = targets.iter().map(|(v, _)| v as usize).collect();
        let remaining: Vec<usize> = possible_values
            .into_iter()
            .filter(|v| !explicit_values.contains(v))
            .collect();

        if remaining.len() == 1 {
            Some(remaining[0])
        } else {
            None
        }
    }

    /// Check whether `next` is an unwind target reachable from `cur` via a
    /// call or drop terminator (may not be recorded as a normal CFG successor).
    fn is_unwind_target(&self, cur: usize, next: usize) -> bool {
        let Some(terminator) = self.cfg.terminator(cur) else {
            return false;
        };

        let unwind = match &terminator.kind {
            TerminatorKind::Call { unwind, .. }
            | TerminatorKind::Drop { unwind, .. }
            | TerminatorKind::Assert { unwind, .. } => unwind,
            _ => return false,
        };

        if let UnwindAction::Cleanup(target) = unwind {
            let base = cur - self.cfg.block(cur).local_index;
            return base + target.as_usize() == next;
        }
        false
    }

    /// Return true if `local` is known to be a non-null pointer.
    fn local_is_known_nonnull(&self, cs: &ConstraintSet, local: usize) -> bool {
        let mut stack = vec![local];
        let mut seen = FxHashSet::default();
        while let Some(cur) = stack.pop() {
            if !seen.insert(cur) {
                continue;
            }
            if let Some(&val) = cs.consts.get(&cur)
                && val > 0
            {
                return true;
            }
            for info in &self.block_info {
                if let Some(&src) = info.origin.get(&cur).and_then(LocalOrigin::as_copy) {
                    stack.push(src);
                }
            }
            if let Some(&cast_src) = self.cast_chains.get(&cur) {
                stack.push(cast_src);
            }
        }
        false
    }

    /// Return true if `local` is known to be a null pointer.
    fn local_is_known_null(&self, cs: &ConstraintSet, local: usize) -> bool {
        let mut stack = vec![local];
        let mut seen = FxHashSet::default();
        while let Some(cur) = stack.pop() {
            if !seen.insert(cur) {
                continue;
            }
            if let Some(&val) = cs.consts.get(&cur)
                && val == 0
            {
                return true;
            }
            for info in &self.block_info {
                if let Some(&src) = info.origin.get(&cur).and_then(LocalOrigin::as_copy) {
                    stack.push(src);
                }
            }
            if let Some(&cast_src) = self.cast_chains.get(&cur) {
                stack.push(cast_src);
            }
        }
        false
    }

    /// Populate the `child_sccs` field for a given SCC entry block, then
    /// recurse into those child SCCs. Called eagerly from `find_scc()` so
    /// that enumeration can be purely read-only on the graph.
    fn populate_child_sccs(&mut self, enter: usize) {
        let nodes: Vec<usize> = self.cfg.block(enter).scc.nodes.iter().cloned().collect();
        let mut child_enters = Vec::new();
        let mut seen = FxHashSet::default();

        for node in nodes {
            if let Some(block) = self.cfg.blocks.get(node) {
                let node_enter = block.scc.enter;
                let non_trivial = !block.scc.nodes.is_empty();
                if node_enter != enter && non_trivial && seen.insert(node_enter) {
                    child_enters.push(node_enter);
                }
            }
        }

        self.cfg.block_mut(enter).scc.child_sccs = child_enters;

        let child_count = self.cfg.block(enter).scc.child_sccs.len();
        for i in 0..child_count {
            let child_enter = self.cfg.block(enter).scc.child_sccs[i];
            self.populate_child_sccs(child_enter);
        }
    }

    fn populate_all_child_sccs(&mut self) {
        let mut visited = FxHashSet::default();
        let block_count = self.cfg.blocks.len();
        for i in 0..block_count {
            let scc = &self.cfg.block(i).scc;
            let enter = scc.enter;
            if scc.nodes.is_empty() || !visited.insert(enter) {
                continue;
            }
            self.populate_child_sccs(enter);
        }
    }
}

/// Hash of the constraint state accumulated along a path prefix.
///
/// Computed by walking the prefix, collecting `(local → constant_value)`
/// bindings from each block's [`BlockFacts`], sorting them, and
/// hashing the result.  Used by [`PathEnumerator::visited_sccs`] to
/// skip redundant re-entries into the same SCC with the same state.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, Default)]
pub struct ConstraintHash(u64);

impl ConstraintHash {
    fn from_path(path: &[usize], graph: &PathGraph<'_>) -> Self {
        let mut hasher = DefaultHasher::new();
        let mut constraints: ConstraintSet = ConstraintSet::default();

        for &block in path.iter() {
            if let Some(info) = graph.block_info.get(block) {
                for local in &info.assigned_locals {
                    if let Some(&src) = info.origin.get(local).and_then(LocalOrigin::as_copy) {
                        if let Some(&src_val) = constraints.consts.get(&src) {
                            constraints.consts.insert(*local, src_val);
                            continue;
                        }
                        if let Some(&dst_val) = constraints.consts.get(local) {
                            constraints.consts.insert(src, dst_val);
                            constraints.consts.insert(*local, dst_val);
                            continue;
                        }
                    }
                    if let Some(&val) = info.origin.get(local).and_then(LocalOrigin::as_const) {
                        constraints.consts.insert(*local, val);
                        continue;
                    }
                    constraints.consts.remove(local);
                }
            }
        }

        let mut entries: Vec<(usize, usize)> = constraints.consts.into_iter().collect();
        entries.sort();
        entries.hash(&mut hasher);
        ConstraintHash(hasher.finish())
    }
}

/// Key for [`PathEnumerator::scc_paths`] and [`PathEnumerator::visited_sccs`] and [`PathEnumerator::visited_sccs`]:
/// which SCC entry block, with what constraint state, and how many
/// additional postfix repeats are allowed.
///
/// In `scc_paths` the `constraint` field is unused (cache keyed by
/// `entry` + `repeat`); in `visited_sccs` the `repeat` field is
/// unused (deduplicated by `entry` + `constraint`).
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct SccKey {
    pub entry: usize,
    pub repeat: usize,
    pub constraint: ConstraintHash,
}

/// Builds a [`PathTree`] by depth-first enumeration of whole-CFG paths.
///
/// The enumerator holds a `&PathGraph` (which must have `find_scc()` called
/// beforehand) and two caches:
///
/// The **constraint hash** used by `visited_sccs` is a
/// [`ConstraintHash`]: it walks the current path prefix, accumulates
/// `(local → constant_value)` bindings from each block's
/// [`BlockFacts`], sorts them, and hashes the result.  Different
/// constraint states (e.g. a loop variable changing from `true` to
/// `false`) produce different hashes.
///
/// 1. `scc_paths` — maps [`SccKey`] to a list of acyclic paths through
///    that SCC.  Reused across repeated enumerations of the same function
///    with different repeat counts.
///
/// 2. `visited_sccs` — set of [`SccKey`] entries already explored
///    (matched by `entry` + `constraint`, ignoring `repeat`).
///    When the same SCC is reached with the same constraint state, its
///    sub-paths are identical, so the re-entry is skipped.
///
/// Constraint-based filtering runs incrementally during DFS via
/// [`PathGraph::check_transition`], so only feasible paths are inserted
/// into the resulting tree.
pub struct PathEnumerator<'g, 'tcx> {
    graph: &'g PathGraph<'tcx>,
    scc_paths: FxHashMap<SccKey, Vec<SccPath>>,
    visited_sccs: FxHashSet<SccKey>,
}

impl<'g, 'tcx> PathEnumerator<'g, 'tcx> {
    pub fn new(graph: &'g PathGraph<'tcx>) -> Self {
        PathEnumerator {
            graph,
            scc_paths: FxHashMap::default(),
            visited_sccs: FxHashSet::default(),
        }
    }

    /// Enumerate all whole-CFG paths, pruning infeasible transitions via
    /// incremental constraint-based filtering during DFS.
    ///
    /// SCC regions are flattened into a bounded set of acyclic paths.
    pub fn enumerate_paths(&mut self) -> PathTree {
        self.enumerate_paths_repeat(0)
    }

    /// Enumerate whole-CFG paths allowing each SCC postfix segment to repeat
    /// up to `postfix_repeat` additional times. `postfix_repeat = 0` gives
    /// the same result as `enumerate_paths`.
    ///
    /// Enumeration stops once [`crate::limit::path_limit`] paths are
    /// collected and the tree is marked truncated.
    pub fn enumerate_paths_repeat(&mut self, postfix_repeat: usize) -> PathTree {
        let mut tree = PathTree::new();

        if self.graph.cfg.blocks.is_empty() {
            return tree;
        }

        self.collect_whole_cfg_paths(
            0,
            &mut vec![0],
            &mut tree,
            0,
            postfix_repeat,
            &ConstraintSet::default(),
        );

        tree
    }

    /// Enumerate all acyclic paths through `scc` starting at `start`,
    /// allowing each postfix segment to repeat up to `postfix_repeat`
    /// additional times.
    ///
    /// Results are cached per `(def_id, scc_enter, postfix_repeat)`.
    pub fn find_scc_paths_repeat(
        &mut self,
        start: usize,
        scc: &SccInfo,
        postfix_repeat: usize,
    ) -> Vec<SccPath> {
        let cache_key = SccKey {
            entry: scc.enter,
            repeat: postfix_repeat,
            constraint: ConstraintHash::default(),
        };
        if let Some(cached) = self.scc_paths.get(&cache_key) {
            return cached.clone();
        }

        let mut out = Vec::new();
        let mut seen: FxHashSet<Vec<usize>> = FxHashSet::default();
        let mut path = vec![start];
        let mut segment_counts = FxHashMap::default();

        self.dfs_scc_tree(
            scc,
            start,
            &mut path,
            &mut segment_counts,
            postfix_repeat,
            &mut out,
            &mut seen,
            0,
        );

        if self.scc_paths.len() >= SCC_PATH_CACHE_LIMIT {
            self.scc_paths.clear();
        }
        self.scc_paths.insert(cache_key, out.clone());

        out
    }

    /// Recursive DFS through one level of the SCC tree.
    ///
    /// Enumerates structurally possible paths through the SCC to exit points.
    /// No constraint tracking — `check_postfix_segment` prunes repeated
    /// loop-body segments purely by block-id sequence.
    ///
    /// When `postfix_repeat > 0`, allows the same postfix segment to repeat
    /// up to `postfix_repeat` additional times beyond the first occurrence.
    ///
    /// Child SCC paths are pre-enumerated via `find_scc_paths_repeat` and treated as
    /// atomic building blocks (no recursive descent into child SCC internals).
    #[allow(clippy::too_many_arguments)]
    fn dfs_scc_tree(
        &mut self,
        scc: &SccInfo,
        cur: usize,
        path: &mut Vec<usize>,
        segment_counts: &mut FxHashMap<Vec<usize>, usize>,
        postfix_repeat: usize,
        out: &mut Vec<SccPath>,
        seen_paths: &mut FxHashSet<Vec<usize>>,
        depth: usize,
    ) {
        if depth > SCC_MAX_DEPTH {
            return;
        }
        if out.len() >= SCC_MAX_SEEN_PATHS {
            return;
        }
        if path.len() > SCC_MAX_PATH_LEN {
            return;
        }
        if cur != scc.enter && !scc.nodes.contains(&cur) {
            return;
        }

        if cur == scc.enter && path.len() > 1
            && !check_postfix_segment(path, scc.enter, segment_counts, postfix_repeat) {
                if (postfix_repeat > 0 || segment_counts.len() > 1)
                    && scc.exits.iter().any(|e| e.exit == cur)
                {
                    self.record_unique_path(path, scc, out, seen_paths);
                }
                return;
            }

        if scc.exits.iter().any(|e| e.exit == cur) {
            self.record_unique_path(path, scc, out, seen_paths);
        }

        let is_child = scc.child_sccs.contains(&cur);

        if is_child {
            let ctx = self.constraint_context(path);
            if !self.visited_sccs.insert(SccKey {
                entry: cur,
                repeat: 0,
                constraint: ctx,
            }) {
                return;
            }

            let child_scc = self.graph.cfg_block(cur).scc.clone();
            let child_paths = self.find_scc_paths_repeat(cur, &child_scc, postfix_repeat);

            for child_path in &child_paths {
                let orig_len = path.len();
                if child_path.blocks.len() > 1 {
                    path.extend(&child_path.blocks[1..]);
                }

                let mut branch_counts = segment_counts.clone();
                for &next in &child_path.exit_successors {
                    path.push(next);
                    self.dfs_scc_tree(
                        scc,
                        next,
                        path,
                        &mut branch_counts,
                        postfix_repeat,
                        out,
                        seen_paths,
                        depth + 1,
                    );
                    path.pop();
                }
                path.truncate(orig_len);
            }
            return;
        }

        let successors: Vec<usize> = self.graph.cfg.block(cur).next.iter().copied().collect();
        let saved_counts = segment_counts.clone();
        for next in successors {
            if next != scc.enter && !scc.nodes.contains(&next) {
                self.record_unique_path(path, scc, out, seen_paths);
                continue;
            }
            let mut branch_counts = saved_counts.clone();
            path.push(next);
            self.dfs_scc_tree(
                scc,
                next,
                path,
                &mut branch_counts,
                postfix_repeat,
                out,
                seen_paths,
                depth + 1,
            );
            path.pop();
        }
    }

    /// Build a [`ConstraintHash`] from the constraint state along `path`.
    fn constraint_context(&self, path: &[usize]) -> ConstraintHash {
        ConstraintHash::from_path(path, self.graph)
    }

    /// Depth-first enumeration of all CFG paths from `current` to a terminator.
    ///
    /// SCC nodes are flattened via `find_scc_paths_repeat`; non-SCC blocks are followed
    /// one by one.  No cycle detection is needed because the post-SCC CFG is a DAG.
    /// Constraints are maintained incrementally — each transition is checked
    /// via `PathGraph::check_transition` before recursing, and infeasible
    /// branches are pruned early.
    fn collect_whole_cfg_paths(
        &mut self,
        current: usize,
        path: &mut Vec<usize>,
        tree: &mut PathTree,
        depth: usize,
        postfix_repeat: usize,
        cs: &ConstraintSet,
    ) {
        if current >= self.graph.cfg.blocks.len() {
            return;
        }
        if depth > WHOLE_CFG_PATH_DEPTH_LIMIT
            || tree.len() >= crate::limit::path_limit()
        {
            tree.mark_truncated();
            return;
        }

        let scc_info = self.graph.cfg_block(current).scc.clone();
        let is_scc = current == scc_info.enter && !scc_info.nodes.is_empty();
        if is_scc {
            let scc = self.sort_scc_tree(&scc_info);
            let segments = self.find_scc_paths_repeat(current, &scc, postfix_repeat);

            if segments.is_empty() {
                tree.insert(path);
                return;
            }

            for seg in segments {
                if tree.len() >= crate::limit::path_limit() {
                    tree.mark_truncated();
                    break;
                }

                let orig_len = path.len();
                let mut seg_constraints = cs.clone();
                let mut reachable = true;

                if seg.blocks.len() > 1 {
                    for i in 0..seg.blocks.len() - 1 {
                        if !self.graph.check_transition(
                            seg.blocks[i],
                            seg.blocks[i + 1],
                            &mut seg_constraints,
                        ) {
                            reachable = false;
                            break;
                        }
                    }
                    if reachable {
                        path.extend_from_slice(&seg.blocks[1..]);
                    }
                }

                if reachable {
                    if seg.exit_successors.is_empty() {
                        tree.insert(path);
                    } else {
                        for &next in &seg.exit_successors {
                            let mut next_constraints = seg_constraints.clone();
                            let last = *path.last().unwrap();
                            if self
                                .graph
                                .check_transition(last, next, &mut next_constraints)
                            {
                                path.push(next);
                                self.collect_whole_cfg_paths(
                                    next,
                                    path,
                                    tree,
                                    depth + 1,
                                    postfix_repeat,
                                    &next_constraints,
                                );
                                path.pop();
                            }
                        }
                    }
                }

                path.truncate(orig_len);
            }
            return;
        }

        // Non-SCC block: follow CFG successors.
        let successors: Vec<usize> = self.graph.cfg_block(current).next.iter().copied().collect();
        if successors.is_empty() {
            tree.insert(path);
            return;
        }

        for next in successors {
            let mut next_constraints = cs.clone();
            if self
                .graph
                .check_transition(current, next, &mut next_constraints)
            {
                path.push(next);
                self.collect_whole_cfg_paths(
                    next,
                    path,
                    tree,
                    depth + 1,
                    postfix_repeat,
                    &next_constraints,
                );
                path.pop();
            }
        }
    }

    fn sort_scc_tree(&self, scc: &SccInfo) -> SccInfo {
        self.graph.cfg_block(scc.enter).scc.clone()
    }

    fn record_unique_path(
        &self,
        path: &[usize],
        scc: &SccInfo,
        out: &mut Vec<SccPath>,
        seen_paths: &mut FxHashSet<Vec<usize>>,
    ) {
        if !seen_paths.insert(path.to_vec()) {
            return;
        }
        let exit_successors = self.compute_exit_successors(path, scc);
        out.push(SccPath {
            blocks: path.to_vec(),
            exit_successors,
        });
    }

    fn compute_exit_successors(&self, path: &[usize], scc: &SccInfo) -> Vec<usize> {
        let Some(&last) = path.last() else {
            return vec![];
        };
        scc.exits
            .iter()
            .filter(|e| e.exit == last)
            .map(|e| e.to)
            .filter(|&n| {
                !scc.child_sccs
                    .contains(&self.graph.cfg.block(n).scc.enter())
            })
            .collect()
    }
}

/// Resolve a concrete discriminant value to the corresponding `SwitchInt`
/// successor block index.
fn resolve_switch_target(targets: &SwitchTargets, val: u128) -> usize {
    targets
        .iter()
        .find(|(v, _)| *v == val)
        .map(|(_, bb)| bb.as_usize())
        .unwrap_or_else(|| targets.otherwise().as_usize())
}
