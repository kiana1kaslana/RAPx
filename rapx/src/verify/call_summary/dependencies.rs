//! Dependency summaries derived from MIR for local callees.
//!
//! When no hand-written effect exists, this module inspects a callee's own MIR
//! to approximate its return dependencies and must-write arguments.

use std::collections::{HashMap, HashSet, VecDeque};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        BasicBlock, Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
    },
    ty::TyCtxt,
};

use crate::analysis::dataflow::{DataflowAnalysis, default::DataflowAnalyzer};
use crate::analysis::path::graph::{PathEnumerator, PathGraph};
use crate::helpers::mir_utils as helpers;


/// Trace backward from an operand (inner call arg) through Copy/Move/Cast/
/// Ref/RawPtr assignments to the outer callee's argument local, returning its
/// index. `Ref`/`RawPtr` are treated as data-flow too, which is an
/// approximation (taking a reference is not a pure copy) but is adequate for
/// wrapper recognition.
fn trace_to_callee_arg<'tcx>(
    body: &rustc_middle::mir::Body<'tcx>,
    operand: &Operand<'_>,
) -> Option<usize> {
    let local = match operand {
        Operand::Copy(place) | Operand::Move(place) => place.local,
        _ => return None,
    };
    trace_local_to_callee_arg(body, local)
}

fn trace_local_to_callee_arg(
    body: &rustc_middle::mir::Body<'_>,
    local: rustc_middle::mir::Local,
) -> Option<usize> {
    let mut queue = VecDeque::from([local]);
    let mut seen = HashSet::from([local]);
    while let Some(current) = queue.pop_front() {
        let cidx = current.as_usize();
        if cidx >= 1 && cidx <= body.arg_count {
            return Some(cidx - 1);
        }
        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                let StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let dest = assign.0.local;
                if dest != current {
                    continue;
                }
                let source = match &assign.1 {
                    Rvalue::Use(Operand::Copy(place), ..)
                    | Rvalue::Use(Operand::Move(place), ..)
                    | Rvalue::Cast(_, Operand::Copy(place), _)
                    | Rvalue::Cast(_, Operand::Move(place), _)
                    | Rvalue::Ref(_, _, place)
                    | Rvalue::RawPtr(_, place)
                    | Rvalue::CopyForDeref(place) => place.local,
                    _ => continue,
                };
                if !seen.contains(&source) {
                    seen.insert(source);
                    queue.push_back(source);
                }
            }
            let Some(terminator) = &bb.terminator else {
                continue;
            };
            let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &terminator.kind
            else {
                continue;
            };
            if destination.local != current {
                continue;
            }
            // Trace through pointer-preserving calls: `as_ptr`/`as_mut_ptr`
            // (and friends) return the pointee address, while `add`/`sub`/
            // `offset` return the base pointer shifted by an offset — the
            // provenance (and thus the written-through arg) is carried by
            // their first (base/receiver) argument.
            let callee = helpers::dep_callee_def_id(func);
            let traces_base = crate::verify::api_classify::is_as_ptr(callee)
                || crate::verify::api_classify::is_pointer_add(callee)
                || crate::verify::api_classify::is_pointer_sub(callee);
            if !traces_base {
                continue;
            }
            let Some(source) = args.first().and_then(|arg| match &arg.node {
                Operand::Copy(place) | Operand::Move(place) => Some(place.local),
                Operand::Constant(_) => None,
                #[cfg(rapx_ge_95)]
                Operand::RuntimeChecks(_) => None,
            }) else {
                continue;
            };
            if !seen.contains(&source) {
                seen.insert(source);
                queue.push_back(source);
            }
        }
    }
    None
}

/// Use the existing dataflow graph to approximate callee return deps.
/// Works for any callee with available MIR (local or cross-crate `#[inline]`).
pub(super) fn local_return_dependencies(tcx: TyCtxt<'_>, callee: DefId) -> Option<Vec<usize>> {
    if !tcx.is_mir_available(callee) {
        return None;
    }
    helpers::catch_panic(|| {
        let mut analyzer = DataflowAnalyzer::new(tcx, false);
        analyzer.build_graph(callee);
        let deps = analyzer.get_fn_arg2ret(callee);
        deps.iter_enumerated()
            .filter_map(|(local, depends)| {
                if *depends && local.as_usize() > 0 {
                    Some(local.as_usize() - 1)
                } else {
                    None
                }
            })
            .collect()
    })
    .ok()
}

/// Memo keyed by `(callee, depth)`, shared within a single
/// `local_write_args` recursion.
type WriteMemo = HashMap<(DefId, usize), Option<HashSet<usize>>>;

/// Return callee argument indices that are written. Works for any callee with
/// available MIR, and follows wrapper calls (`Vec::push` → `push_mut`) with
/// bounded depth.
pub(super) fn local_write_args(
    tcx: TyCtxt<'_>,
    callee: DefId,
) -> Option<Vec<usize>> {
    write_args_rec(tcx, callee, 0, &mut HashMap::new())
        .map(|set| set.into_iter().collect())
}

fn write_args_rec(
    tcx: TyCtxt<'_>,
    callee: DefId,
    depth: usize,
    memo: &mut WriteMemo,
) -> Option<HashSet<usize>> {
    if depth > 4 {
        return None;
    }
    if !tcx.is_mir_available(callee) {
        return None;
    }
    if tcx.intrinsic(callee).is_some() || helpers::is_drop_in_place(callee) {
        return None;
    }
    let key = (callee, depth);
    if let Some(summary) = memo.get(&key) {
        return summary.clone();
    }

    let summary = helpers::catch_panic(|| {
        let body = tcx.optimized_mir(callee);
        let mut graph = PathGraph::new(tcx, callee);
        graph.find_scc();
        let mut enumerator = PathEnumerator::new(&graph);
        let paths = enumerator.enumerate_paths_repeat(0);
        if paths.is_truncated() {
            return None;
        }

        let mut write: Option<HashSet<usize>> = None;
        for path in paths.iter() {
            if !path_ends_in_return(body, &path) {
                continue;
            }
            let writes = write_args_on_path(tcx, body, &path, depth, memo);
            write = Some(match write {
                Some(mut current) => {
                    current.extend(writes);
                    current
                }
                None => writes,
            });
        }

        Some(write.unwrap_or_default())
    })
    .ok()
    .flatten();
    memo.insert(key, summary.clone());
    summary
}

fn path_ends_in_return(body: &rustc_middle::mir::Body<'_>, path: &[usize]) -> bool {
    path.last().is_some_and(|block| {
        body.basic_blocks
            .get(BasicBlock::from_usize(*block))
            .and_then(|data| data.terminator.as_ref())
            .is_some_and(|terminator| matches!(terminator.kind, TerminatorKind::Return))
    })
}

fn write_args_on_path<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    path: &[usize],
    depth: usize,
    memo: &mut WriteMemo,
) -> HashSet<usize> {
    let mut writes = HashSet::new();
    for block in path {
        let Some(data) = body.basic_blocks.get(BasicBlock::from_usize(*block)) else {
            continue;
        };

        // Direct writes through `&mut` args: `*self = ...`, `(*self).0 = ...`.
        for stmt in &data.statements {
            let StatementKind::Assign(assign) = &stmt.kind else {
                continue;
            };
            let dest = &assign.0;
            if dest.projection.first() == Some(&ProjectionElem::Deref)
                && let Some(arg) = trace_local_to_callee_arg(body, dest.local) {
                    writes.insert(arg);
                }
        }

        let Some(terminator) = data.terminator.as_ref() else {
            continue;
        };
        let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
            continue;
        };

        // `ptr::write`-style writes: trace the pointer arg to a callee arg.
        if crate::verify::api_classify::is_ptr_write(helpers::dep_callee_def_id(func)) {
            if let Some(pointer_arg) = args
                .first()
                .and_then(|arg| trace_to_callee_arg(body, &arg.node))
            {
                writes.insert(pointer_arg);
            }
            continue;
        }

        if crate::verify::api_classify::is_ptr_copy(helpers::dep_callee_def_id(func)) {
            if let Some(destination_arg) = args
                .get(1)
                .and_then(|arg| trace_to_callee_arg(body, &arg.node))
            {
                writes.insert(destination_arg);
            }
            continue;
        }

        // Wrapper calls: a nested callee that writes its own args maps those
        // writes back onto this callee's args.
        if let Some(nested) = helpers::dep_callee_def_id(func)
            && let Some(nested_writes) = write_args_rec(tcx, nested, depth + 1, memo)
        {
            for (i, arg) in args.iter().enumerate() {
                if nested_writes.contains(&i)
                    && let Some(outer) = trace_to_callee_arg(body, &arg.node) {
                        writes.insert(outer);
                    }
            }
        }
    }
    writes
}

