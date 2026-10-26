//! Path extraction for verification targets.
//!
//! This module builds finite, acyclic paths from a function CFG to each unsafe checkpoint
//! so that the verifier can reason about pointer properties along concrete execution
//! traces without unrolling loops or recursive cycles.
//!
//! # Path reachability
//!
//! Each path is validated against a `PathGraph` (an SCC-aware path enumeration
//! structure) to ensure the computed block sequence is actually reachable. Paths
//! that fail this check are silently discarded.
//!
//! # Path limit
//!
//! To prevent exponential blow-up, path enumeration is capped at
//! [`crate::limit::path_limit`] (the `--path-limit` CLI value, or
//! [`crate::limit::PATH_LIMIT`]). Enumeration stops producing new paths once
//! the limit is reached and the tree is marked truncated.

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::BasicBlock,
    ty::{EarlyBinder, Instance, TyCtxt, TypingEnv},
};

use crate::analysis::path::{
    PathTree,
    graph::{PathEnumerator, PathGraph},
};

use crate::verify::checkpoint::CheckpointLocation;

/// Enumerates finite, acyclic verification paths from function entry to each
/// unsafe checkpoint in one function body.
///
/// `run` builds a [`PathGraph`], inlines callees, finds SCCs, then enumerates
/// acyclic paths with `allow_repeat` extra loop iterations.  The resulting
/// [`PathTree`] holds all whole-CFG paths; checkpoints and struct invariants
/// slice their own prefixes from it via `walk_prefixes`/`subtree_to`.
///
/// Enumeration is capped at [`crate::limit::path_limit`] to avoid exponential
/// blow-up.
pub(crate) struct PathExtractor<'tcx> {
    /// Compiler type context used for MIR access and name resolution.
    tcx: TyCtxt<'tcx>,
    /// The function whose MIR body is being analyzed.
    def_id: DefId,
    /// Number of extra SCC postfix repetitions allowed (default 0).
    allow_repeat: usize,
    /// An optional monomorphized instance; when set, `run` verifies the
    /// instance's instantiated body instead of `optimized_mir(def_id)`.
    instance: Option<Instance<'tcx>>,
}

impl<'tcx> PathExtractor<'tcx> {
    /// Create a path extractor that verifies `def_id`, optionally against a
    /// monomorphized instance body (when `instance` is `Some`).
    ///
    /// Path extraction (SCC detection, enumeration, filtering) is deferred
    /// until [`run`] is called.
    ///
    /// `allow_repeat` controls how many times a repeated SCC postfix segment
    /// is allowed beyond the first occurrence. Default is 0 (no extra repeats).
    pub(crate) fn new_with_instance(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        allow_repeat: usize,
        instance: Option<Instance<'tcx>>,
    ) -> Self {
        Self {
            tcx,
            def_id,
            allow_repeat,
            instance,
        }
    }

    /// Run path extraction, consuming the extractor.
    ///
    /// Returns the whole-CFG [`PathTree`], with inlined callees and the
    /// block-function metadata attached.
    pub(crate) fn run(self) -> PathTree {
        let body = match self.instance {
            Some(inst) => {
                let mir = self.tcx.optimized_mir(self.def_id);
                inst.instantiate_mir_and_normalize_erasing_regions(
                    self.tcx,
                    TypingEnv::post_analysis(self.tcx, self.def_id),
                    EarlyBinder::bind(self.tcx, mir.clone()),
                )
            }
            None => self.tcx.optimized_mir(self.def_id).clone(),
        };
        let mut graph = PathGraph::new_with_body(self.tcx, self.def_id, &body);
        let caller_block_count = graph.cfg.blocks.len();
        let caller_has_branch = graph.cfg.blocks.iter().any(|block| block.next.len() > 1);
        graph.inline_callees();
        graph.find_scc();
        let mut structural = false;
        let mut tree = {
            let mut enumerator = PathEnumerator::new(&graph);
            if !caller_has_branch || graph.inlined_call_blocks.is_empty() {
                enumerator.enumerate_paths_repeat(self.allow_repeat)
            } else {
                let mut caller_graph = PathGraph::new_with_body(self.tcx, self.def_id, &body);
                caller_graph.find_scc();
                if caller_graph
                    .cfg
                    .blocks
                    .iter()
                    .any(|block| !block.scc.nodes.is_empty())
                {
                    enumerator.enumerate_paths_repeat(self.allow_repeat)
                } else {
                    let caller_paths = PathEnumerator::new(&caller_graph)
                        .enumerate_paths_repeat(self.allow_repeat);
                    if caller_paths.len() <= 1 {
                        enumerator.enumerate_paths_repeat(self.allow_repeat)
                    } else {
                        structural = true;
                        PathEnumerator::new_context_insensitive(&graph)
                            .enumerate_paths_caller_first(
                                &caller_paths,
                                caller_block_count,
                                self.allow_repeat,
                            )
                    }
                }
            }
        };
        if structural {
            tree.mark_structural();
        }
        tree.set_block_fn(
            graph
                .cfg
                .blocks
                .iter()
                .map(|b| (b.def_id, b.local_index))
                .collect(),
            graph.inline_bindings.clone(),
            graph.inline_parents.clone(),
            graph.inlined_call_blocks.clone(),
        );
        tree
    }
}

/// One finite, acyclic execution trace from function entry to a checkpoint,
/// represented as an ordered sequence of MIR basic blocks.
///
/// Built by the [`BackwardSlicer`](super::slicer::BackwardSlicer) from the
/// [`PathTree`] produced by [`PathExtractor`]; the VM later consumes it to
/// know which MIR instructions are relevant and in what order.
///
/// Every path is validated against the SCC-aware [`PathGraph`]; unreachable
/// sequences are silently discarded during extraction.
#[derive(Clone, Debug)]
pub(crate) struct Path {
    /// The [`CheckpointLocation`] (function + basic block) reached by this
    /// path, also recorded as the final `PathStep::Checkpoint`.
    pub target: CheckpointLocation,
    /// Ordered block sequence from function entry to `target`, terminated by a
    /// `PathStep::Checkpoint`.
    pub steps: Vec<PathStep>,
}

impl Path {
    /// Render this path as a compact array of block indices.
    pub(crate) fn describe_indices(&self) -> String {
        let mut indices: Vec<usize> = Vec::new();
        for step in &self.steps {
            match step {
                PathStep::Block(b) => indices.push(b.as_usize()),
                PathStep::Checkpoint(l) => {
                    let bb = l.block.as_usize();
                    if indices.last() != Some(&bb) {
                        indices.push(bb);
                    }
                }
            }
        }
        format!("{:?}", indices)
    }
}

/// One step in a finite verification path.
#[derive(Clone, Debug)]
pub(crate) enum PathStep {
    /// A normal MIR basic block.
    Block(BasicBlock),
    /// The target checkpoint that terminates the path.
    Checkpoint(CheckpointLocation),
}
