use annotate_snippets::Level;

use crate::{analysis::dataflow::*, check::opt::OptCheck};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use crate::check::opt::check_utils::node_matches_any_call;
use crate::check::opt::report::OptReport;

/// `s = s + x` desugars to a call of the trait method `ops::Add::add`
/// (MIR keeps the trait-level def, not the impl method). Match any
/// `Add::add` call; the self-update check below filters to the
/// accumulating form. Refinement TODO: restrict the receiver type to
/// `String` once types are available on graph locals.
fn is_add_call(tcx: &TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.def_path_str(def_id).ends_with("ops::Add::add")
}

/// Detects the quadratic string-building idiom `s = s + x` (String `Add`
/// whose result is moved back into the receiver). Every `+` on a `String`
/// reallocates the whole buffer, so accumulating in a loop is O(n^2);
/// `push_str` / `write!` append in place.
pub struct StringAddCheck {
    record: Vec<Span>,
}

impl OptCheck for StringAddCheck {
    fn new() -> Self {
        Self { record: vec![] }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let debug = std::env::var("RAPX_DEBUG_STRING_ADD").is_ok();
        let mut cand = 0usize;
        let mut fired = 0usize;
        for (idx, node) in graph.nodes.iter_enumerated() {
            if !node_matches_any_call(node, |d| is_add_call(tcx, d)) {
                continue;
            }
            cand += 1;
            // receiver = first argument (`self` in `impl Add<&str> for String`)
            let Some(self_edge) = node.in_edges.first() else {
                continue;
            };
            let receiver = graph.edges[*self_edge].src;
            // self-update idiom: the call result is moved back into the receiver
            // the receiver is usually a temp moved out of the accumulating
            // local; recover that local by following the receiver's own
            // incoming edge (acc -> temp_recv, add -> acc)
            let acc_local = graph
                .edges
                .iter()
                .find(|e| e.dst == receiver && e.src != idx)
                .map(|e| e.src)
                .unwrap_or(receiver);
            // self-update idiom: the call result is moved back into acc_local
            let updates_self = graph.edges.iter().any(|e| {
                e.src == idx && e.dst == acc_local && matches!(e.op, EdgeOp::Move)
            });
            if debug {
                eprintln!(
                    "[string_add-debug] node={idx:?} receiver={receiver:?} updates_self={updates_self} in_edges={:?}",
                    node.in_edges
                );
                for e in graph.edges.iter() {
                    eprintln!("[string_add-debug] edge {:?} -> {:?} op={:?} seq={}", e.src, e.dst, e.op, e.seq);
                }
            }
            if updates_self {
                fired += 1;
                self.record.push(node.span);
            }
        }
        if debug {
            let mut calls: Vec<String> = Vec::new();
            for node in graph.nodes.iter() {
                for op in node.ops.iter() {
                    if let NodeOp::Call(d) = op {
                        calls.push(tcx.def_path_str(*d));
                    }
                }
            }
            calls.sort();
            calls.dedup();
            eprintln!("[string_add-debug] calls={calls:?}");
            eprintln!(
                "[string_add-debug] nodes={} edges={} candidates={cand} fired={fired}",
                graph.nodes.len(),
                graph.edges.len()
            );
        }
    }

    fn report(&self, graph: &Graph) {
        for span in self.record.iter() {
            OptReport::from_graph(graph)
                .title("Quadratic string concatenation detected")
                .annotate(
                    Level::Error,
                    *span,
                    "String is reallocated on every `+` here.",
                )
                .footer("Use `push_str` (or `write!`) to append in place.")
                .emit();
        }
    }

    fn cnt(&self) -> usize {
        self.record.len()
    }
}
