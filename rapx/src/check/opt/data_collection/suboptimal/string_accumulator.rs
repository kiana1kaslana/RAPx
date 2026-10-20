//! String Add already reuses its buffer; only an explicit prefix clone
//! creates the repeated-copy candidate recognized here.
use crate::{
    analysis::dataflow::Graph,
    check::opt::{OptCheck, report::OptReport},
};
use annotate_snippets::Level;
use rustc_ast::BinOpKind;
use rustc_hir::{Expr, ExprKind, HirId, QPath, def::Res, intravisit};
use rustc_middle::ty::{self, TyCtxt, TypeckResults};
use rustc_span::Span;

crate::def_paths! {
    clone: "std::clone::Clone::clone",
    string: "std::string::String",
}

pub struct StringAccumulatorCheck {
    record: Vec<Span>,
}

impl OptCheck for StringAccumulatorCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }
    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let Some(local) = graph.def_id.as_local() else {
            return;
        };
        let Some(body) = tcx.hir_maybe_body_owned_by(local) else {
            return;
        };
        let paths = DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        let mut finder = Finder {
            tcx: *tcx,
            typeck: tcx.typeck(local),
            clone: paths.clone.last_def_id(),
            string: paths.string.last_def_id(),
            loops: Vec::new(),
            record: Vec::new(),
        };
        intravisit::walk_body(&mut finder, body);
        self.record = finder.record;
    }
    fn report(&self, graph: &Graph) {
        for &span in &self.record {
            OptReport::from_graph(graph)
                .title("Repeated String accumulator cloning")
                .annotate(Level::Info, span, "This copies the accumulated prefix before appending.")
                .footer("Consider push_str or += when the suffix can be borrowed independently. Repeated growth can make prefix copying quadratic; benchmark the workload.")
                .emit();
        }
    }
    fn cnt(&self) -> usize {
        self.record.len()
    }
}

struct Finder<'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'tcx TypeckResults<'tcx>,
    clone: rustc_hir::def_id::DefId,
    string: rustc_hir::def_id::DefId,
    loops: Vec<&'tcx Expr<'tcx>>,
    record: Vec<Span>,
}
fn local(expr: &Expr<'_>) -> Option<HirId> {
    if let ExprKind::Path(QPath::Resolved(_, path)) = expr.kind
        && let Res::Local(id) = path.res
    {
        Some(id)
    } else {
        None
    }
}
impl<'tcx> intravisit::Visitor<'tcx> for Finder<'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if let ExprKind::Loop(..) = expr.kind {
            self.loops.push(expr);
            intravisit::walk_expr(self, expr);
            self.loops.pop();
            return;
        }

        if let Some(loop_span) = self.loops.last()
            && let ExprKind::Assign(lhs, rhs, _) = expr.kind
            && let Some(accumulator) = local(lhs)
            && !loop_span.span.contains(self.tcx.hir_span(accumulator))
            && let ty::Adt(adt, _) = self.typeck.expr_ty(lhs).kind()
            && adt.did() == self.string
            && let ExprKind::Binary(op, prefix, _) = rhs.kind
            && op.node == BinOpKind::Add
            && let ExprKind::MethodCall(_, receiver, [], _) = prefix.kind
            && local(receiver) == Some(accumulator)
            && self.typeck.type_dependent_def_id(prefix.hir_id) == Some(self.clone)
            && !has_other_mutation(loop_span, accumulator, expr.hir_id)
        {
            self.record.push(expr.span);
        }
        intravisit::walk_expr(self, expr);
    }
}

// A reset inside the loop defeats the growing-prefix argument. Conservatively
// reject other receiver methods/borrows, even if some are actually read-only.
fn has_other_mutation(expr: &Expr<'_>, target: HirId, candidate: HirId) -> bool {
    struct Finder {
        target: HirId,
        candidate: HirId,
        found: bool,
    }
    impl<'tcx> intravisit::Visitor<'tcx> for Finder {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            match expr.kind {
                ExprKind::Assign(lhs, _, _) | ExprKind::AssignOp(_, lhs, _)
                    if local(lhs) == Some(self.target) && expr.hir_id != self.candidate =>
                {
                    self.found = true
                }
                ExprKind::MethodCall(method, receiver, _, _)
                    if local(receiver) == Some(self.target)
                        && method.ident.name.as_str() != "clone" =>
                {
                    self.found = true
                }
                ExprKind::AddrOf(_, ty::Mutability::Mut, receiver)
                    if local(receiver) == Some(self.target) =>
                {
                    self.found = true
                }
                ExprKind::Closure(_) => self.found = true,
                _ => {}
            }
            if !self.found {
                intravisit::walk_expr(self, expr);
            }
        }
    }
    let mut finder = Finder {
        target,
        candidate,
        found: false,
    };
    intravisit::Visitor::visit_expr(&mut finder, expr);
    finder.found
}
