pub mod participant;
pub mod slice_contains;
pub mod string_add;
pub mod vec_remove;

use participant::ParticipantCheck;
use slice_contains::SliceContainsCheck;
use string_add::StringAddCheck;
use vec_remove::VecRemoveCheck;

use crate::analysis::dataflow::Graph;
use crate::check::opt::OptCheck;

use rustc_middle::ty::TyCtxt;

use super::super::LEVEL;

pub struct SuboptimalCheck {
    participant: ParticipantCheck,
    slice_contains: SliceContainsCheck,
    string_add: StringAddCheck,
    vec_remove: VecRemoveCheck,
}

impl OptCheck for SuboptimalCheck {
    fn new() -> Self {
        Self {
            participant: ParticipantCheck::new(),
            slice_contains: SliceContainsCheck::new(),
            string_add: StringAddCheck::new(),
            vec_remove: VecRemoveCheck::new(),
        }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        self.string_add.check(graph, tcx);
        self.vec_remove.check(graph, tcx);
        let level = LEVEL.lock().unwrap();
        if *level == 2 {
            self.participant.check(graph, tcx);
            self.slice_contains.check(graph, tcx);
        }
    }

    fn report(&self, graph: &Graph) {
        self.participant.report(graph);
        self.slice_contains.report(graph);
        self.string_add.report(graph);
        self.vec_remove.report(graph);
    }

    fn cnt(&self) -> usize {
        self.participant.cnt() + self.slice_contains.cnt() + self.string_add.cnt() + self.vec_remove.cnt()
    }
}
