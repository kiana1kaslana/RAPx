use annotate_snippets::Level;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use crate::{
    analysis::dataflow::Graph,
    check::opt::{
        OptCheck,
        evidence::{ByteEvidence, ByteFact, direct_call},
        report::OptReport,
    },
};

// Keep candidate recognition separate from the proof of the API precondition.
crate::def_paths! {
    str_from_utf8: "std::str::from_utf8",
    string_from_utf8: "std::string::String::from_utf8",
    string_from_utf8_lossy: "std::string::String::from_utf8_lossy",
    to_lowercase: "str::to_lowercase",
}

pub struct EncodingCheck {
    record: Vec<(Span, ByteFact, bool)>,
}

impl OptCheck for EncodingCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let paths = DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        let body = tcx.optimized_mir(graph.def_id);
        let mut evidence = None;
        for block in body.basic_blocks.iter() {
            let Some((id, args, span)) = direct_call(*tcx, body, block) else {
                continue;
            };
            let lowercase = id == paths.to_lowercase.last_def_id();
            if !lowercase
                && ![
                    paths.str_from_utf8.last_def_id(),
                    paths.string_from_utf8.last_def_id(),
                    paths.string_from_utf8_lossy.last_def_id(),
                ]
                .contains(&id)
            {
                continue;
            }
            let Some(arg) = args.first() else {
                continue;
            };
            let evidence =
                evidence.get_or_insert_with(|| ByteEvidence::new(*tcx, graph.def_id, body));
            let fact = evidence.operand(&arg.node);
            if (lowercase && fact == ByteFact::Ascii) || (!lowercase && fact.valid_utf8()) {
                self.record.push((span, fact, lowercase));
            }
        }
    }

    fn report(&self, graph: &Graph) {
        for &(span, fact, lowercase) in &self.record {
            let (title, help) = if lowercase {
                (
                    "ASCII lowercase opportunity",
                    "The receiver is proven ASCII. Consider to_ascii_lowercase; measure the release-build benefit.",
                )
            } else {
                (
                    "Redundant UTF-8 validation candidate",
                    "Prefer reusing the original str or a string literal. Preserve the Result/Cow contract; measure the release-build benefit before considering an unchecked conversion.",
                )
            };
            OptReport::from_graph(graph)
                .title(title)
                .annotate(
                    Level::Info,
                    span,
                    if fact == ByteFact::Ascii {
                        "Evidence: all input bytes are ASCII."
                    } else {
                        "Evidence: the complete input is valid UTF-8."
                    },
                )
                .footer(help)
                .emit();
        }
    }

    fn cnt(&self) -> usize {
        self.record.len()
    }
}
