use crate::compat::FxHashSet;
use crate::def_ids::other_api::is_drop_fn;
use crate::helpers::draw_dot::render_dot_string;
use colorful::{Color, Colorful};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{
    BasicBlockData, BasicBlocks, Body, LocalDecl, LocalDecls, Operand, Rvalue, Statement,
    StatementKind, Terminator, TerminatorKind, VarDebugInfoContents,
};
use rustc_middle::ty::{self, TyCtxt, TyKind};
use std::io::IsTerminal;

const NEXT_LINE: &str = "\n";
const PADDING: &str = "    ";
const EXPLAIN: &str = " @ ";
// Functions injected by RAPx itself (see `preprocess::dummy_fns`); they are not part of the user crate.
const DUMMY_FNS: [&str; 2] = ["__raw_ptr_deref_dummy", "__static_mut_deref_dummy"];

fn callee_display(id: DefId) -> String {
    let path = ty::tls::with(|tcx| tcx.def_path_str(id));
    format!(
        "Call: {} #{}:{}",
        path,
        id.krate.as_u32(),
        id.index.as_u32()
    )
}

// This trait is a wrapper towards std::Display or std::Debug, and is to resolve orphan restrictions.
pub trait MirDisplay {
    fn display(&self) -> String;
}

impl<'tcx> MirDisplay for Terminator<'tcx> {
    fn display(&self) -> String {
        let mut s = String::new();
        s += &format!("{}{:?}{}", PADDING, self.kind, self.kind.display());
        s
    }
}

impl<'tcx> MirDisplay for TerminatorKind<'tcx> {
    fn display(&self) -> String {
        let mut s = String::new();
        s += EXPLAIN;
        match &self {
            TerminatorKind::Goto { .. } => s += "Goto",
            TerminatorKind::SwitchInt { .. } => s += "SwitchInt",
            TerminatorKind::Return => s += "Return",
            TerminatorKind::Unreachable => s += "Unreachable",
            TerminatorKind::Drop { .. } => s += "Drop",
            TerminatorKind::Assert { .. } => s += "Assert",
            TerminatorKind::Yield { .. } => s += "Yield",
            TerminatorKind::FalseEdge { .. } => s += "FalseEdge",
            TerminatorKind::FalseUnwind { .. } => s += "FalseUnwind",
            TerminatorKind::InlineAsm { .. } => s += "InlineAsm",
            TerminatorKind::UnwindResume => s += "UnwindResume",
            TerminatorKind::UnwindTerminate(..) => s += "UnwindTerminate",
            TerminatorKind::CoroutineDrop => s += "CoroutineDrop",
            TerminatorKind::Call { func, .. } => {
                if let Operand::Constant(constant) = func
                    && let ty::FnDef(id, ..) = constant.ty().kind()
                {
                    s += &callee_display(*id)
                } else {
                    s += "Call: <indirect>"
                }
            }
            TerminatorKind::TailCall { .. } => s += "TailCall",
        };
        s
    }
}

impl<'tcx> MirDisplay for Statement<'tcx> {
    fn display(&self) -> String {
        let mut s = String::new();
        s += &format!("{}{:?}{}", PADDING, self.kind, self.kind.display());
        s
    }
}

impl<'tcx> MirDisplay for StatementKind<'tcx> {
    fn display(&self) -> String {
        let mut s = String::new();
        s += EXPLAIN;
        match &self {
            StatementKind::Assign(assign) => {
                s += &format!("Assign({})", assign.1.display().trim_start_matches(EXPLAIN));
            }
            StatementKind::FakeRead(..) => s += "FakeRead",
            StatementKind::SetDiscriminant { .. } => s += "SetDiscriminant",
            StatementKind::StorageLive(..) => s += "StorageLive",
            StatementKind::StorageDead(..) => s += "StorageDead",
            #[cfg(not(rapx_ge_99))]
            StatementKind::Retag(..) => s += "Retag",
            StatementKind::AscribeUserType(..) => s += "AscribeUserType",
            StatementKind::Coverage(..) => s += "Coverage",
            StatementKind::Nop => s += "Nop",
            StatementKind::PlaceMention(..) => s += "PlaceMention",
            StatementKind::Intrinsic(..) => s += "Intrinsic",
            StatementKind::ConstEvalCounter => s += "ConstEvalCounter",
            #[allow(unreachable_patterns)]
            _ => s += "Other",
        }
        s
    }
}

impl<'tcx> MirDisplay for Rvalue<'tcx> {
    fn display(&self) -> String {
        let mut s = String::new();
        s += EXPLAIN;
        match self {
            Rvalue::Use(..) => s += "Use",
            Rvalue::Repeat(..) => s += "Repeat",
            Rvalue::Ref(..) => s += "Ref",
            Rvalue::ThreadLocalRef(..) => s += "ThreadLocalRef",
            Rvalue::Cast(..) => s += "Cast",
            Rvalue::BinaryOp(..) => s += "BinaryOp",
            #[cfg(not(rapx_ge_95))]
            Rvalue::NullaryOp(..) => s += "NullaryOp",
            Rvalue::UnaryOp(..) => s += "UnaryOp",
            Rvalue::Discriminant(..) => s += "Discriminant",
            Rvalue::Aggregate(..) => s += "Aggregate",
            #[cfg(not(rapx_ge_99))]
            Rvalue::ShallowInitBox(..) => s += "ShallowInitBox",
            Rvalue::CopyForDeref(..) => s += "CopyForDeref",
            Rvalue::RawPtr(_, _) => s += "RawPtr",
            #[allow(unreachable_patterns)]
            _ => s += "Other",
        }
        s
    }
}

impl<'tcx> MirDisplay for BasicBlocks<'tcx> {
    fn display(&self) -> String {
        let mut s = String::new();
        for (index, bb) in self.iter().enumerate() {
            s += &format!(
                "bb {} {{{}{}}}{}",
                index,
                NEXT_LINE,
                bb.display(),
                NEXT_LINE
            );
        }
        s
    }
}

impl<'tcx> MirDisplay for BasicBlockData<'tcx> {
    fn display(&self) -> String {
        let mut s = String::new();
        s += &format!("CleanUp: {}{}", self.is_cleanup, NEXT_LINE);
        for stmt in self.statements.iter() {
            s += &format!("{}{}", stmt.display(), NEXT_LINE);
        }
        s += &format!(
            "{}{}",
            self.terminator.clone().unwrap().display(),
            NEXT_LINE
        );
        s
    }
}

impl<'tcx> MirDisplay for LocalDecls<'tcx> {
    fn display(&self) -> String {
        let mut s = String::new();
        for (index, ld) in self.iter().enumerate() {
            s += &format!("_{}: {}{}", index, ld.display(), NEXT_LINE);
        }
        s
    }
}

impl<'tcx> MirDisplay for LocalDecl<'tcx> {
    fn display(&self) -> String {
        let mut s = String::new();
        s += &format!("{}", self.ty);
        s
    }
}

impl<'tcx> MirDisplay for Body<'tcx> {
    fn display(&self) -> String {
        let mut s = String::new();
        s += &self.local_decls.display();
        s += &self.basic_blocks.display();
        s
    }
}

impl<'tcx> MirDisplay for TyKind<'tcx> {
    fn display(&self) -> String {
        let mut s = String::new();
        s += &format!("{:?}", self);
        s
    }
}

impl MirDisplay for DefId {
    fn display(&self) -> String {
        format!("{:?}", self)
    }
}

pub struct ShowMir<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

// Local declarations annotated with the user variable names recorded in debug info.
fn display_locals(body: &Body) -> String {
    let mut names = vec![Vec::new(); body.local_decls.len()];
    for info in body.var_debug_info.iter() {
        if let VarDebugInfoContents::Place(place) = info.value
            && place.projection.is_empty()
        {
            names[place.local.as_usize()].push(info.name.to_string());
        }
    }
    let mut s = String::new();
    for (index, ld) in body.local_decls.iter().enumerate() {
        s += &format!("_{}: {}", index, ld.display());
        if !names[index].is_empty() {
            s += &format!("{}{}", EXPLAIN, names[index].join(", "));
        }
        s += NEXT_LINE;
    }
    s
}

fn paint(text: String, color: Color) -> String {
    if std::io::stderr().is_terminal() {
        text.color(color).to_string()
    } else {
        text
    }
}

// #[inline(always)]
pub fn display_mir(did: DefId, body: &Body) {
    let header = ty::tls::with(|tcx| {
        format!(
            "MIR [{}] {} ({:?})",
            tcx.def_descr(did).replace(' ', "_"),
            tcx.def_path_str(did),
            did
        )
    });
    rap_info!("{}", paint(header, Color::LightRed));
    rap_info!("{}", paint(display_locals(body), Color::Green));
    rap_info!(
        "{}",
        paint(body.basic_blocks.display(), Color::LightGoldenrod2a)
    );
}

fn is_dummy_fn(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.opt_item_name(def_id)
        .is_some_and(|name| DUMMY_FNS.contains(&name.as_str()))
}

impl<'tcx> ShowMir<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }

    pub fn start(&mut self) {
        rap_info!("Show MIR");
        let mir_keys = self.tcx.mir_keys(());
        for each_mir in mir_keys {
            let def_id = each_mir.to_def_id();
            if is_dummy_fn(self.tcx, def_id) {
                continue;
            }
            let body = self.tcx.instance_mir(ty::InstanceKind::Item(def_id));
            display_mir(def_id, body);
        }
    }

    pub fn start_generate_dot(&mut self) {
        rap_info!("Generate MIR DOT");
        std::process::Command::new("mkdir")
            .args(["MIR_dot_graph"])
            .output()
            .expect("Failed to create directory");

        let mir_keys = self.tcx.mir_keys(());
        let mut used_names = FxHashSet::default();
        for each_mir in mir_keys {
            let def_id = each_mir.to_def_id();
            if is_dummy_fn(self.tcx, def_id) {
                continue;
            }
            // Closures and anonymous constants share a cleaned path with their parent, so the
            // file name is derived from the full def path and disambiguated by the def index.
            let mut name = dot_file_name(&self.tcx.def_path_str(def_id));
            if !used_names.insert(name.clone()) {
                name = format!("{}-{}", name, def_id.index.as_u32());
            }
            let _ = generate_mir_cfg_dot(self.tcx, def_id, name, &Vec::new());
        }
    }
}

fn dot_file_name(def_path: &str) -> String {
    def_path
        .chars()
        .map(|c| {
            if c.is_alphanumeric() || "_-:#{}".contains(c) {
                c
            } else {
                '_'
            }
        })
        .collect()
}

fn generate_mir_cfg_dot<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    name: String,
    alias_sets: &Vec<FxHashSet<usize>>,
) -> Result<(), std::io::Error> {
    // `optimized_mir` ICEs on const items; `instance_mir` picks the right body for every item kind.
    let mir = tcx.instance_mir(ty::InstanceKind::Item(def_id));
    let mut dot_content = String::new();
    let alias_info_str = if alias_sets.is_empty() {
        String::new()
    } else {
        format!("Alias Sets: {:?}\\n", alias_sets)
    };

    dot_content.push_str(&format!("digraph \"mir_cfg_{}\" {{\n", name));
    dot_content.push_str(&format!(
        "    label = \"MIR CFG for {}\\n{}\";\n",
        tcx.def_path_str(def_id).replace('"', "\\\""),
        alias_info_str.replace("\"", "\\\"")
    ));
    dot_content.push_str("    labelloc = \"t\";\n");
    dot_content.push_str("    node [shape=box, fontname=\"Courier\", align=\"left\"];\n\n");

    for (bb_index, bb_data) in mir.basic_blocks.iter_enumerated() {
        let mut lines: Vec<String> = bb_data
            .statements
            .iter()
            .map(|stmt| format!("{:?}", stmt))
            .collect();
        let mut node_style = String::new();

        if let Some(terminator) = &bb_data.terminator {
            let mut is_drop_related = false;
            match &terminator.kind {
                TerminatorKind::Drop { .. } => is_drop_related = true,
                TerminatorKind::Call { func, .. } => {
                    if let Operand::Constant(c) = func
                        && let ty::FnDef(def_id, _) = *c.ty().kind()
                        && is_drop_fn(def_id)
                    {
                        is_drop_related = true;
                    }
                }
                _ => {}
            }
            if is_drop_related {
                node_style = ", style=\"filled\", fillcolor=\"#ffdddd\", color=\"red\"".to_string();
            }
            lines.push(format!("{:?}", terminator.kind));
        } else {
            lines.push("(no terminator)".to_string());
        }

        let label_content = lines.join("\\l");
        let node_label = format!("BB{}:\\l{}\\l", bb_index.index(), label_content);
        dot_content.push_str(&format!(
            "    BB{} [label=\"{}\"{}];\n",
            bb_index.index(),
            node_label.replace("\"", "\\\""),
            node_style
        ));

        if let Some(terminator) = &bb_data.terminator {
            for target in terminator.successors() {
                dot_content.push_str(&format!(
                    "    BB{} -> BB{} [label=\"\"];\n",
                    bb_index.index(),
                    target.index(),
                ));
            }
        }
    }
    dot_content.push_str("}\n");
    render_dot_string(name, dot_content);
    Ok(())
}
