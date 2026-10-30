use std::fs::{File, remove_file, rename};
use std::io::Write;
use std::process::Command;

fn render_dot_file(dir_name: &str, name: &str, dot_graph: &str) {
    let _ = Command::new("mkdir").args([dir_name]).output();

    let file_name = format!("{}.dot", name);
    let mut file = File::create(&file_name).expect("Unable to create file");
    file.write_all(dot_graph.as_bytes())
        .expect("Unable to write data");

    let rendered = Command::new("dot")
        .args([
            "-Tpng",
            &file_name,
            "-o",
            &format!("{}/{}.png", dir_name, name),
        ])
        .output();

    match rendered {
        Ok(out) if out.status.success() => {
            remove_file(&file_name).expect("Failed to delete .dot file");
        }
        // Keep the DOT source next to the PNGs so it can be rendered later.
        _ => {
            let kept = format!("{}/{}", dir_name, file_name);
            let _ = rename(&file_name, &kept);
            rap_warn!("Graphviz `dot` failed or is not installed; kept {}", kept);
        }
    }
}

pub fn render_dot_graphs(dot_graphs: Vec<(String, String)>) {
    for dot in dot_graphs {
        render_dot_file("SafetyFlow", &dot.0, &dot.1);
    }
}

pub fn render_dot_string(name: String, dot_graph: String) {
    rap_debug!("render graph {:?}", name);
    render_dot_file("MIR_dot_graph", &name, &dot_graph);
}
