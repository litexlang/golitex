use super::DefinitionGraphBuilder;
use crate::prelude::*;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

fn definition_graph_output(source: &'static str) -> String {
    std::thread::Builder::new()
        .name("definition_graph_output_large_stack".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            render_graph(
                GraphKind::Definition,
                run_code(source, RunOptions::default()),
                true,
            )
            .1
        })
        .expect("spawn definition graph output test")
        .join()
        .expect("definition graph output test panicked")
}

#[test]
fn definition_graph_reads_environment_stored_props_and_functions() {
    let output = definition_graph_output(
        "abstract_prop p(x)\nprop q(x R):\n    $p(x)\nhave fn f(x R: $q(x)) R = x\n",
    );

    assert!(output.contains(r#""graph": "litex-definition-graph""#));
    assert!(output.contains("\"target\": {\n    \"kind\": \"code\"\n  }"));
    assert!(output.contains(r#""id": "definition:prop:p""#));
    assert!(output.contains(r#""id": "definition:prop:q""#));
    assert!(output.contains(r#""id": "definition:fn:f""#));
    assert!(output.contains(r#""graph_version": "0.3""#));
    assert!(output.contains(r#""kind": "definition""#));
    assert!(output.contains(r#""kind": "well_definedness""#));
    assert!(output.contains(r#""referenced_kind": "prop""#));
    assert!(output.contains(r#""semantic_role": "property""#));
    assert!(output.contains(r#""knowledge_status": "checked""#));
    assert!(output.contains(r#""is_dag": true"#));
    assert!(output.contains(r#""line": 1"#));
}

#[test]
fn definition_graph_records_selection_certificate_and_actual_trust_source() {
    let output = definition_graph_output(
            "abstract_prop F(x, y)\nhave A set\nhave B set\nhave fn f by exist!:\n    ? forall x A:\n        exist! y B st {$F(x, y)}\n    trust exist! y B st {$F(x, y)}\n",
        );

    assert!(output.contains("certificate:exist_unique:f"), "{output}");
    assert!(output.contains(r#""kind": "selection""#), "{output}");
    assert!(output.contains(r#""kind": "proof""#), "{output}");
    assert!(output.contains(r#""kind": "trust_source""#), "{output}");
    assert!(
        output.contains(r#""litex_form": "have_fn_by_exist_unique""#),
        "{output}"
    );
    assert!(
        output.contains(r#""semantic_role": "canonical_selection""#),
        "{output}"
    );
    assert!(output.contains(r#""trust_kind": "direct""#), "{output}");
}

#[test]
fn definition_graph_proof_edges_follow_actual_by_theorem_results() {
    let output = definition_graph_output(
            "abstract_prop P(x)\naxiom base_p:\n    ? forall x R:\n        $P(x)\nthm derived_p:\n    ? forall x R:\n        $P(x)\n    release thm base_p(x)\n",
        );

    assert!(
        output.contains(
            r#""from": "definition:theorem:base_p",
      "to": "definition:theorem:derived_p",
      "kind": "proof""#
        ),
        "{output}"
    );
    assert!(
        output.contains(r#""knowledge_status": "axiom""#),
        "{output}"
    );
    assert!(output.contains(r#""trust_kind": "indirect""#), "{output}");
}

#[test]
fn definition_graph_file_uses_selected_export_environment() {
    let fixture = DefinitionGraphFixture::new("selected-export");
    write_file(
        &fixture.path("litex.config"),
        "[hierarchy]\nmodule\n\n[export]\nfirst = \"./first.lit\"\ntarget = \"./target.lit\"\n",
    );
    write_file(
        &fixture.path("first.lit"),
        "prop first_prop(x R):\n    x = x\n",
    );
    let target = fixture.path("target.lit");
    write_file(
            &target,
            "prop local_prop(x R):\n    x = x\n\nprop target_prop(x R):\n    $local_prop(x)\n    $first::first_prop(x)\n\nabstract_prop Choice(x, y)\nhave A set\nhave B set\nhave fn selected by exist!:\n    ? forall x A:\n        exist! y B st {$Choice(x, y)}\n    trust exist! y B st {$Choice(x, y)}\n",
        );
    let hidden_root = fixture
        .root
        .to_str()
        .expect("fixture root is UTF-8")
        .to_string();
    let target_string = target.to_str().expect("fixture path is UTF-8").to_string();
    let output = std::thread::Builder::new()
        .name("definition_graph_selected_export".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            render_graph(
                GraphKind::Definition,
                run_file(target_string.as_str(), RunOptions::default()),
                true,
            )
            .1
        })
        .expect("spawn selected export definition graph test")
        .join()
        .expect("selected export definition graph test panicked");

    assert!(output.contains("definition:prop:target_prop"), "{output}");
    assert!(
        output.contains(
            r#""from": "definition:prop:local_prop",
      "to": "definition:prop:target_prop",
      "kind": "definition""#
        ),
        "{output}"
    );
    assert!(
        !output.contains("definition:prop:target::local_prop"),
        "{output}"
    );
    assert!(
        output.contains("definition:prop:first::first_prop"),
        "{output}"
    );
    let imported_prop_id = r#""id": "definition:prop:first::first_prop""#;
    let imported_prop_index = output.find(imported_prop_id).expect("imported prop node");
    let imported_prop_end = (imported_prop_index + 500).min(output.len());
    let imported_prop_window = &output[imported_prop_index..imported_prop_end];
    assert!(
        imported_prop_window.contains(r#""definition_kind": "prop""#),
        "{imported_prop_window}"
    );
    assert!(
        imported_prop_window.contains(r#""defined": false"#),
        "{imported_prop_window}"
    );
    assert!(
        imported_prop_window.contains(r#""knowledge_status": "checked""#),
        "{imported_prop_window}"
    );
    let certificate_id = r#""id": "certificate:exist_unique:selected:"#;
    let certificate_index = output
        .find(certificate_id)
        .expect("selection certificate node");
    let certificate_end = (certificate_index + 900).min(output.len());
    let certificate_window = &output[certificate_index..certificate_end];
    assert!(
        certificate_window.contains(r#""knowledge_status": "trust""#),
        "{certificate_window}"
    );
    assert!(
        certificate_window.contains(r#""trust_kind": "direct""#),
        "{certificate_window}"
    );
    assert!(
        output.contains(r#""to": "certificate:exist_unique:selected:target.lit:"#),
        "{output}"
    );
    let function_index = output
        .find(r#""id": "definition:fn:selected""#)
        .expect("selected function node");
    let function_end = (function_index + 900).min(output.len());
    let function_window = &output[function_index..function_end];
    assert!(
        function_window.contains(r#""line": 11"#),
        "{function_window}"
    );
    assert!(!output.contains(hidden_root.as_str()), "{output}");
}

#[test]
fn definition_graph_repository_uses_the_selected_submodule_environment() {
    let fixture = DefinitionGraphFixture::new("selected-submodule");
    write_file(
        &fixture.path("litex.config"),
        "[hierarchy]\nmodule\n\n[export]\nroot_before = \"./root_before.lit\"\nB = \"./B\"\n",
    );
    write_file(
        &fixture.path("root_before.lit"),
        "prop root_prop(x R):\n    x = x\n",
    );
    write_file(
        &fixture.path("B/litex.config"),
        "[hierarchy]\nsubmodule\n\n[export]\nmain = \"./main.lit\"\n",
    );
    write_file(
        &fixture.path("B/main.lit"),
        "prop submodule_prop(x R):\n    x = x\n",
    );
    let target = fixture.path("B");
    let target = target.to_str().expect("fixture path is UTF-8").to_string();
    let output = std::thread::Builder::new()
        .name("definition_graph_selected_submodule".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            render_graph(
                GraphKind::Definition,
                run_repository(target.as_str(), RunOptions::default()),
                true,
            )
            .1
        })
        .expect("spawn selected submodule definition graph test")
        .join()
        .expect("selected submodule definition graph test panicked");

    assert!(
        output.contains("definition:prop:submodule_prop"),
        "{output}"
    );
    assert!(
        !output.contains("definition:prop:root_before::root_prop"),
        "{output}"
    );
}

#[test]
fn definition_graph_project_proof_sources_normalize_local_qualifier() {
    let fixture = DefinitionGraphFixture::new("local-proof-source");
    write_file(
        &fixture.path("litex.config"),
        "[hierarchy]\nmodule\n\n[export]\ntarget = \"./target.lit\"\n",
    );
    let target = fixture.path("target.lit");
    write_file(
            &target,
            "thm local_base:\n    ? forall x R:\n        x = x\nthm local_derived:\n    ? forall x R:\n        x = x\n    release thm local_base(x)\n",
        );
    let target_string = target.to_str().expect("fixture path is UTF-8").to_string();
    let output = std::thread::Builder::new()
        .name("definition_graph_local_proof_source".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            render_graph(
                GraphKind::Definition,
                run_file(
                    target_string.as_str(),
                    RunOptions {
                        strict_mode: true,
                        ..RunOptions::default()
                    },
                ),
                true,
            )
            .1
        })
        .expect("spawn local proof-source definition graph test")
        .join()
        .expect("local proof-source definition graph test panicked");

    assert!(
        output.contains(
            r#""from": "definition:theorem:local_base",
      "to": "definition:theorem:local_derived",
      "kind": "proof""#
        ),
        "{output}"
    );
    assert!(
        !output.contains("definition:theorem:target::local_base"),
        "{output}"
    );
    assert!(
        !output.contains("definition:theorem:target::local_derived"),
        "{output}"
    );
}

#[test]
fn definition_graph_cycle_nodes_exclude_downstream_nodes() {
    let mut graph = DefinitionGraphBuilder::new();
    for name in ["a", "b", "downstream"] {
        graph.ensure_node(name.to_string(), "prop", "prop", name, true, None, None);
    }
    graph.add_edge("a", "b", "definition");
    graph.add_edge("b", "a", "definition");
    graph.add_edge("b", "downstream", "definition");

    assert_eq!(graph.cycle_nodes(), vec!["a".to_string(), "b".to_string()]);
    assert!(!graph.is_dag());
}

fn write_file(path: &Path, source: &str) {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).expect("create definition graph fixture directory");
    }
    fs::write(path, source).expect("write definition graph fixture file");
}

struct DefinitionGraphFixture {
    root: PathBuf,
}

impl DefinitionGraphFixture {
    fn new(name: &str) -> Self {
        static NEXT_ID: AtomicUsize = AtomicUsize::new(0);
        let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "litex-definition-graph-{name}-{}-{id}",
            std::process::id()
        ));
        if root.exists() {
            fs::remove_dir_all(&root).expect("remove stale definition graph fixture");
        }
        fs::create_dir_all(&root).expect("create definition graph fixture root");
        Self { root }
    }

    fn path(&self, name: &str) -> PathBuf {
        self.root.join(name)
    }
}
