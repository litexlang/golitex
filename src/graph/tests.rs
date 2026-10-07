use super::MathGraph;
use crate::knowledge_base::JsonValue;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn make_graph(code: &str, strict: bool, language: OutputLanguage) -> MathGraph {
    let command = LaunchCommand::Eval { code: code.into(), strict, session: false, language };
    let mut runtime = Runtime::new(command);
    let result = runtime.run_litex_code(code).unwrap();
    let count = runtime.top_exec_env().facts.facts_by_id.len();
    let ids_before = runtime.global_ids.clone();
    let mut graph = MathGraph::new(language);
    graph.collect_run(&result, &runtime, "<eval>");
    assert_eq!(runtime.top_exec_env().facts.facts_by_id.len(), count);
    assert_eq!(runtime.global_ids, ids_before);
    graph
}

#[test]
fn graph_theorem_application_is_an_edge_and_publishes_the_fact() {
    let graph = make_graph("thm only_natural:\n    ? forall n N:\n        n >= 0\nby thm only_natural(1) => 1 >= 0", true, OutputLanguage::English);
    let theorem = graph.nodes.iter().find(|n| n.kind == "thm" && n.label == "only_natural").unwrap();
    let fact = graph.nodes.iter().find(|n| n.kind == "fact" && n.label == "1 >= 0" && !n.scope.starts_with("local:")).unwrap();
    assert!(fact.published);
    assert!(graph.edges.iter().any(|e| e.from == theorem.id && e.to == fact.id && e.kind == "theorem_instance"));
    assert!(graph.nodes.iter().all(|n| ["definition", "thm", "fact"].contains(&n.kind.as_str())));
    assert!(!graph.nodes.iter().any(|n| n.label.starts_with("by thm") || n.label.starts_with("release thm")));
}

#[test]
fn graph_definition_and_its_inferred_facts_are_distinct() {
    let graph = make_graph("prop above_zero(x R):\n    x > 0\n$above_zero(1)", true, OutputLanguage::English);
    let definition = graph.nodes.iter().find(|n| n.kind == "definition" && n.label == "above_zero").unwrap();
    let fact = graph.nodes.iter().find(|n| n.label == "$above_zero(1)").unwrap();
    let inferred = graph.nodes.iter().find(|n| n.label == "1 > 0" && n.inferred).unwrap();
    assert!(fact.published);
    assert!(graph.edges.iter().any(|e| e.from == definition.id && e.to == fact.id));
    assert!(graph.edges.iter().any(|e| e.from == fact.id && e.to == inferred.id && e.kind == "inferred_from"));
}

#[test]
fn graph_definition_reference_is_not_an_implication_or_time_edge() {
    let graph = make_graph("prop first(x R):\n    x > 0\nprop second(x R):\n    $first(x)", true, OutputLanguage::English);
    let first = graph.nodes.iter().find(|n| n.label == "first").unwrap();
    let second = graph.nodes.iter().find(|n| n.label == "second").unwrap();
    assert!(graph.edges.iter().any(|e| e.from == first.id && e.to == second.id && e.kind == "definition_reference"));
    let independent = make_graph("2 = 2\n3 = 3", true, OutputLanguage::English);
    assert!(independent.edges.is_empty());
}

#[test]
fn graph_known_equality_dependency_preserves_the_real_source() {
    let graph = make_graph("have x R = 2\nx > 0", true, OutputLanguage::English);
    let equality = graph.nodes.iter().find(|n| n.label == "x = 2").unwrap();
    let positive = graph.nodes.iter().find(|n| n.label == "x > 0").unwrap();
    assert!(graph.edges.iter().any(|e| e.from == equality.id && e.to == positive.id && e.kind == "depends_on"));
}

#[test]
fn graph_forall_assumptions_remain_local() {
    let graph = make_graph("forall n N:\n    n = 16\n    =>:\n        $prime(n + 1)", true, OutputLanguage::English);
    let premise = graph.nodes.iter().find(|n| n.label == "n = 16").unwrap();
    assert_eq!(premise.origin, "assumption");
    assert!(premise.scope.starts_with("local:"));
    assert!(!premise.published);
    let whole = graph.nodes.iter().find(|n| n.label.starts_with("forall n N:")).unwrap();
    assert!(whole.published);
    assert!(!graph.edges.iter().any(|e| e.from == whole.id && graph.nodes.iter().any(|n| n.id == e.to && n.scope.starts_with("local:"))));
}

#[test]
fn graph_failed_statement_and_failed_claim_do_not_publish() {
    let failed = make_graph("1 / 0 = 0", true, OutputLanguage::English);
    assert!(failed.nodes.is_empty());
    assert!(!failed.diagnostics.is_empty());
    let claim = make_graph("claim:\n    ? 1 = 0\n    2 = 2\n3 = 3", true, OutputLanguage::English);
    assert!(!claim.nodes.iter().any(|n| n.label == "2 = 2" || n.label == "1 = 0"));
    assert!(claim.nodes.iter().any(|n| n.label == "3 = 3" && !n.published));
}

#[test]
fn graph_trusted_source_keeps_its_origin() {
    let graph = make_graph("have x R\ntrust x = 2\nx > 0", false, OutputLanguage::English);
    let trusted = graph.nodes.iter().find(|n| n.label == "x = 2").unwrap();
    assert_eq!(trusted.origin, "trusted");
    let positive = graph.nodes.iter().find(|n| n.label == "x > 0").unwrap();
    assert!(graph.edges.iter().any(|e| e.from == trusted.id && e.to == positive.id));
    let strict = make_graph("trust 1 = 0", true, OutputLanguage::English);
    assert!(strict.nodes.is_empty());
}

#[test]
fn graph_semantics_and_ids_are_independent_of_locale() {
    let code = "prop above_zero(x R):\n    x > 0\n$above_zero(1)";
    let en = make_graph(code, true, OutputLanguage::English);
    let zh = make_graph(code, true, OutputLanguage::Chinese);
    let mut en = JsonValue::parse(&en.json(true, "eval", None)).unwrap().as_object().unwrap().clone();
    let mut zh = JsonValue::parse(&zh.json(true, "eval", None)).unwrap().as_object().unwrap().clone();
    en.insert("language".into(), JsonValue::Null);
    zh.insert("language".into(), JsonValue::Null);
    assert_eq!(en, zh);
}

#[test]
fn graph_command_preserves_operand_ownership_and_rejects_unselected_modes() {
    use crate::run::run_graph::parse_graph_command;
    let args = |items: &[&str]| items.iter().map(|s| s.to_string()).collect::<Vec<_>>();
    assert!(parse_graph_command(&args(&["-e", "-graph"])).unwrap().is_none());
    assert!(parse_graph_command(&args(&["-graph", "-e", "1 = 1"])).unwrap().is_some());
    assert!(parse_graph_command(&args(&["-e", "1 = 1", "-graph"])).unwrap().is_some());
    for items in [vec!["-graph"], vec!["-graph", "-session", "-e", "1 = 1"], vec!["-graph", "-latex", "-e", "1 = 1"], vec!["-graph", "-graph", "-e", "1 = 1"]] {
        assert!(parse_graph_command(&args(&items)).is_err());
    }
}

#[test]
fn graph_generated_visitor_matches_current_certificate_fields() {
    let output = std::process::Command::new("python3")
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .args(["src/graph/generate_walk.py", "--check"]).output().unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
}

#[test]
fn graph_file_prefix_and_cached_module_aliases_preserve_owners() {
    use crate::run::run_graph::run_graph_command;
    use std::fs;
    use std::time::{SystemTime, UNIX_EPOCH};
    let directory = std::env::temp_dir().join(format!("litex-graph-{}-{}", std::process::id(), SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()));
    fs::create_dir_all(directory.join("library")).unwrap();
    fs::write(directory.join("library/litex.config"), "[export]\nmain = \"main.lit\"\n").unwrap();
    fs::write(directory.join("library/main.lit"), "thm identity:\n    ? forall x R:\n        x = x\n").unwrap();
    fs::write(directory.join("litex.config"), "[import]\nA = \"./library\"\nB = \"./library\"\n[export]\nprefix = \"prefix.lit\"\ntarget = \"target.lit\"\nlater = \"later.lit\"\n").unwrap();
    fs::write(directory.join("prefix.lit"), "prop above_zero(x R):\n    x > 0\n").unwrap();
    fs::write(directory.join("target.lit"), "by thm A:::identity(2) => 2 = 2\nby thm B:::identity(3) => 3 = 3\n$prefix::above_zero(1)\n").unwrap();
    fs::write(directory.join("later.lit"), "prop later_only(x R):\n    x = 0\n").unwrap();
    for _ in 0..2 {
        let result = run_graph_command(LaunchCommand::File { path: directory.join("target.lit"), strict: true, session: false, language: OutputLanguage::English }).unwrap();
        assert!(result.success, "{}", result.json);
        let graph = JsonValue::parse(&result.json).unwrap();
        let graph = graph.as_object().unwrap();
        let nodes = graph.get("nodes").unwrap().as_array().unwrap();
        let theorems = nodes.iter().filter(|node| node.as_object().unwrap().get("kind").unwrap().as_str().unwrap() == "thm").collect::<Vec<_>>();
        assert_eq!(theorems.len(), 1);
        assert!(!nodes.iter().any(|node| node.as_object().unwrap().get("label").unwrap().as_str().unwrap() == "later_only"));
        let id = theorems[0].as_object().unwrap().get("id").unwrap().as_str().unwrap();
        let edges = graph.get("edges").unwrap().as_array().unwrap();
        assert!(edges.iter().filter(|edge| {
            let edge = edge.as_object().unwrap();
            edge.get("from").unwrap().as_str().unwrap() == id && edge.get("kind").unwrap().as_str().unwrap() == "theorem_instance"
        }).count() >= 2, "{}", result.json);
    }
    // The test owns this unique system-temporary project, including its cache.
    fs::remove_dir_all(directory).unwrap();
}
