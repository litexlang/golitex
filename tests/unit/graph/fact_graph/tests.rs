use crate::prelude::*;

fn fact_graph_output(source: &'static str) -> String {
    std::thread::Builder::new()
        .name("fact_graph_output_large_stack".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            run_graph(GraphRequest::new(
                GraphKind::Fact,
                RunRequest::new(
                    RunTarget::code(source, "fact_graph_test"),
                    RunOptions::default(),
                ),
                true,
            ))
            .1
        })
        .expect("spawn fact graph output test")
        .join()
        .expect("fact graph output test panicked")
}

#[test]
fn fact_graph_uses_runtime_fact_evidence_without_definition_nodes() {
    let output = fact_graph_output(
            "abstract_prop p(x)\nabstract_prop q(x)\ntrust forall x R:\n    $p(x)\n    =>:\n        $q(x)\nthm fact_graph_chain:\n    ? forall x R:\n        $p(x)\n        =>:\n            $q(x)\n    $q(x)\nclaim:\n    ? forall x R:\n        $p(x)\n        =>:\n            $q(x)\n    $q(x)\n",
        );

    assert!(output.contains(r#""graph": "litex-fact-graph""#));
    assert!(output.contains(r#""fact_kind": "thm""#));
    assert!(output.contains(r#""fact_kind": "claim""#));
    assert!(output.contains(r#""fact_kind": "trust""#));
    assert!(output.contains(r#""kind": "requires""#));
    assert!(output.contains(r#""longest_chain""#));
    assert!(!output.contains(r#""kind": "prop""#));
    assert!(!output.contains(r#""kind": "fn""#));
}

#[test]
fn fact_graph_flattens_definition_dependencies_into_fact_edges() {
    let output = fact_graph_output(
            "abstract_prop p(x)\nabstract_prop q(x)\nprop packed(x R):\n    $p(x)\n    $q(x)\nthm packed_from_facts:\n    ? forall x R:\n        $p(x)\n        $q(x)\n        =>:\n            $packed(x)\n    by def $packed(x)\n",
        );

    assert!(output.contains(r#""kind": "unfolds""#));
    assert!(output.contains(
        r#""selection": "facts, claims, and theorems; inferred facts are compressed into edges""#
    ));
    assert!(!output.contains(r#""kind": "prop""#));
}

#[test]
fn fact_graph_records_by_def_target_and_unfolding_edges() {
    let output =
        fact_graph_output("prop unit(x R):\n    x = 1\n1 = 1\nby def $unit(1)\n$unit(1)\n");

    assert!(output.contains("$unit(1)"));
    assert!(output.contains(r#""store_reason": "proof by definition""#));
    assert!(output.contains(r#""kind": "unfolds""#));
}
