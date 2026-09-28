//! Ordered relation-chain closure contracts.

use crate::prelude::*;

fn obj(name: &str) -> Obj {
    Identifier::new(name.to_string()).into()
}

fn prop(name: &str) -> AtomicName {
    AtomicName::WithoutMod(name.to_string())
}

fn closure_strings(objs: &[&str], props: &[&str]) -> Vec<String> {
    ChainFact::new(
        objs.iter().map(|name| obj(name)).collect(),
        props.iter().map(|name| prop(name)).collect(),
        default_line_file(),
    )
    .facts_with_order_transitive_closure()
    .expect("valid relation chain should have a closure")
    .into_iter()
    .map(|fact| fact.to_string())
    .collect()
}

#[test]
fn set_inclusion_closure_is_strict_when_any_path_edge_is_strict() {
    let facts = closure_strings(&["A", "B", "C", "D"], &[SUBSET, PROPER_SUBSET, SUBSET]);

    for expected in [
        "A $proper_subset C",
        "A $proper_subset D",
        "B $proper_subset D",
    ] {
        assert!(facts.iter().any(|fact| fact == expected), "{facts:?}");
    }

    let reverse_order = closure_strings(&["A", "B", "C"], &[PROPER_SUBSET, SUBSET]);
    assert!(
        reverse_order
            .iter()
            .any(|fact| fact == "A $proper_subset C"),
        "{reverse_order:?}"
    );

    let supersets = closure_strings(&["A", "B", "C"], &[SUPERSET, PROPER_SUPERSET]);
    assert!(
        supersets.iter().any(|fact| fact == "A $proper_superset C"),
        "{supersets:?}"
    );
}

#[test]
fn opposite_inclusion_directions_do_not_create_endpoint_facts() {
    let facts = closure_strings(&["A", "B", "C"], &[PROPER_SUBSET, PROPER_SUPERSET]);

    assert_eq!(
        facts,
        vec![
            "A $proper_subset B".to_string(),
            "B $proper_superset C".to_string(),
        ]
    );
}

#[test]
fn numeric_order_steps_survive_an_unrelated_equality_suffix() {
    let chain = ChainFact::new(
        ["A", "B", "C", "D"].into_iter().map(obj).collect(),
        [LESS_EQUAL, LESS, EQUAL].into_iter().map(prop).collect(),
        default_line_file(),
    );

    let steps = chain
        .numeric_order_chain_closure_steps()
        .expect("mixed numeric/equality chain should retain numeric subchains");

    assert_eq!(steps.len(), 1);
    assert_eq!(steps[0].start_object_index, 0);
    assert_eq!(steps[0].end_object_index, 2);
    assert_eq!(steps[0].premises.len(), 2);
    assert_eq!(Fact::from(steps[0].conclusion.clone()).to_string(), "A < C");
}
