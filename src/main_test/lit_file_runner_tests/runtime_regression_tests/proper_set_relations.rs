use super::*;

#[test]
fn proper_set_relations_expand_from_components_and_expose_components() {
    let source_code = r#"
forall A, B set:
    A $subset B
    A != B
    =>:
        A $proper_subset B
        B $proper_superset A

forall A, B set:
    A $proper_subset B
    =>:
        A $subset B
        A != B
        B $proper_superset A

forall A, B set:
    A $superset B
    A != B
    =>:
        A $proper_superset B
        B $proper_subset A
"#;

    let (run_succeeded, run_output) = run_proper_relation_source(
        source_code,
        "proper_set_relations_expand_from_components_and_expose_components",
    );

    assert!(
        run_succeeded,
        "proper set-relation definitions or duality failed:\n{run_output}"
    );
}

#[test]
fn proper_set_relations_work_in_nested_theorem_premises() {
    let source_code = r#"
abstract_prop q(A, B)

axiom q_of_proper_subset:
    ? forall A, B set:
        A $proper_subset B
        =>:
            $q(A, B)

forall A, B set:
    A $subset B
    A != B
    =>:
        $q(A, B)
"#;

    let (run_succeeded, run_output) = run_proper_relation_source(
        source_code,
        "proper_set_relations_work_in_nested_theorem_premises",
    );

    assert!(
        run_succeeded,
        "proper subset components should satisfy a theorem premise:\n{run_output}"
    );
}

#[test]
fn negated_proper_set_relations_follow_their_disjunctive_definition() {
    let source_code = r#"
forall A, B set:
    not A $subset B
    =>:
        not A $proper_subset B

forall A, B set:
    A = B
    =>:
        not A $proper_subset B
        not A $proper_superset B

forall A, B set:
    not A $superset B
    =>:
        not A $proper_superset B

forall A, B set:
    not A $proper_subset B
    =>:
        not B $proper_superset A

forall A set:
    not A $proper_subset A
    not A $proper_superset A
"#;

    let (run_succeeded, run_output) = run_proper_relation_source(
        source_code,
        "negated_proper_set_relations_follow_their_disjunctive_definition",
    );

    assert!(
        run_succeeded,
        "negated proper relations should follow not-containment OR equality:\n{run_output}"
    );
}

#[test]
fn negated_proper_set_relations_do_not_infer_either_disjunct() {
    for (label, source_code) in [
        (
            "negated_proper_subset_does_not_imply_not_subset",
            r#"
forall A, B set:
    not A $proper_subset B
    =>:
        not A $subset B
"#,
        ),
        (
            "negated_proper_subset_does_not_imply_equality",
            r#"
forall A, B set:
    not A $proper_subset B
    =>:
        A = B
"#,
        ),
    ] {
        let (run_succeeded, run_output) = run_proper_relation_source(source_code, label);
        assert!(
            !run_succeeded,
            "a negated proper relation must not expose one arbitrary disjunct:\n{run_output}"
        );
    }
}

#[test]
fn mixed_strict_set_inclusion_chains_close_in_each_direction() {
    let source_code = r#"
forall A, B, C, D set:
    A $subset B $proper_subset C $subset D
    =>:
        A $proper_subset C
        A $proper_subset D
        B $proper_subset D

forall A, B, C set:
    A $proper_subset B $subset C
    =>:
        A $proper_subset C

forall A, B, C set:
    A $superset B $proper_superset C
    =>:
        A $proper_superset C

forall A, B, C set:
    A $proper_superset B $superset C
    =>:
        A $proper_superset C
"#;

    let (run_succeeded, run_output) = run_proper_relation_source(
        source_code,
        "mixed_strict_set_inclusion_chains_close_in_each_direction",
    );

    assert!(
        run_succeeded,
        "mixed strict/non-strict inclusion chains should close transitively:\n{run_output}"
    );
}

#[test]
fn proper_set_relations_reject_reflexive_goals_and_wrong_arity() {
    for (label, source_code, expected_message) in [
        (
            "proper_subset_is_irreflexive",
            "forall A set:\n    A $proper_subset A",
            None,
        ),
        (
            "proper_superset_is_irreflexive",
            "forall A set:\n    A $proper_superset A",
            None,
        ),
        (
            "proper_subset_wrong_arity",
            "$proper_subset({1})",
            Some("expects 2 argument(s), but got 1"),
        ),
        (
            "proper_superset_wrong_arity",
            "$proper_superset({1}, {2}, {3})",
            Some("expects 2 argument(s), but got 3"),
        ),
    ] {
        let (run_succeeded, run_output) = run_proper_relation_source(source_code, label);
        assert!(
            !run_succeeded,
            "{label} unexpectedly succeeded:\n{run_output}"
        );
        if let Some(expected_message) = expected_message {
            assert!(
                run_output.contains(expected_message),
                "{label} should report builtin arity:\n{run_output}"
            );
        }
    }
}

#[test]
fn set_relation_and_family_operator_latex_uses_standard_symbols() {
    let output = to_latex_from_source(
        r#"
A $proper_subset B $proper_superset C
not A $proper_subset C
x $in union(A, B)
x $in intersect(A, B)
x $in big_union(F)
x $in big_intersect(F)
"#,
        "set_relation_and_family_operator_latex_uses_standard_symbols",
    )
    .expect("set-relation and family-operator source should convert to LaTeX");

    for expected in [
        r"\subsetneq",
        r"\supsetneq",
        r"\bigcup",
        r"\bigcap",
        r"\cup",
        r"\cap",
    ] {
        assert!(
            output.contains(expected),
            "missing LaTeX symbol `{expected}`:\n{output}"
        );
    }
    assert!(!output.contains(r"\operatorname{big\_union}"), "{output}");
    assert!(
        !output.contains(r"\operatorname{big\_intersect}"),
        "{output}"
    );
}

fn run_proper_relation_source(source_code: &str, label: &str) -> (bool, String) {
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(label);
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false)
}
