use super::*;

#[test]
fn builtin_rules_consume_complete_quantifier_free_premises() {
    let source = r#"
forall A, B set, x set:
    x $in A or x $in B
    =>:
        x $in union(A, B)

forall a, x, b Z:
    a <= x <= b
    =>:
        x $in closed_range(a, b)

forall a, b, c R:
    a + b = c or b + a = c
    =>:
        a = c - b

forall a, b R:
    a != 0 and b != 0
    =>:
        a / b != 0

forall a, b R:
    0 <= a and 0 <= b or a <= 0 and b <= 0
    =>:
        0 <= a * b

forall A, B set, x, y set:
    x $in A and y $in B
    =>:
        (x, y) $in cart(A, B)

forall A, B set:
    $is_finite_set(A) and $is_finite_set(B)
    =>:
        $is_finite_set(union(A, B))

forall A, B set:
    A $subset B and A != B
    =>:
        A $proper_subset B

forall A, B set:
    not A $subset B or A = B
    =>:
        not A $proper_subset B

forall a, b R:
    0 <= a and 0 <= b
    =>:
        sqrt(a * b) = sqrt(a) * sqrt(b)

forall a, m, n set:
    m $in N and n $in N and a $in C
    =>:
        a^(m + n) = a^m * a^n

forall x R:
    x <= 0 or 1 <= x
    =>:
        x $in {y R: y <= 0 or 1 <= y}
"#;
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "builtin_rules_consume_complete_quantifier_free_premises",
    );
    let (results, error) = run_source_code(source, &mut runtime);
    let (succeeded, output) = render_run_source_code_output(&runtime, &results, &error, false);
    assert!(
        succeeded,
        "complete quantifier-free premises should be reusable without selecting a branch:\n{output}"
    );
    for expected in [
        "union membership from complete left-or-right membership premise",
        "in closed_range from complete bound chain",
        "equality: subtraction from complete addition-order disjunction",
        "local builtin nonzero.div",
        "0 <= a * b from either same weak-sign branch",
        "tuple in cart: each component is in the corresponding cart factor",
        "local builtin set.union_finite",
        "A $proper_subset B from its complete quantifier-free definition premise",
        "not A $proper_subset B from its complete quantifier-free definition premise",
        "sqrt: sqrt(a * b) = sqrt(a) * sqrt(b)",
        "equality: a^(m+n) = a^m * a^n",
        "\"type\": \"builtin strategy\"",
    ] {
        assert!(
            output.contains(expected),
            "missing compound-premise provenance `{expected}`:\n{output}"
        );
    }
}

#[test]
fn complete_disjunction_is_never_treated_as_a_selected_branch() {
    for (name, source) in [
        (
            "known_or_does_not_prove_left_branch",
            r#"
have x, A, B set
trust x $in A or x $in B
x $in A
"#,
        ),
        (
            "known_or_does_not_prove_intersection_membership",
            r#"
have x, A, B set
trust x $in A or x $in B
x $in intersect(A, B)
"#,
        ),
        (
            "partial_bound_or_does_not_prove_range_membership",
            r#"
have a, x, b Z
trust a <= x or x <= b
x $in closed_range(a, b)
"#,
        ),
    ] {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(name);
        let (results, error) = run_source_code(source, &mut runtime);
        let (succeeded, output) = render_run_source_code_output(&runtime, &results, &error, false);
        assert!(
            !succeeded,
            "a complete disjunction must not leak either branch into known atomic facts:\n{output}"
        );
        assert!(output.contains("UnknownError"), "{output}");
    }
}
