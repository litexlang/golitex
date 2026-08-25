use super::*;

#[test]
fn let_callable_alias_reduces_once_with_typed_definition_evidence() {
    let source = r#"
have fn f(x R) R = x + 1
let g = f
g(1) = 2
"#;

    let mut runtime = Runtime::new();
    runtime.start_isolated_source("transparent_callable_alias");
    let (results, error) = execute_source(source, &mut runtime);
    let (succeeded, output) = render_run_output(&runtime, &results, &error);

    assert!(succeeded, "transparent callable alias failed:\n{output}");
    let json = crate::output::display_stmt_result_json_v2(&results[2]);
    assert!(
        json.contains(r#""kind": "TransparentDefinitionReduction""#),
        "the proof must retain its transparent reduction:\n{json}"
    );
    assert!(json.contains(r#""defining_equality":"#), "{json}");
    assert!(json.contains("g ="), "{json}");
    assert!(
        json.contains(r#""defining_equality_fact_id": "f7""#),
        "{json}"
    );

    let graph = crate::graph::render_result_graph_from_stmt_results(
        "code",
        "transparent_callable_alias",
        true,
        &results,
    );
    assert!(
        graph.contains(r#""role": "TransparentDefinitionReduction""#),
        "{graph}"
    );
    assert!(graph.contains(r#""kind": "defining_equality""#), "{graph}");
    assert!(graph.contains(r#""fact_id": "f7""#), "{graph}");
}

#[test]
fn ordinary_have_equality_does_not_register_a_transparent_definition() {
    let source = "have a R = 1\n";
    let mut runtime = Runtime::new();
    runtime.start_isolated_source("ordinary_have_is_not_transparent");
    let (results, error) = execute_source(source, &mut runtime);
    assert!(error.is_none(), "ordinary have failed: {error:?}");
    assert_eq!(results.len(), 1);

    let definition = runtime
        .iter_environments_from_top()
        .find_map(|environment| environment.definitions.symbols.get("a"))
        .expect("the ordinary have symbol should be stored");
    assert!(
        definition.transparent_object_definition().is_none(),
        "only let definitions are transparent"
    );
}

#[test]
fn transparent_definition_reduction_applies_to_non_equality_atomic_facts() {
    let source = "let S = R\n1 $in S\n";
    let mut runtime = Runtime::new();
    runtime.start_isolated_source("transparent_non_equality_atomic_fact");
    let (results, error) = execute_source(source, &mut runtime);
    let (succeeded, output) = render_run_output(&runtime, &results, &error);

    assert!(succeeded, "transparent membership failed:\n{output}");
    let json = crate::output::display_stmt_result_json_v2(&results[1]);
    assert!(
        json.contains(r#""kind": "TransparentDefinitionReduction""#),
        "the membership proof must retain transparent reduction evidence:\n{json}"
    );
}

#[test]
fn transparent_lookup_is_exact_by_symbol_id_and_one_layer_per_pass() {
    let source = "let a = R\nlet b = a\n";
    let mut runtime = Runtime::new();
    runtime.start_isolated_source("transparent_lookup_boundaries");
    let (_, error) = execute_source(source, &mut runtime);
    assert!(error.is_none(), "transparent aliases failed: {error:?}");

    let (a_binding, b_binding) = runtime
        .iter_environments_from_top()
        .find_map(|environment| {
            Some((
                environment.definitions.symbols.get("a")?.binding().clone(),
                environment.definitions.symbols.get("b")?.binding().clone(),
            ))
        })
        .expect("both let symbols should be stored together");
    let b: Obj = Identifier::new_bound("b".to_string(), b_binding.as_ref()).into();
    let a: Obj = Identifier::new_bound("a".to_string(), a_binding.as_ref()).into();

    let (first, first_uses) = runtime
        .resolve_transparent_obj_once(&b)
        .expect("first transparent pass");
    assert_eq!(obj_equality_key(&first), obj_equality_key(&a));
    assert_eq!(first_uses.len(), 1);
    assert_eq!(first_uses[0].symbol.id(), b_binding.id());

    let (second, second_uses) = runtime
        .resolve_transparent_obj_once(&first)
        .expect("second transparent pass");
    assert_eq!(
        obj_equality_key(&second),
        obj_equality_key(&Obj::from(StandardSet::R))
    );
    assert_eq!(second_uses.len(), 1);
    assert_eq!(second_uses[0].symbol.id(), a_binding.id());

    let same_spelling_other_identity: Obj = Identifier::new_bound(
        "a".to_string(),
        SymbolRef::new(SymbolId::new(999_999), "a".to_string()),
    )
    .into();
    let (unchanged, uses) = runtime
        .resolve_transparent_obj_once(&same_spelling_other_identity)
        .expect("same-spelling lookup");
    assert_eq!(
        obj_equality_key(&unchanged),
        obj_equality_key(&same_spelling_other_identity)
    );
    assert!(uses.is_empty());
}

#[test]
fn callable_alias_still_checks_application_arity() {
    let source = r#"
have fn f(x R) R = x + 1
let g = f
g(1, 2) = 3
"#;

    let mut runtime = Runtime::new();
    runtime.start_isolated_source("callable_alias_arity_boundary");
    let (results, error) = execute_source(source, &mut runtime);
    let (succeeded, output) = render_run_output(&runtime, &results, &error);

    assert!(
        !succeeded,
        "equality must not bypass the aliased function's arity check:\n{}",
        output
    );
    assert!(
        output.contains("number of args (2) does not match"),
        "the failure should remain localized to function arity:\n{}",
        output
    );
}
