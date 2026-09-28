use crate::pipeline::render_run_output;
use crate::prelude::*;
use crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source;
use crate::test_support::execute_source;

const SYMMETRY_SOURCE: &str = r#"
forall a set, b set:
    $is_set(a)
    $is_set(b)
    a != b
    =>:
        b != a
"#;

#[test]
fn not_equal_symmetry_is_a_builtin_rule_with_a_negative_boundary() {
    let mut runtime = Runtime::with_named_source("not-equality-symmetry-positive");
    let (results, error) = execute_source(SYMMETRY_SOURCE, &mut runtime);
    let (succeeded, output) = render_run_output(&runtime, &results, &error);
    assert!(succeeded, "not-equality symmetry should verify:\n{output}");
    assert!(
        output.contains("not-equality symmetry"),
        "the proof should name the builtin route:\n{output}"
    );

    let mut negative_runtime = Runtime::with_named_source("not-equality-symmetry-negative");
    let (negative_results, negative_error) =
        execute_source("have a, b R\nb != a", &mut negative_runtime);
    let (negative_succeeded, negative_output) =
        render_run_output(&negative_runtime, &negative_results, &negative_error);
    assert!(
        !negative_succeeded,
        "symmetry must not invent a non-equality premise:\n{negative_output}"
    );

    let known_forall_source = r#"
abstract_prop marked(x)

trust forall a, b R:
    $marked(a)
    =>:
        a != b

have x, y R
trust $marked(x)
y != x
"#;
    let mut known_forall_runtime = Runtime::with_named_source("not-equality-symmetry-known-forall");
    let (known_forall_results, known_forall_error) =
        execute_source(known_forall_source, &mut known_forall_runtime);
    let (known_forall_succeeded, known_forall_output) = render_run_output(
        &known_forall_runtime,
        &known_forall_results,
        &known_forall_error,
    );
    assert!(
            known_forall_succeeded,
            "the later full-verifier symmetry fallback should retain known-forall proofs:\n{known_forall_output}"
        );
}

#[test]
fn not_equal_symmetry_compiles_from_recursive_forall_results() {
    let generated =
        compile_litex_source_to_lean_source(SYMMETRY_SOURCE, "not-equality-symmetry-compiler")
            .expect("the recursive forall Result retains every proof-scope FactId");
    assert!(generated.contains("Litex.Rules.notSameSymm"), "{generated}");
    assert!(
        generated.contains("__domain3 : ¬ @Litex.Same"),
        "{generated}"
    );
}
