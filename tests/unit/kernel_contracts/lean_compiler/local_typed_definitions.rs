use super::super::*;
use super::run_registered_rule_test;

const LOCAL_TYPED_SET_DEFINITION_SOURCE: &str = r#"
thm local_typed_set_definition:
    ? forall marker R:
        marker = marker
        =>:
            marker = marker
    have E power_set(R) = {x R: x = 0}
    marker = marker
"#;

fn execute_source() -> Vec<StmtResult> {
    crate::lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        LOCAL_TYPED_SET_DEFINITION_SOURCE,
        "local_typed_set_definition.lit",
    )
    .expect("execute local typed-set definition")
}

fn theorem_proof_steps_mut(results: &mut [StmtResult]) -> &mut [StmtResult] {
    let [StmtResult::Success(SuccessStmtResult::Definition(
        SuccessDefinitionStmtResult::DefThmStmt(theorem),
    ))] = results
    else {
        panic!("expected one named theorem Result")
    };
    theorem
        .verification
        .as_mut()
        .expect("named theorem must retain verification")
        .proof_steps
        .as_mut_slice()
}

#[test]
fn local_typed_set_definition_compiles_from_exact_result_evidence() {
    run_registered_rule_test(|| {
        let results = execute_source();
        let generated = StmtResultToLeanCompiler::new("local_typed_set_definition.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile local typed-set definition");

        assert!(
            generated.contains("let E : Litex.Set := (Litex.setBuilder"),
            "{generated}"
        );
        assert!(
            generated.contains("Litex.Rules.setBuilderInPowerSetViaParamSubset"),
            "{generated}"
        );
        for forbidden in ["LitexObject", "Litex.Object", "Set.univ", "sorry", "axiom "] {
            assert!(
                !generated.contains(forbidden),
                "forbidden `{forbidden}` in:\n{generated}"
            );
        }
    });
}

#[test]
fn local_typed_set_definition_rejects_a_missing_frozen_fact_id() {
    run_registered_rule_test(|| {
        let mut results = execute_source();
        let proof_steps = theorem_proof_steps_mut(&mut results);
        let StmtResult::Success(SuccessStmtResult::Definition(
            SuccessDefinitionStmtResult::HaveObjEqualStmt(definition),
        )) = &mut proof_steps[0]
        else {
            panic!("expected local have-object equality as proof step one")
        };
        definition.common.infers.store_fact_outputs[0].fact_id = None;

        let error = StmtResultToLeanCompiler::new("local_typed_set_definition.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("a missing local definition FactId must fail closed");
        assert!(error.contains("FactId"), "{error}");
    });
}
