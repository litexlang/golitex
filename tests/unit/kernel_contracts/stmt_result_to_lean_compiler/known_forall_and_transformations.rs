use super::super::*;
use super::run_registered_rule_test;

fn execute_known_forall_instantiation() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        "abstract_prop p(x)\naxiom p_real:\n    ? forall x R:\n        $p(x)\n\n$p(2)\n",
        "direct_known_forall.lit",
    )
    .expect("execute known-forall instantiation")
}

fn known_forall_instantiation_result_mut(
    results: &mut [StmtResult],
) -> &mut SuccessInstantiateKnownForallResult {
    let [_, _, StmtResult::Success(SuccessStmtResult::Fact(result))] = results else {
        panic!("expected abstract predicate, source axiom, and instantiated fact")
    };
    let verification =
        std::rc::Rc::get_mut(&mut result.verification).expect("test result has one proof owner");
    let SuccessFactProofResult::KnownForallInstantiation(instantiation) = verification.proof_mut()
    else {
        panic!("expected known-forall proof Result")
    };
    instantiation
}

#[test]
fn known_forall_instantiation_combines_exact_fact_id_and_requirement_result_directly() {
    run_registered_rule_test(|| {
        let results = execute_known_forall_instantiation();
        let generated = StmtResultToLeanCompiler::new("direct_known_forall.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile known-forall Result directly");

        assert!(generated.contains("axiom p_real"), "{generated}");
        assert!(
                generated.contains("exact (p_real (2 : ℂ) (Litex.Rules.complexRealInR")
                    && generated.contains("complexRealInR (2 : ℝ)"),
                "known-forall application did not combine its source theorem and parameter requirement: {generated}"
            );
    });
}

fn execute_multi_conclusion_known_forall_instantiation() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        "abstract_prop first(x)\nabstract_prop second(x)\naxiom paired_source:\n    ? forall x R:\n        $first(x)\n        $second(x)\n\n$second(2)\n",
        "direct_multi_conclusion_known_forall.lit",
    )
    .expect("execute multi-conclusion known-forall instantiation")
}

fn multi_conclusion_known_forall_instantiation_result_mut(
    results: &mut [StmtResult],
) -> &mut SuccessInstantiateKnownForallResult {
    let result = results
        .last_mut()
        .and_then(StmtResult::factual_success_mut)
        .expect("final result should be the instantiated second conclusion");
    let verification =
        std::rc::Rc::get_mut(&mut result.verification).expect("test result has one proof owner");
    let SuccessFactProofResult::KnownForallInstantiation(instantiation) = verification.proof_mut()
    else {
        panic!("expected known-forall proof Result")
    };
    instantiation
}

#[test]
fn known_forall_instantiation_projects_the_selected_multi_conclusion_source() {
    run_registered_rule_test(|| {
        let results = execute_multi_conclusion_known_forall_instantiation();
        let generated = StmtResultToLeanCompiler::new("direct_multi_conclusion_known_forall.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile selected multi-conclusion known-forall source");

        assert!(generated.contains("axiom paired_source"), "{generated}");
        assert!(
            generated.contains("paired_source") && generated.contains(".2"),
            "the compiler did not project the retained second conclusion: {generated}"
        );
    });
}

#[test]
fn known_forall_instantiation_rejects_a_corrupted_multi_conclusion_location() {
    run_registered_rule_test(|| {
        let mut results = execute_multi_conclusion_known_forall_instantiation();
        multi_conclusion_known_forall_instantiation_result_mut(&mut results)
            .source_conclusion_location = ForallConclusionLocation::direct_then_fact(0);

        let error = StmtResultToLeanCompiler::new("direct_multi_conclusion_known_forall.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("corrupted multi-conclusion location must fail closed");
        assert!(
            error.contains("does not match target"),
            "unexpected corruption error: {error}"
        );
    });
}

#[test]
fn known_forall_instantiation_rejects_a_corrupted_source_fact_id() {
    run_registered_rule_test(|| {
        let mut results = execute_multi_conclusion_known_forall_instantiation();
        multi_conclusion_known_forall_instantiation_result_mut(&mut results).source_fact_id =
            FactId::new(u64::MAX);

        let error = StmtResultToLeanCompiler::new("direct_multi_conclusion_known_forall.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("corrupted known-forall source FactId must fail closed");
        assert!(
            error.contains("unavailable cited fact `f18446744073709551615`"),
            "unexpected corruption error: {error}"
        );
    });
}

#[test]
fn known_forall_instantiation_rejects_a_reclassified_parameter_requirement() {
    run_registered_rule_test(|| {
        let mut results = execute_known_forall_instantiation();
        known_forall_instantiation_result_mut(&mut results).requirements[0].kind =
            KnownForallRequirementKind::Domain;

        let error = StmtResultToLeanCompiler::new("direct_known_forall.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("reclassified known-forall requirement must fail closed");
        assert!(error.contains("parameter requirement 0 changed its kind"));
    });
}

#[test]
fn function_application_return_membership_resolves_its_exact_well_definedness_fact_id() {
    run_registered_rule_test(|| {
        let results = crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
                "trust have f fn(x R) R\ntrust have a R\nf(a) $in R\n",
                "direct_function_application_return_membership.lit",
            )
            .expect("execute exact function-return membership");
        let result = results
            .last()
            .and_then(StmtResult::factual_success)
            .expect("function-return membership is factual");
        assert!(result.well_definedness.recursive.is_some());

        let generated =
            StmtResultToLeanCompiler::new("direct_function_application_return_membership.lit")
                .compile_stmt_results_to_lean_source(&results)
                .expect("compile exact function-return membership directly");
        assert!(
            generated.contains("Litex.In.own Litex.R") && generated.contains("Litex.fnApply"),
            "function-return membership did not use its retained application layer: {generated}"
        );
    });
}

#[test]
fn trust_have_rejects_a_missing_parameter_store_fact_id() {
    run_registered_rule_test(|| {
        let mut results = crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
                "trust have a R\n",
                "direct_trust_have.lit",
            )
            .expect("execute trusted object declaration");
        let [StmtResult::Success(SuccessStmtResult::UnsafeStmt(
            SuccessUnsafeStmtResult::TrustHaveStmt(result),
        ))] = results.as_mut_slice()
        else {
            panic!("expected one trust-have Result")
        };
        result.common.infers.store_fact_outputs[0].fact_id = None;

        let error = StmtResultToLeanCompiler::new("direct_trust_have.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("missing trusted binding FactId must fail closed");
        assert!(error.contains("parameter store 0 has no FactId"), "{error}");
    });
}

#[test]
fn known_fact_rational_transformation_replays_its_ordered_result_steps() {
    run_registered_rule_test(|| {
        const SOURCE: &str = "trust:\n    2 < 3\n1 + 1 < 3\n";
        let results = crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
                SOURCE,
                "direct_fact_transformation.lit",
            )
            .expect("execute a rationally normalized known-fact citation");
        let result = results
            .last()
            .and_then(StmtResult::factual_success)
            .expect("normalized citation is factual");
        let SuccessFactProofResult::Transform(transformation) = result.proof() else {
            panic!(
                "expected recursive fact transformation, got {:#?}",
                result.proof()
            )
        };
        assert!(matches!(
            transformation.rule,
            FactTransformationRule::RationalNormalization
        ));
        assert!(matches!(
            transformation.source.proof(),
            SuccessFactProofResult::StoredFactCitation(_)
        ));

        let generated = StmtResultToLeanCompiler::new("direct_fact_transformation.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile ordered fact transformation");
        assert!(generated.contains("convert __fact0 using 1 <;> norm_num"));
    });
}

#[test]
fn known_fact_transformation_rejects_a_removed_result_step() {
    run_registered_rule_test(|| {
        let mut results = crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
                "trust:\n    2 < 3\n1 + 1 < 3\n",
                "direct_fact_transformation.lit",
            )
            .expect("execute a rationally normalized known-fact citation");
        let result = results
            .last_mut()
            .and_then(StmtResult::factual_success_mut)
            .expect("normalized citation is factual");
        let verification = std::rc::Rc::get_mut(&mut result.verification)
            .expect("test citation has one verification owner");
        let SuccessFactProofResult::Transform(transformation) = verification.proof_mut() else {
            panic!("expected recursive fact transformation")
        };
        let source = std::rc::Rc::get_mut(&mut transformation.source)
            .expect("test owns the nested transformation source");
        *source.proof_mut() =
            SuccessFactProofResult::DiagnosticOnly(SuccessDiagnosticFactProofResult {
                detail: "corrupted nested source".to_string(),
            });

        let error = StmtResultToLeanCompiler::new("direct_fact_transformation.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("removed transformation step must fail closed");
        assert!(
            error.contains("does not support") || error.contains("no direct"),
            "{error}"
        );
    });
}
