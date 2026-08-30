use super::super::*;
use crate::output::display_stmt_result_json_v2;

#[test]
fn combined_builtin_items_retain_and_compile_their_typed_component_evidence() {
    let results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "1 = 1 and 2 = 2\n",
            "combined_builtin_items.lit",
        )
        .expect("execute conjunction fixture");
    let [StmtResult::Success(SuccessStmtResult::Fact(result))] = results.as_slice() else {
        panic!("expected one successful conjunction Result")
    };
    let target = result.fact();
    let SuccessFactProofResult::CombinedProofs(combined) = result.proof() else {
        panic!("expected recursive combined proof Result")
    };

    let proof = StmtResultToLeanCompiler::new("combined_builtin_items.lit")
        .construct_lean_combined_fact_proof_from_result(&target, combined)
        .expect("compile typed combined builtin items")
        .expect("typed combined builtin items are direct");
    assert_eq!(proof, "⟨Litex.Same.refl (1 : ℂ), Litex.Same.refl (2 : ℂ)⟩");
}

fn execute_structured_integer_induction_from(start: &str) -> Vec<StmtResult> {
    let source = format!(
        "by induc n from {start}:\n    ? n + 1 = n + 1\n    ? from n = {start}:\n        {start} + 1 = {start} + 1\n    ? induc:\n        n + 1 + 1 = n + 1 + 1\n"
    );
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        &source,
        "structured_integer_induction_result.lit",
    )
    .expect("execute structured integer induction")
}

fn structured_integer_induction_result_mut(
    results: &mut [StmtResult],
) -> &mut SuccessByInducStmtResult {
    let [StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByInducStmt(result)))] =
        results
    else {
        panic!("expected one successful structured induction Result")
    };
    result
}

#[test]
fn structured_integer_induction_retains_named_recursive_results_and_exact_fact_ids() {
    let mut results = execute_structured_integer_induction_from("-1");
    let result = structured_integer_induction_result_mut(&mut results);
    let verification = result
        .verification
        .as_ref()
        .expect("structured induction retains its verification Result");
    let SuccessVerifyByInducProofResult::IntegerStructured(proof) = &verification.proof else {
        panic!("expected typed structured integer-induction proof")
    };

    assert_eq!(
        proof.start.to_string(),
        result.statement.induc_from.to_string()
    );
    assert_eq!(proof.base.proof_steps.len(), 1);
    assert_eq!(proof.step.proof_steps.len(), 1);
    assert_eq!(proof.base.conclusions.len(), 1);
    assert_eq!(proof.step.conclusions.len(), 1);

    let [base_parameter, base_equality] = proof.base.assumptions.as_slice() else {
        panic!("base case must retain its two named assumptions")
    };
    assert_eq!(
        base_parameter.role,
        SuccessVerifyByInducAssumptionRole::ParameterType
    );
    assert_eq!(
        base_equality.role,
        SuccessVerifyByInducAssumptionRole::BaseCaseEquality
    );
    assert_ne!(base_parameter.fact_id, base_equality.fact_id);

    let [step_parameter, step_domain, step_hypothesis] = proof.step.assumptions.as_slice() else {
        panic!("step case must retain parameter, domain, and hypothesis assumptions")
    };
    assert_eq!(
        step_parameter.role,
        SuccessVerifyByInducAssumptionRole::ParameterType
    );
    assert_eq!(
        step_domain.role,
        SuccessVerifyByInducAssumptionRole::DomainLowerBound
    );
    assert_eq!(
        step_hypothesis.role,
        SuccessVerifyByInducAssumptionRole::InductionHypothesis
    );
    assert_eq!(step_hypothesis.goal_index, Some(0));
    assert_ne!(step_parameter.fact_id, step_domain.fact_id);
    assert_ne!(step_domain.fact_id, step_hypothesis.fact_id);
    for assumption in proof
        .base
        .assumptions
        .iter()
        .chain(proof.step.assumptions.iter())
    {
        let case_infers = if proof
            .base
            .assumptions
            .iter()
            .any(|candidate| candidate.fact_id == assumption.fact_id)
        {
            &proof.base.assumption_infers
        } else {
            &proof.step.assumption_infers
        };
        assert!(infer_result_retains_fact_id(
            case_infers,
            &assumption.fact,
            assumption.fact_id
        ));
    }
    assert_eq!(
        proof.base.conclusions[0].goal.to_string(),
        proof.base.conclusions[0]
            .check
            .factual_success()
            .expect("base conclusion check is factual")
            .fact()
            .to_string()
    );
    assert_eq!(
        proof.step.conclusions[0].goal.to_string(),
        proof.step.conclusions[0]
            .check
            .factual_success()
            .expect("step conclusion check is factual")
            .fact()
            .to_string()
    );
}

#[test]
fn structured_integer_induction_compiler_follows_result_scopes_and_balances_its_stack() {
    let results = execute_structured_integer_induction_from("-1");
    let mut compiler = StmtResultToLeanCompiler::new("structured_integer_induction_result.lit");
    for result in &results {
        compiler
            .compile_stmt_result(result)
            .expect("compile recursive structured induction Result");
    }
    assert!(compiler.environment_stack.is_top_level());
    let generated = compiler.finish_lean_source().expect("finish Lean source");
    assert!(
        generated.contains("Litex.Rules.integerInductionFrom"),
        "{generated}"
    );
}

#[test]
fn structured_integer_induction_rejects_a_retargeted_hypothesis_fact_id() {
    let mut results = execute_structured_integer_induction_from("-1");
    let result = structured_integer_induction_result_mut(&mut results);
    let verification = result
        .verification
        .as_mut()
        .expect("structured induction retains verification");
    let SuccessVerifyByInducProofResult::IntegerStructured(proof) = &mut verification.proof else {
        panic!("expected structured integer induction")
    };
    proof.step.assumptions[2].fact_id = proof.step.assumptions[1].fact_id;

    let error = StmtResultToLeanCompiler::new("corrupted_structured_induction.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("retargeted local FactId must fail closed");
    assert!(error.contains("lost FactId"), "{error}");
}

#[test]
fn structured_integer_induction_rejects_a_changed_conclusion_result() {
    let mut results = execute_structured_integer_induction_from("-1");
    let result = structured_integer_induction_result_mut(&mut results);
    let verification = result
        .verification
        .as_mut()
        .expect("structured induction retains verification");
    let SuccessVerifyByInducProofResult::IntegerStructured(proof) = &mut verification.proof else {
        panic!("expected structured integer induction")
    };
    proof.step.conclusions[0].goal = proof.step.assumptions[1].fact.clone();

    let error = StmtResultToLeanCompiler::new("corrupted_structured_induction.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("changed conclusion must fail closed");
    assert!(error.contains("changed its checked goal"), "{error}");
}

#[test]
fn structured_integer_induction_zero_and_strong_boundaries_fail_closed() {
    let zero_results = execute_structured_integer_induction_from("0");
    let zero_error = StmtResultToLeanCompiler::new("zero_structured_induction.lit")
        .compile_stmt_results_to_lean_source(&zero_results)
        .expect_err("zero-ended order lowering must fail closed");
    assert!(zero_error.contains("nonnegative-value"), "{zero_error}");

    let strong_source = "by strong_induc n from -1:\n    ? n + 1 = n + 1\n    ? from n = -1:\n        -1 + 1 = -1 + 1\n    ? strong_induc:\n        n + 1 + 1 = n + 1 + 1\n";
    let strong_results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            strong_source,
            "strong_structured_induction.lit",
        )
        .expect("execute structured strong induction");
    let strong_error = StmtResultToLeanCompiler::new("strong_structured_induction.lit")
        .compile_stmt_results_to_lean_source(&strong_results)
        .expect_err("strong induction must fail closed until its Result compiler lands");
    assert!(strong_error.contains("strong induction"), "{strong_error}");
}

#[test]
fn forall_result_retains_exact_parameter_and_domain_fact_ids_for_compiler_scope() {
    let source = "forall a set, b set:\n    $is_set(a)\n    $is_set(b)\n    a != b\n    =>:\n        b != a\n";
    let results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            source,
            "direct_forall_scope_fact_ids.lit",
        )
        .expect("execute forall before dropping Runtime");
    let [StmtResult::Success(SuccessStmtResult::Fact(result))] = results.as_slice() else {
        panic!("expected one successful forall Result")
    };
    let SuccessFactProofResult::ForallProof(proof) = result.proof() else {
        panic!("expected recursive ForallProof Result")
    };
    assert_eq!(proof.parameter_assumptions.len(), 2);
    assert_eq!(proof.domain_assumptions.len(), 3);
    assert_eq!(
        proof.parameter_assumptions[0].fact_id,
        proof.domain_assumptions[0].fact_id
    );
    assert_eq!(
        proof.parameter_assumptions[1].fact_id,
        proof.domain_assumptions[1].fact_id
    );
    assert_ne!(
        proof.domain_assumptions[2].fact_id,
        proof.parameter_assumptions[0].fact_id
    );

    let json = display_stmt_result_json_v2(&results[0]);
    assert!(json.contains("\"parameter_assumptions\""), "{json}");
    assert!(json.contains("\"domain_assumptions\""), "{json}");

    let generated = StmtResultToLeanCompiler::new("direct_forall_scope_fact_ids.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile only from the frozen recursive Result");
    assert!(generated.contains("Litex.Rules.notSameSymm"), "{generated}");
}

#[test]
fn nested_compiler_environment_inherits_outer_bindings_without_leaking_back() {
    let outer_fact_id = FactId::new(1);
    let inner_fact_id = FactId::new(2);
    let inner_integer_symbol_id = SymbolId::new(3);
    let mut outer = StmtResultToLeanCompilerEnvironmentStack::default();
    outer
        .fact_names
        .insert(outer_fact_id, "__outer".to_string());

    let mut inner = outer.clone();
    inner.push_inherited_environment();
    assert_eq!(inner.environments.len(), 2);
    assert_eq!(
        inner.fact_names.get(&outer_fact_id),
        Some(&"__outer".to_string())
    );
    inner
        .fact_names
        .insert(inner_fact_id, "__inner".to_string());
    inner
        .numeric_integer_values
        .insert(inner_integer_symbol_id, "(__inner_integer : ℤ)".to_string());
    inner.numeric_rational_values.insert(
        inner_integer_symbol_id,
        "(__inner_rational : ℚ)".to_string(),
    );

    assert!(!outer.fact_names.contains_key(&inner_fact_id));
    assert!(!outer
        .numeric_integer_values
        .contains_key(&inner_integer_symbol_id));
    assert!(!outer
        .numeric_rational_values
        .contains_key(&inner_integer_symbol_id));
    assert_eq!(
        inner.fact_names.get(&inner_fact_id),
        Some(&"__inner".to_string())
    );
    inner.pop_local_environment();
    assert_eq!(inner.environments.len(), 1);
    assert!(!inner.fact_names.contains_key(&inner_fact_id));
    assert!(!inner
        .numeric_integer_values
        .contains_key(&inner_integer_symbol_id));
    assert!(!inner
        .numeric_rational_values
        .contains_key(&inner_integer_symbol_id));
    assert_eq!(
        inner.fact_names.get(&outer_fact_id),
        Some(&"__outer".to_string())
    );
}

#[test]
fn failed_local_result_compilation_restores_the_outer_compiler_layer() {
    let outer_fact_id = FactId::new(1);
    let mut compiler = StmtResultToLeanCompiler::new("local_failure.lit");
    compiler.declarations.push("outer declaration".into());
    compiler.next_fact_name_index = 7;
    compiler.next_sketch_namespace_index = 3;
    compiler
        .environment_stack
        .fact_names
        .insert(outer_fact_id, "__outer".into());

    let unknown: StmtResult =
        UnknownGenericStmtResult::new_with_detail("deliberate local compiler failure".into())
            .into();
    let error = compiler
        .compile_stmt_results_in_new_local_environment(&[unknown])
        .expect_err("unknown local result must fail closed");

    assert!(error.contains("cannot compile unknown result"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    assert_eq!(compiler.declarations, ["outer declaration"]);
    assert_eq!(compiler.next_fact_name_index, 7);
    assert_eq!(compiler.next_sketch_namespace_index, 3);
    assert_eq!(
        compiler.environment_stack.fact_names.get(&outer_fact_id),
        Some(&"__outer".to_string())
    );
}
