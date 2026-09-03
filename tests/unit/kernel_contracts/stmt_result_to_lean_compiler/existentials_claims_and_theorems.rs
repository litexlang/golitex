use super::super::*;

#[test]
fn explicit_source_axiom_preserves_its_name_and_fact_id() {
    let results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "axiom source_reflexivity:\n    ? forall x R:\n        x = x\n",
            "direct_source_axiom.lit",
        )
        .expect("execute explicit source axiom");
    let generated = StmtResultToLeanCompiler::new("direct_source_axiom.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile explicit source axiom");
    assert!(
        generated.contains("axiom source_reflexivity"),
        "{generated}"
    );
    assert!(!generated.contains("sorry"), "{generated}");
}

fn rename_object_choice_nonempty_diagnostic_label(results: &mut [StmtResult]) {
    let Some(StmtResult::Success(SuccessStmtResult::Definition(
        SuccessDefinitionStmtResult::HaveObjInNonemptySetStmt(choice),
    ))) = results.first_mut()
    else {
        panic!("expected object-choice statement result")
    };
    let verification = choice
        .verification
        .as_mut()
        .expect("object choice retains verification result");
    let nonempty = verification.groups[0]
        .nonempty_check
        .as_deref_mut()
        .expect("standard carrier retains nonempty check");
    let factual = nonempty.verified_mut().expect("nonempty check is factual");
    let SuccessFactProofResult::BuiltinRule(proof) = factual.proof_mut() else {
        panic!("expected standard-set builtin proof")
    };
    proof.msg = "diagnostic label is not semantic input".into();
}

#[test]
fn direct_object_choice_compiler_uses_typed_child_evidence_not_its_label() {
    const SOURCE: &str = "have chosen R\nchosen $in R\n";
    let original =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            SOURCE,
            "direct_object_choice.lit",
        )
        .expect("execute object choice");
    let original_lean = StmtResultToLeanCompiler::new("direct_object_choice.lit")
        .compile_stmt_results_to_lean_source(&original)
        .expect("compile object choice");

    let mut renamed =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            SOURCE,
            "direct_object_choice.lit",
        )
        .expect("execute object choice again");
    rename_object_choice_nonempty_diagnostic_label(&mut renamed);
    let renamed_lean = StmtResultToLeanCompiler::new("direct_object_choice.lit")
        .compile_stmt_results_to_lean_source(&renamed)
        .expect("compile object choice after diagnostic-only mutation");

    assert_eq!(renamed_lean, original_lean);
    assert!(original_lean.contains("Classical.choice (Litex.Rules.realNonempty)"));
    assert!(original_lean.contains("Litex.In.own Litex.R chosen"));
}

fn execute_single_existential_witness() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        "witness exist x R st {x = 1} from 1:\n    1 = 1\n",
        "direct_existential_witness.lit",
    )
    .expect("execute one-witness existential introduction")
}

fn single_existential_witness_result_mut(
    results: &mut [StmtResult],
) -> &mut SuccessWitnessExistFactResult {
    let [StmtResult::Success(SuccessStmtResult::Witness(
        SuccessWitnessStmtResult::WitnessExistFact(result),
    ))] = results
    else {
        panic!("expected one successful existential-witness result")
    };
    result
}

#[test]
fn existential_witness_compiles_directly_from_named_recursive_children() {
    let mut results = execute_single_existential_witness();
    let result = single_existential_witness_result_mut(&mut results);
    let local_fact_id = result
        .verification
        .as_ref()
        .expect("witness retains verification")
        .proof_steps[0]
        .factual_success()
        .expect("witness proof step is factual")
        .store
        .fact_id
        .expect("witness proof step retains its local FactId");
    let outer_fact_id = result.common.infers.store_fact_outputs[0]
        .fact_id
        .expect("witness outer store retains its FactId");

    let mut compiler = StmtResultToLeanCompiler::new("direct_existential_witness.lit");
    assert!(compiler
        .compile_witness_exist_fact_stmt_result_to_lean_source(result)
        .expect("direct existential-witness compilation succeeds"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    assert!(!compiler
        .environment_stack
        .fact_names
        .contains_key(&local_fact_id));
    assert_eq!(
        compiler.environment_stack.fact_names.get(&outer_fact_id),
        Some(&"__fact0".to_string())
    );
    assert!(compiler.declarations[0]
        .contains("∃ (x : (Litex.R).Carrier), ∃ (__type_x : Litex.In x Litex.R)"));
    assert!(compiler.declarations[0].contains("Litex.Same x (1 : ℂ)"));
    assert!(compiler.declarations[0].contains("have __step"));
    assert!(compiler.declarations[0].contains("Litex.In.own Litex.R (1 : ℝ)"));
    assert!(compiler.declarations[0].contains("Litex.Same.realComplex"));
    assert!(!compiler.declarations[0].contains("Litex.In.rep (1 : ℂ)"));
}

#[test]
fn existential_witness_rejects_a_missing_parameter_check_child() {
    let mut results = execute_single_existential_witness();
    let result = single_existential_witness_result_mut(&mut results);
    result
        .verification
        .as_mut()
        .expect("witness retains verification")
        .parameter_checks[0] = None;

    let error = StmtResultToLeanCompiler::new("direct_existential_witness.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("missing parameter child must fail closed");
    assert!(error.contains("has no parameter-check child Result"));
}

#[test]
fn existential_witness_rejects_a_missing_outer_fact_id() {
    let mut results = execute_single_existential_witness();
    let result = single_existential_witness_result_mut(&mut results);
    result.common.infers.store_fact_outputs[0].fact_id = None;

    let error = StmtResultToLeanCompiler::new("direct_existential_witness.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("missing outer FactId must fail closed");
    assert!(error.contains("existential witness outer effect store has no FactId"));
}

#[test]
fn existential_elimination_uses_source_and_projection_fact_ids_directly() {
    let results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "witness exist x R st {x = 1} from 1:\n    1 = 1\nobtain y from exist x R st {x = 1}\n",
            "direct_existential_elimination.lit",
        )
        .expect("execute existential introduction and elimination");
    let [StmtResult::Success(SuccessStmtResult::Witness(
        SuccessWitnessStmtResult::WitnessExistFact(witness),
    )), StmtResult::Success(SuccessStmtResult::Definition(
        SuccessDefinitionStmtResult::ObtainObjFromExistFact(elimination),
    ))] = results.as_slice()
    else {
        panic!("expected witness followed by existential elimination")
    };
    let source_fact_id = witness.common.infers.store_fact_outputs[0]
        .fact_id
        .expect("witness retains source FactId");
    let source_citation = elimination
        .verification
        .as_ref()
        .expect("elimination retains verification")
        .source_result
        .fact()
        .and_then(VerifyFactResult::verified)
        .expect("elimination source is factual");
    let SuccessFactProofResult::StoredFactCitation(source_citation) = source_citation.proof()
    else {
        panic!("elimination source cites the stored existential")
    };
    assert_eq!(source_citation.source_fact_id, source_fact_id);

    let mut compiler = StmtResultToLeanCompiler::new("direct_existential_elimination.lit");
    assert!(compiler
        .compile_witness_exist_fact_stmt_result_to_lean_source(witness)
        .expect("compile direct existential introduction"));
    assert!(compiler
        .compile_obtain_obj_from_exist_fact_stmt_result_to_lean_source(elimination)
        .expect("compile direct existential elimination"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    assert!(compiler.declarations[1]
        .contains("noncomputable def y : (Litex.R).Carrier := Classical.choose"));
    assert!(compiler.declarations[1].contains("from __fact0"));
    assert!(compiler.declarations[2].contains("Classical.choose_spec"));
    assert!(compiler.declarations[2].contains("from __fact0"));
    assert!(compiler.declarations[2].contains(").1"));
    assert!(compiler.declarations[3].contains("Classical.choose_spec"));
    assert!(compiler.declarations[3].contains("from __fact0"));
    assert!(compiler.declarations[3].contains(").2"));
}

#[test]
fn existential_elimination_rejects_a_projection_without_fact_id() {
    let mut results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "witness exist x R st {x = 1} from 1:\n    1 = 1\nobtain y from exist x R st {x = 1}\n",
            "direct_existential_elimination.lit",
        )
        .expect("execute existential introduction and elimination");
    let StmtResult::Success(SuccessStmtResult::Definition(
        SuccessDefinitionStmtResult::ObtainObjFromExistFact(elimination),
    )) = &mut results[1]
    else {
        panic!("expected existential elimination")
    };
    elimination.common.infers.store_fact_outputs[1].fact_id = None;

    let error = StmtResultToLeanCompiler::new("direct_existential_elimination.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("projection without FactId must fail closed");
    assert!(
        error.contains("existential elimination store 1 has incomplete frozen fact identities"),
        "{error}"
    );
}

fn execute_predicate_backed_existential_elimination() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "prop has_copy(a R):\n    exist x R st {x = a}\nwitness exist x R st {x = 2} from 2:\n    2 = 2\nby def $has_copy(2)\nobtain copy from $has_copy(2)\n",
            "direct_predicate_backed_existential_elimination.lit",
        )
        .expect("execute predicate-backed existential elimination")
}

#[test]
fn predicate_backed_existential_elimination_compiles_definition_projection_directly() {
    let results = execute_predicate_backed_existential_elimination();
    let [definition, witness, by_definition, StmtResult::Success(SuccessStmtResult::Definition(
        SuccessDefinitionStmtResult::ObtainObjFromAtomicFact(elimination),
    ))] = results.as_slice()
    else {
        panic!("expected predicate definition, witness, by-definition, and obtain")
    };

    let mut compiler =
        StmtResultToLeanCompiler::new("direct_predicate_backed_existential_elimination.lit");
    for result in [definition, witness, by_definition] {
        compiler
            .compile_stmt_result(result)
            .expect("compile prerequisite Result directly");
    }
    assert!(compiler
        .compile_obtain_obj_from_atomic_fact_stmt_result_to_lean_source(elimination)
        .expect("compile predicate-backed elimination directly"));
    assert!(compiler
        .declarations
        .iter()
        .any(|declaration| declaration.contains("unfold has_copy at __definition")));
    assert!(compiler
        .declarations
        .iter()
        .any(|declaration| declaration.contains("noncomputable def copy")));
}

#[test]
fn predicate_backed_existential_elimination_rejects_a_retargeted_source_publication() {
    let mut results = execute_predicate_backed_existential_elimination();
    let StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByDefStmt(by_definition))) =
        &mut results[2]
    else {
        panic!("expected by-definition prerequisite")
    };
    let source_fact_id = by_definition.common.infers.store_fact_outputs[0]
        .fact_id
        .expect("by-definition retains source FactId");
    by_definition.common.infers.store_fact_outputs[0].fact_id =
        Some(FactId::new(source_fact_id.value() + 10_000));

    let mut compiler =
        StmtResultToLeanCompiler::new("direct_predicate_backed_existential_elimination.lit");
    for result in &results[..2] {
        compiler
            .compile_stmt_result(result)
            .expect("compile prerequisites before the corrupted publication");
    }
    let error = compiler
        .compile_stmt_result(&results[2])
        .expect_err("retargeting the source publication must fail at its typed infer edge");
    assert!(
        error.contains(&format!("unavailable cited fact `{source_fact_id}`")),
        "{error}"
    );
}

fn execute_direct_cases_and_contradiction() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "by cases:\n    ? 2 = 2\n    case 1 = 1 and 2 = 2:\n        1 = 1\nby contra:\n    ? not 2 < 1\n    impossible 2 < 1\n",
            "direct_cases_and_contradiction.lit",
        )
        .expect("execute direct cases and contradiction")
}

#[test]
fn cases_and_contradiction_compile_directly_in_nested_environments() {
    let results = execute_direct_cases_and_contradiction();
    let [StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByCasesStmt(cases))), StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByContraStmt(
        contradiction,
    )))] = results.as_slice()
    else {
        panic!("expected cases followed by contradiction")
    };
    let branch = &cases
        .verification
        .as_ref()
        .expect("cases retains verification")
        .branches[0];
    let branch_assumption_fact_id = branch.assumption_fact_id;
    let branch_component_fact_ids = branch
        .proof_scope
        .assumption_components
        .iter()
        .map(|(fact_id, _)| *fact_id)
        .collect::<Vec<_>>();
    let reverse_assumption_fact_id = contradiction
        .verification
        .as_ref()
        .expect("contra retains verification")
        .reverse_assumption_fact_id;

    let mut compiler = StmtResultToLeanCompiler::new("direct_cases_and_contradiction.lit");
    let coverage = cases
        .verification
        .as_ref()
        .expect("cases retains verification")
        .coverage_check
        .verified()
        .expect("coverage is factual");
    assert!(
        compiler
            .construct_lean_proof_from_direct_fact_result(coverage)
            .expect("construct coverage proof")
            .is_some(),
        "coverage proof remained unsupported: {:?}",
        coverage.proof()
    );
    assert!(compiler
        .compile_by_cases_stmt_result_to_lean_source(cases)
        .expect("compile cases directly"));
    assert!(compiler
        .compile_by_contra_stmt_result_to_lean_source(contradiction)
        .expect("compile contradiction directly"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    assert!(!compiler
        .environment_stack
        .fact_names
        .contains_key(&branch_assumption_fact_id));
    assert!(branch_component_fact_ids
        .iter()
        .all(|fact_id| !compiler.environment_stack.fact_names.contains_key(fact_id)));
    assert!(!compiler
        .environment_stack
        .fact_names
        .contains_key(&reverse_assumption_fact_id));
    assert!(compiler.declarations[0].contains("have __case1_component1"));
    assert!(compiler.declarations[0].contains("have __case1_component2"));
    assert!(compiler.declarations[1].contains("Classical.byContradiction"));
}

#[test]
fn cases_and_contradiction_tracer_compiles_from_recursive_results() {
    let source = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/lean/examples/9_CasesAndContradiction.lit"
    ));
    let results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            source,
            "9_CasesAndContradiction.lit",
        )
        .expect("execute cases-and-contradiction tracer");
    let lean_source = StmtResultToLeanCompiler::new("9_CasesAndContradiction.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile recursive cases-and-contradiction Results");
    assert!(lean_source.contains("__case1_component1"));
    assert!(lean_source.contains("Classical.byContradiction"));
}

#[test]
fn cases_reject_a_branch_assumption_fact_id_mismatch() {
    let mut results = execute_direct_cases_and_contradiction();
    let StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByCasesStmt(cases))) =
        &mut results[0]
    else {
        panic!("expected cases result")
    };
    let exported_fact_id = cases.common.infers.store_fact_outputs[0]
        .fact_id
        .expect("cases exports a FactId");
    cases
        .verification
        .as_mut()
        .expect("cases retains verification")
        .branches[0]
        .assumption_fact_id = exported_fact_id;

    let error = StmtResultToLeanCompiler::new("direct_cases_and_contradiction.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("mismatched branch FactId must fail closed");
    assert!(error.contains("branch assumption FactIds disagree"));
}

#[test]
fn contradiction_rejects_a_reverse_assumption_fact_id_mismatch() {
    let mut results = execute_direct_cases_and_contradiction();
    let StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByContraStmt(
        contradiction,
    ))) = &mut results[1]
    else {
        panic!("expected contradiction result")
    };
    let exported_fact_id = contradiction.common.infers.store_fact_outputs[0]
        .fact_id
        .expect("contradiction exports a FactId");
    contradiction
        .verification
        .as_mut()
        .expect("contradiction retains verification")
        .reverse_assumption_fact_id = exported_fact_id;

    let error = StmtResultToLeanCompiler::new("direct_cases_and_contradiction.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("mismatched reverse FactId must fail closed");
    assert!(error.contains("reverse-assumption FactIds disagree"));
}

fn execute_ordinary_claim() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        "claim:\n    ? 2 = 2\n    2 = 2\n",
        "direct_claim.lit",
    )
    .expect("execute ordinary claim")
}

fn ordinary_claim_result_mut(results: &mut [StmtResult]) -> &mut SuccessClaimStmtResult {
    let [StmtResult::Success(SuccessStmtResult::ProofBlock(SuccessProofBlockStmtResult::ClaimStmt(
        result,
    )))] = results
    else {
        panic!("expected one successful claim result")
    };
    result
}

#[test]
fn local_claim_proof_step_store_keeps_its_local_fact_id_after_outer_store() {
    let mut results = execute_ordinary_claim();
    let claim = ordinary_claim_result_mut(&mut results);
    let outer_fact_id = claim.environment_effects.store_fact_outputs[0]
        .fact_id
        .expect("claim outer store has a FactId");
    let local = claim.proof_steps[0]
        .factual_success()
        .expect("claim proof step is factual");
    let local_fact_id = local
        .store
        .fact_id
        .expect("local proof step has a frozen FactId");

    assert_ne!(local_fact_id, outer_fact_id);
    assert_eq!(
        local.store.infers.store_fact_outputs[0].fact_id,
        Some(local_fact_id)
    );
    let SuccessFactProofResult::StoredFactCitation(citation) = claim.conclusion_checks[0]
        .verified()
        .expect("claim conclusion is factual")
        .proof()
    else {
        panic!("claim conclusion cites its local proof step")
    };
    assert_eq!(citation.source_fact_id, local_fact_id);
}

#[test]
fn ordinary_claim_and_example_compile_directly_from_recursive_results() {
    let results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "claim:\n    ? 2 = 2\n    2 = 2\n\nexample:\n    ? 3 = 3\n    3 = 3\n",
            "direct_claim_and_example.lit",
        )
        .expect("execute claim and example");
    let [StmtResult::Success(SuccessStmtResult::ProofBlock(SuccessProofBlockStmtResult::ClaimStmt(
        claim,
    ))), StmtResult::Success(SuccessStmtResult::ProofBlock(
        SuccessProofBlockStmtResult::ExampleStmt(example),
    ))] = results.as_slice()
    else {
        panic!("expected claim and example results")
    };

    let mut compiler = StmtResultToLeanCompiler::new("direct_claim_and_example.lit");
    assert!(compiler
        .compile_claim_stmt_result_to_lean_source(claim)
        .expect("direct claim compilation succeeds"));
    assert!(compiler
        .compile_example_stmt_result_to_lean_source(example)
        .expect("direct example compilation succeeds"));
    assert!(compiler.declarations[0].contains("theorem __fact0"));
    assert!(compiler.declarations[0].contains("have __step"));
    assert!(compiler.declarations[0].contains("exact __step"));
    assert!(compiler.declarations[1].starts_with("example :"));
    assert!(compiler.declarations[1].contains("have __step1"));
}

#[test]
fn direct_claim_compiler_rejects_a_local_store_retargeted_to_the_outer_fact_id() {
    let mut results = execute_ordinary_claim();
    let claim = ordinary_claim_result_mut(&mut results);
    let outer_fact_id = claim.environment_effects.store_fact_outputs[0]
        .fact_id
        .expect("claim outer store has a FactId");
    claim.proof_steps[0]
        .factual_success_mut()
        .expect("claim proof step is factual")
        .store
        .infers
        .store_fact_outputs[0]
        .fact_id = Some(outer_fact_id);

    let error = StmtResultToLeanCompiler::new("direct_claim.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("retargeted local store must fail closed");
    assert!(error.contains("local proof-step store does not retain its exact FactId"));
}

fn execute_zero_binder_named_theorem() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        "thm one_eq_one:\n    ? forall:\n        1 = 1\n",
        "direct_zero_binder_theorem.lit",
    )
    .expect("execute zero-binder named theorem")
}

pub(super) fn named_theorem_result_mut(results: &mut [StmtResult]) -> &mut SuccessDefThmStmtResult {
    let [StmtResult::Success(SuccessStmtResult::Definition(
        SuccessDefinitionStmtResult::DefThmStmt(result),
    ))] = results
    else {
        panic!("expected one successful named-theorem result")
    };
    result
}

#[test]
fn zero_binder_named_theorem_compiles_directly_from_recursive_result() {
    let mut results = execute_zero_binder_named_theorem();
    let theorem = named_theorem_result_mut(&mut results);
    let mut compiler = StmtResultToLeanCompiler::new("direct_zero_binder_theorem.lit");

    assert!(compiler
        .compile_named_theorem_stmt_result_to_lean_source(theorem)
        .expect("direct zero-binder theorem compilation succeeds"));
    assert_eq!(compiler.declarations.len(), 1);
    assert!(compiler.declarations[0].starts_with("theorem one_eq_one :"));
    assert!(compiler.declarations[0].contains("have __c0_0"));
    assert!(compiler.declarations[0].contains("exact __c0_0"));
}

#[test]
fn zero_binder_named_theorem_compiler_ignores_conclusion_diagnostic_label() {
    let original = execute_zero_binder_named_theorem();
    let original_lean = StmtResultToLeanCompiler::new("direct_zero_binder_theorem.lit")
        .compile_stmt_results_to_lean_source(&original)
        .expect("compile original zero-binder theorem");

    let mut renamed = execute_zero_binder_named_theorem();
    let theorem = named_theorem_result_mut(&mut renamed);
    let conclusion = theorem
        .verification
        .as_mut()
        .expect("named theorem retains verification")
        .conclusion_checks[0]
        .verified_mut()
        .expect("named theorem conclusion is factual");
    let SuccessFactProofResult::BuiltinRule(proof) = conclusion.proof_mut() else {
        panic!("expected builtin conclusion proof")
    };
    proof.msg = "diagnostic-only theorem conclusion label".into();

    let renamed_lean = StmtResultToLeanCompiler::new("direct_zero_binder_theorem.lit")
        .compile_stmt_results_to_lean_source(&renamed)
        .expect("compile theorem after diagnostic-only mutation");
    assert_eq!(renamed_lean, original_lean);
}

#[test]
fn zero_binder_named_theorem_compiler_rejects_missing_outer_fact_id() {
    let mut results = execute_zero_binder_named_theorem();
    let theorem = named_theorem_result_mut(&mut results);
    theorem.common.infers.store_fact_outputs[0].fact_id = None;

    let error = StmtResultToLeanCompiler::new("direct_zero_binder_theorem.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("theorem without its frozen outer FactId must fail closed");
    assert!(
        error.contains("named forall Result lost its exact source FactId store"),
        "{error}"
    );
}

fn execute_named_atomic_theorem_and_direct_citation() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        "thm one_is_one:\n    ? 1 = 1\n\nrelease thm one_is_one\n",
        "direct_atomic_theorem.lit",
    )
    .expect("execute named atomic theorem and direct citation")
}

fn direct_theorem_citation_result_mut(
    results: &mut [StmtResult],
) -> &mut SuccessReleaseThmStmtResult {
    let [_, StmtResult::Success(SuccessStmtResult::ReleaseThmStmt(result))] = results else {
        panic!("expected an ordinary named theorem followed by its direct citation")
    };
    result
}

#[test]
fn ordinary_named_theorem_and_direct_citation_compile_once_by_exact_fact_id() {
    let results = execute_named_atomic_theorem_and_direct_citation();
    let [StmtResult::Success(SuccessStmtResult::Definition(
        SuccessDefinitionStmtResult::DefThmStmt(theorem),
    )), StmtResult::Success(SuccessStmtResult::ReleaseThmStmt(citation))] = results.as_slice()
    else {
        panic!("expected an ordinary named theorem followed by its direct citation")
    };
    let verification = citation
        .verification
        .as_ref()
        .expect("direct citation retains verification");
    let SuccessVerifyTheoremApplicationSourceResult::Litex(source) = &verification.source else {
        panic!("direct citation retains a Litex source")
    };
    assert_eq!(source.source_fact_id, Some(theorem.source_fact_id));
    assert!(matches!(
        source.mode,
        SuccessVerifyLitexTheoremApplicationMode::DirectFactCitation
    ));
    assert!(citation.statement.call.is_bare());
    assert!(citation.common.infers.is_empty());

    let lean = StmtResultToLeanCompiler::new("direct_atomic_theorem.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile ordinary theorem and exact direct citation");
    assert_eq!(lean.matches("theorem one_is_one :").count(), 1, "{lean}");
    assert!(!lean.contains("theorem __fact"), "{lean}");
}

#[test]
fn ordinary_compound_named_theorems_compile_with_their_typed_inferences() {
    let source = "thm conjunction:\n    ? 1 = 1 and 2 = 2\nrelease thm conjunction\n\nthm disjunction:\n    ? 1 = 1 or 2 = 3\nrelease thm disjunction\n\nthm relation_chain:\n    ? 1 <= 1 = 1\nrelease thm relation_chain\n";
    let results = crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        source,
        "direct_compound_theorems.lit",
    )
    .expect("execute compound ordinary theorem facts");
    let lean = StmtResultToLeanCompiler::new("direct_compound_theorems.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile compound ordinary theorem facts and typed inferences");

    assert!(lean.contains("theorem conjunction :"), "{lean}");
    assert!(lean.contains("theorem disjunction :"), "{lean}");
    assert!(lean.contains("theorem relation_chain :"), "{lean}");
    assert!(
        lean.contains("theorem __fact"),
        "conjunction-component inference should retain its exact FactId:\n{lean}"
    );
}

#[test]
fn direct_theorem_citation_rejects_parentheses_and_changed_application_mode() {
    let mut parenthesized = execute_named_atomic_theorem_and_direct_citation();
    let citation = direct_theorem_citation_result_mut(&mut parenthesized);
    citation.statement.call = TheoremCall::parenthesized(citation.statement.name().clone(), vec![]);
    let error = StmtResultToLeanCompiler::new("direct_atomic_theorem.lit")
        .compile_stmt_results_to_lean_source(&parenthesized)
        .expect_err("parenthesized ordinary theorem citation must fail closed");
    assert!(
        error.contains("direct theorem citation Result changed"),
        "{error}"
    );

    let mut changed_mode = execute_named_atomic_theorem_and_direct_citation();
    let citation = direct_theorem_citation_result_mut(&mut changed_mode);
    citation.statement.call = TheoremCall::parenthesized(citation.statement.name().clone(), vec![]);
    let verification = citation
        .verification
        .as_mut()
        .expect("direct citation retains verification");
    let SuccessVerifyTheoremApplicationSourceResult::Litex(source) = &mut verification.source
    else {
        panic!("direct citation retains a Litex source")
    };
    source.mode = SuccessVerifyLitexTheoremApplicationMode::ForallInstantiation {
        argument_verification: None,
        domain_facts: vec![],
        domain_checks: vec![],
    };
    let error = StmtResultToLeanCompiler::new("direct_atomic_theorem.lit")
        .compile_stmt_results_to_lean_source(&changed_mode)
        .expect_err("changed direct-citation application mode must fail closed");
    assert!(
        error.contains("source FactId does not identify a forall fact"),
        "{error}"
    );
}

#[test]
fn ordinary_named_theorem_rejects_a_changed_source_fact_id() {
    let mut results = execute_named_atomic_theorem_and_direct_citation();
    let theorem = match &mut results[0] {
        StmtResult::Success(SuccessStmtResult::Definition(
            SuccessDefinitionStmtResult::DefThmStmt(theorem),
        )) => theorem,
        _ => panic!("expected ordinary named theorem"),
    };
    theorem.source_fact_id = FactId::new(theorem.source_fact_id.value() + 1000);

    let error = StmtResultToLeanCompiler::new("direct_atomic_theorem.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("changed ordinary theorem source FactId must fail closed");
    assert!(
        error.contains("ordinary named theorem outer store changed its fact or exact FactId"),
        "{error}"
    );
}

#[test]
fn standard_set_binder_named_theorem_compiles_in_a_child_environment() {
    let mut results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "thm local_reflexivity:\n    ? forall x R:\n        x = x\n    x = x\n",
            "direct_binder_theorem.lit",
        )
        .expect("execute standard-set binder theorem");
    let theorem = named_theorem_result_mut(&mut results);
    let mut compiler = StmtResultToLeanCompiler::new("direct_binder_theorem.lit");

    assert!(compiler
        .compile_named_theorem_stmt_result_to_lean_source(theorem)
        .expect("direct binder theorem compilation succeeds"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    assert!(compiler.declarations[0].contains("∀ (x : (Litex.R).Carrier)"));
    assert!(compiler.declarations[0].contains(": Litex.In x Litex.R)"));
    assert!(compiler.declarations[0].contains("intro x __h"));
    assert!(compiler.declarations[0].contains("have __step"));
    assert!(compiler.declarations[0].contains("exact __c0_0"));
}

#[test]
fn existential_theorem_compiles_nested_witness_in_two_child_environments() {
    let mut results = crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "thm member_has_witness:\n    ? forall S set, a S:\n        exist x S st {x = a}\n    witness exist x S st {x = a} from a:\n        a = a\n",
            "direct_existential_theorem.lit",
        )
        .expect("execute theorem with a nested existential witness");
    let theorem = named_theorem_result_mut(&mut results);
    let mut compiler = StmtResultToLeanCompiler::new("direct_existential_theorem.lit");

    assert!(compiler
        .compile_named_theorem_stmt_result_to_lean_source(theorem)
        .expect("direct existential theorem compilation succeeds"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    assert_eq!(compiler.declarations.len(), 1);
    assert!(compiler.declarations[0].contains("∀ (S : Litex.Set)"));
    assert!(compiler.declarations[0].contains("{__carrier"));
    assert!(compiler.declarations[0].contains(": Type"));
    assert!(compiler.declarations[0].contains("(a : __carrier"));
    assert!(compiler.declarations[0].contains(": ∃ (__carrier_x : Type)"));
    assert!(compiler.declarations[0].contains(": Litex.Same a a := by"));
    assert!(
        compiler.declarations[0].contains("⟨_, a, (__h"),
        "{}",
        compiler.declarations[0]
    );
    assert!(compiler.declarations[0].contains(", (__step"));
    assert!(compiler.declarations[0].contains("exact __c0_0"));
}

fn execute_named_theorem_and_instantiation() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "thm local_reflexivity:\n    ? forall x R:\n        x = x\n    x = x\n\nrelease thm local_reflexivity(1)\n",
            "direct_theorem_instantiation.lit",
        )
        .expect("execute named theorem and its instantiation")
}

fn theorem_instantiation_result_mut(
    results: &mut [StmtResult],
) -> &mut SuccessReleaseThmStmtResult {
    let [_, StmtResult::Success(SuccessStmtResult::ReleaseThmStmt(result))] = results else {
        panic!("expected a named theorem followed by release-thm")
    };
    result
}

#[test]
fn release_thm_uses_the_exact_source_fact_id_and_argument_check_result() {
    let results = execute_named_theorem_and_instantiation();
    let StmtResult::Success(SuccessStmtResult::ReleaseThmStmt(release_theorem)) = &results[1]
    else {
        panic!("second Result is release-thm")
    };
    let source = &release_theorem
        .verification
        .as_ref()
        .expect("release-thm retains verification")
        .source;
    let SuccessVerifyTheoremApplicationSourceResult::Litex(source) = source else {
        panic!("release-thm retains a Litex theorem source")
    };
    let source_fact_id = source
        .source_fact_id
        .expect("release-thm retains its source theorem FactId");
    let json = crate::output::render_statement_result_json(&results[1]);
    assert!(json.contains(&format!("\"source_fact_id\": \"{source_fact_id}\"")));

    let lean = StmtResultToLeanCompiler::new("direct_theorem_instantiation.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile theorem and exact-FactId instantiation");

    assert!(lean.contains("theorem local_reflexivity :"));
    assert!(lean.contains("theorem __fact1 : Litex.Same (1 : ℂ) (1 : ℂ)"));
    assert!(lean.contains("local_reflexivity (1 : ℝ)"));
    assert!(lean.contains("Litex.In.own Litex.R (1 : ℝ)"));
    assert!(lean.contains("Litex.Same.realComplex ((1 : ℝ))"));
}

#[test]
fn release_thm_rejects_a_missing_source_theorem_fact_id() {
    let mut results = execute_named_theorem_and_instantiation();
    let verification = theorem_instantiation_result_mut(&mut results)
        .verification
        .as_mut()
        .expect("release-thm retains verification");
    let SuccessVerifyTheoremApplicationSourceResult::Litex(source) = &mut verification.source
    else {
        panic!("release-thm retains a Litex theorem source")
    };
    source.source_fact_id = None;

    let error = StmtResultToLeanCompiler::new("direct_theorem_instantiation.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("release-thm without its source FactId must fail closed");
    assert!(error.contains("release-thm Result has no source theorem FactId"));
}

#[test]
fn builtin_release_theorems_replay_typed_constructor_and_pointwise_results() {
    let source = "release thm set_builder_member(1, {x R: x > 0})\n\nrelease thm fn_set_member(fn(x R) R {x}, fn(y R) R)\n\nrelease thm cart_member_from_coordinates((1, 2), cart(R, R))\n\nrelease thm sum_le_sum_from_pointwise(sum(1, 2, fn(k Z) Z {k}), sum(1, 2, fn(k Z) Z {k}))\n";
    let results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            source,
            "builtin_theorem_applications.lit",
        )
        .expect("execute typed builtin theorem applications");
    let generated = StmtResultToLeanCompiler::new("builtin_theorem_applications.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile typed builtin theorem applications");

    assert!(
        generated.contains("Litex.Rules.inSetBuilder"),
        "{generated}"
    );
    assert!(
        generated.contains("Litex.In.own (Litex.fnSet"),
        "{generated}"
    );
    assert!(generated.contains("Litex.Rules.inCartCons"), "{generated}");
    assert!(
        generated.contains("Litex.Rules.integerRangeSumLeOwn"),
        "{generated}"
    );
    assert!(
        generated.contains("callOwn := fun (__arg : ℤ) => __arg"),
        "{generated}"
    );
    assert!(generated.contains("∀ (__p1 : ℤ)"), "{generated}");

    let sum_json = crate::output::render_statement_result_json(
        results.last().expect("sum theorem Result is retained"),
    );
    assert!(
        sum_json.contains("\"kind\": \"IntegerRangeSumPointwiseOrder\""),
        "{sum_json}"
    );
    assert!(sum_json.contains("\"expected_pointwise\""), "{sum_json}");
}

#[test]
fn integer_sum_builtin_release_fails_closed_outside_the_reviewed_z_to_z_contract() {
    let source = "release thm sum_le_sum_from_pointwise(sum(1, 2, fn(k Z) R {k}), sum(1, 2, fn(k Z) R {k}))\n";
    let results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            source,
            "builtin_sum_real_codomain_boundary.lit",
        )
        .expect("the runtime still verifies the broader source theorem");
    let error = StmtResultToLeanCompiler::new("builtin_sum_real_codomain_boundary.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("compiler must reject an unreviewed aggregate carrier");
    assert!(
        error.contains("outside the reviewed unary Z-to-Z integer-range contract"),
        "{error}"
    );
}

#[test]
fn typed_abs_min_max_rules_compile_through_reviewed_scalar_operator_abi() {
    let source = include_str!("../../../../lean/examples/63_ScalarOperatorBuiltins.lit");
    let results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            source,
            "scalar_operator_builtins.lit",
        )
        .expect("execute typed abs/min/max rules");
    let generated = StmtResultToLeanCompiler::new("scalar_operator_builtins.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile typed abs/min/max rules");

    for theorem in [
        "Litex.Rules.absMul",
        "Litex.Rules.absNonnegative",
        "Litex.Rules.absAddLe",
        "Litex.Rules.minMonotone",
        "Litex.Rules.maxMonotone",
        "Litex.Rules.minAssociative",
        "Litex.Rules.maxAbsorbMinLeft",
        "Litex.Rules.realCastLeAddOfNonnegativeRight",
        "Litex.Rules.realCastSubLeOfLeOfNonnegative",
    ] {
        assert!(
            generated.contains(theorem),
            "missing {theorem}:\n{generated}"
        );
    }
    assert!(generated.contains("Litex.abs"), "{generated}");
    assert!(generated.contains("Litex.min"), "{generated}");
    assert!(generated.contains("Litex.max"), "{generated}");
    assert!(
        generated.contains("Litex.Same.trans (Litex.Rules.minIdempotent"),
        "heterogeneous result must retain the exact source-to-selected bridge:\n{generated}"
    );
}

#[test]
fn closed_abs_min_max_normalization_uses_the_same_reviewed_object_abi() {
    let source = "abs(1) = 1\nmin(1, 2) = 1\nmax(1, 2) = 2\n";
    let results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            source,
            "closed_scalar_operator_normalization.lit",
        )
        .expect("execute closed scalar normalization");
    let generated = StmtResultToLeanCompiler::new("closed_scalar_operator_normalization.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile closed scalar normalization");
    assert!(
        generated.contains("norm_num [Litex.abs, Litex.min, Litex.max"),
        "{generated}"
    );
}

#[test]
fn abs_sign_selection_uses_exact_real_bindings_and_retained_premises() {
    let source = "forall x R:\n    0 <= x\n    =>:\n        abs(x) = x\n\nforall x R:\n    x <= 0\n    =>:\n        abs(x) = -x\n\nforall x R:\n    x != 0\n    =>:\n        0 < abs(x)\n";
    let results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            source,
            "abs_sign_selection_boundary.lit",
        )
        .expect("runtime verifies abs sign selection");
    let generated = StmtResultToLeanCompiler::new("abs_sign_selection_boundary.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile abs sign selection with exact real bindings");
    assert!(
        generated.contains("Litex.Rules.absEqSelfOfLe"),
        "{generated}"
    );
    assert!(
        generated.contains("Litex.Rules.absEqNegOfLe"),
        "{generated}"
    );
    assert!(
        generated.contains("Litex.Rules.absPositiveOfNotSame"),
        "{generated}"
    );
    assert!(!generated.contains("sorry"), "{generated}");
}

fn execute_named_theorem_and_selected_application() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "thm expose_zero_sides:\n    ? forall x C:\n        x + 0 = x\n        0 + x = x\n    x + 0 = x\n    0 + x = x\n\nby thm expose_zero_sides(2) => 2 + 0 = 0 + 2\n",
            "direct_by_theorem_selection.lit",
        )
        .expect("execute named theorem and selected theorem application")
}

fn selected_theorem_application_result_mut(
    results: &mut [StmtResult],
) -> &mut SuccessByThmStmtResult {
    let [_, StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByThmStmt(result)))] =
        results
    else {
        panic!("expected a named theorem followed by by-thm")
    };
    result
}

#[test]
fn by_thm_replays_temporary_conclusions_in_a_child_scope_and_publishes_only_selection() {
    let mut results = execute_named_theorem_and_selected_application();
    let [StmtResult::Success(SuccessStmtResult::Definition(
        SuccessDefinitionStmtResult::DefThmStmt(theorem),
    )), StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByThmStmt(selection)))] =
        results.as_mut_slice()
    else {
        panic!("expected theorem followed by selected theorem application")
    };
    let verification = selection
        .verification
        .as_ref()
        .expect("by-thm retains scoped verification");
    let StmtResult::Success(SuccessStmtResult::ReleaseThmStmt(application)) =
        verification.temporary_application.as_ref()
    else {
        panic!("by-thm retains a temporary release-thm Result")
    };
    let temporary_fact_ids = application
        .common
        .infers
        .store_fact_outputs
        .iter()
        .map(|output| output.fact_id.expect("temporary conclusion retains FactId"))
        .collect::<Vec<_>>();
    let selected_fact_id = selection.common.infers.store_fact_outputs[0]
        .fact_id
        .expect("selected parent fact retains FactId");

    let mut compiler = StmtResultToLeanCompiler::new("direct_by_theorem_selection.lit");
    assert!(compiler
        .compile_named_theorem_stmt_result_to_lean_source(theorem)
        .expect("compile source theorem"));
    assert!(compiler
        .compile_by_theorem_selection_stmt_result_to_lean_source(selection)
        .expect("compile selected theorem application"));

    assert_eq!(compiler.environment_stack.environments.len(), 1);
    for fact_id in temporary_fact_ids {
        assert!(
            !compiler.environment_stack.fact_names.contains_key(&fact_id),
            "temporary theorem conclusion escaped its compiler child scope"
        );
    }
    assert_eq!(
        compiler.environment_stack.fact_names.get(&selected_fact_id),
        Some(&"__fact1".to_string())
    );
    assert!(compiler.declarations[0].contains("(Litex.C).Carrier"));
    assert!(!compiler.declarations[0].contains("Litex.In.rep x"));
    assert_eq!(
        compiler.declarations[1]
            .matches("have __projected_conclusion")
            .count(),
        2
    );
    assert!(compiler.declarations[1].contains(".1"));
    assert!(compiler.declarations[1].contains(".2"));
    assert!(
        compiler.declarations[1].contains("try rw [Litex.In.rep_exact]"),
        "exact-carrier theorem arguments must unwrap their projected representatives"
    );
    assert!(compiler.declarations[1].contains("Litex.Same.trans"));

    let json = crate::output::render_statement_result_json(&results[1]);
    assert!(json.contains("\"temporary_application\""), "{json}");
    assert!(json.contains("\"selected_fact_check\""), "{json}");
}

#[test]
fn by_thm_rejects_a_temporary_conclusion_without_its_local_fact_id() {
    let mut results = execute_named_theorem_and_selected_application();
    let selection = selected_theorem_application_result_mut(&mut results);
    let StmtResult::Success(SuccessStmtResult::ReleaseThmStmt(application)) = selection
        .verification
        .as_mut()
        .expect("by-thm retains scoped verification")
        .temporary_application
        .as_mut()
    else {
        panic!("by-thm retains a temporary release-thm Result")
    };
    application.common.infers.store_fact_outputs[0].fact_id = None;

    let error = StmtResultToLeanCompiler::new("direct_by_theorem_selection.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("missing temporary conclusion identity must fail closed");
    assert!(
        error.contains("local release-thm conclusion") && error.contains("has no retained FactId"),
        "{error}"
    );
}

#[test]
fn by_thm_rejects_a_temporary_application_with_changed_arguments() {
    let mut results = execute_named_theorem_and_selected_application();
    let selection = selected_theorem_application_result_mut(&mut results);
    let StmtResult::Success(SuccessStmtResult::ReleaseThmStmt(application)) = selection
        .verification
        .as_mut()
        .expect("by-thm retains scoped verification")
        .temporary_application
        .as_mut()
    else {
        panic!("by-thm retains a temporary release-thm Result")
    };
    application
        .statement
        .parenthesized_args_mut()
        .expect("corrupted forall application retains parentheses")
        .clear();

    let error = StmtResultToLeanCompiler::new("direct_by_theorem_selection.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("changed temporary theorem arguments must fail closed");
    assert!(
        error.contains("by-thm temporary application changed its theorem or arguments"),
        "{error}"
    );
}

#[test]
fn theorem_backed_obtain_consumes_but_does_not_publish_its_local_conclusion() {
    let results = crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "thm self_exists:\n    ? forall a R:\n        exist x R st {x = a}\n    witness exist x R st {x = a} from a:\n        a = a\nobtain selected from thm self_exists(3)\n",
            "direct_theorem_backed_obtain.lit",
        )
        .expect("execute theorem-backed obtain");
    let [StmtResult::Success(SuccessStmtResult::Definition(
        SuccessDefinitionStmtResult::DefThmStmt(theorem),
    )), StmtResult::Success(SuccessStmtResult::Definition(
        SuccessDefinitionStmtResult::ObtainObjFromThm(obtain),
    ))] = results.as_slice()
    else {
        panic!("expected theorem followed by theorem-backed obtain")
    };
    let source = obtain
        .verification
        .as_ref()
        .expect("obtain retains elimination verification")
        .source_result
        .theorem_application()
        .and_then(StmtResult::non_factual_success)
        .expect("obtain source is a statement Result");
    let SuccessStmtResult::ReleaseThmStmt(application) = source else {
        panic!("obtain source is a release-thm Result")
    };
    assert_eq!(
        application.common.infers.store_fact_outputs[0].fact_id, None,
        "the temporary theorem conclusion is not publishable after its local environment pops"
    );
    let theorem_fact_id = theorem.common.infers.store_fact_outputs[0]
        .fact_id
        .expect("named theorem retains its published FactId");
    let projection_fact_ids = obtain
        .common
        .infers
        .store_fact_outputs
        .iter()
        .map(|output| output.fact_id.expect("projection retains FactId"))
        .collect::<Vec<_>>();

    let mut compiler = StmtResultToLeanCompiler::new("direct_theorem_backed_obtain.lit");
    assert!(compiler
        .compile_named_theorem_stmt_result_to_lean_source(theorem)
        .expect("compile source theorem"));
    assert!(compiler
        .compile_obtain_obj_from_theorem_stmt_result_to_lean_source(obtain)
        .expect("compile theorem-backed obtain"));
    assert_eq!(compiler.environment_stack.fact_names.len(), 3);
    assert!(compiler
        .environment_stack
        .fact_names
        .contains_key(&theorem_fact_id));
    for fact_id in projection_fact_ids {
        assert!(compiler.environment_stack.fact_names.contains_key(&fact_id));
    }
    assert_eq!(compiler.declarations.len(), 4);
    assert!(compiler.declarations[1].contains("noncomputable def selected"));
}

fn execute_odd_sum_to_square_flagship() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        include_str!("../../../../showcases/Litex_to_Lean_Mathlib_Pipeline/main.lit"),
        "main.lit",
    )
    .expect("execute the odd-sum flagship")
}

#[test]
fn odd_sum_flagship_exports_only_source_owned_declarations() {
    let litex_source =
        include_str!("../../../../showcases/Litex_to_Lean_Mathlib_Pipeline/main.lit");
    assert!(litex_source.contains("have fn kth_odd"));
    assert!(!litex_source.contains("thm odd_sum_single"));
    assert!(!litex_source.contains("thm odd_sum_step"));
    assert!(!litex_source.contains("thm odd_square_step"));
    assert!(!litex_source.contains("by thm"));
    assert_eq!(litex_source.matches("\nforall n Z:").count(), 2);
    assert_eq!(litex_source.matches("\nthm ").count(), 1);
    assert!(litex_source.contains("kth_odd(1) = 2 * 1 - 1 = 1"));
    assert!(litex_source.contains("n^2 + kth_odd(n + 1) = n^2 + (2 * (n + 1) - 1) = (n + 1)^2"));
    assert!(!litex_source.contains("thm odd_sum_integer"));
    assert!(!litex_source.contains("thm square_integer"));
    assert!(!litex_source.contains("thm sum_first_ten_odds"));

    let results = execute_odd_sum_to_square_flagship();
    let result_audit = results
        .iter()
        .map(crate::output::render_statement_result_json)
        .collect::<Vec<_>>()
        .join("\n");
    let lean = StmtResultToLeanCompiler::new("main.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile the complete odd-sum Result DAG");
    let checked_in =
        include_str!("../../../../showcases/Litex_to_Lean_Mathlib_Pipeline/Generated.lean");

    assert_eq!(lean, checked_in);
    assert!(lean.contains("theorem sum_first_odds :"));
    assert!(!lean.contains("theorem odd_sum_integer :"));
    assert!(!lean.contains("theorem square_integer :"));
    assert!(!lean.contains("theorem sum_first_ten_odds :"));
    assert!(lean.contains("Litex.sum (1 : ℤ) n kth_odd"));
    assert!(!lean.contains("private theorem __native_certificate"));
    assert!(!lean.contains("namespace Native"));
    assert!(!lean.contains("namespace MathlibConsumer"));
    assert!(!lean.contains("Finset.Icc"));
    assert!(lean.contains("Litex.Same.intCastAddComplex"));
    assert!(lean.contains("unfold Litex.fnApplyCarrier kth_odd"));
    assert!(!lean.contains("unfold Litex.fnApplyOwn kth_odd"));
    assert!(result_audit.contains("StructuralKnownEqualityCongruence"));
    assert!(result_audit.contains("CheckedFunctionDefinitionReduction"));
    assert!(result_audit.contains("IntegralPolynomialNormalization"));
    assert!(result_audit.contains("IntegerRangeSumMembership"));
    assert!(result_audit.contains("\"rule_id\": \"aggregate.sum_single\""));
    assert!(result_audit.contains("\"rule_id\": \"aggregate.sum_split_last\""));
    assert!(result_audit.contains("PowNat"));
    assert!(result_audit.contains("\"kind\": \"Iteration\""));
    assert!(!result_audit.contains("\"argument\": \"10\""));
    assert!(!lean.contains("SumExpr"));
    assert!(!lean.contains("theorem odd_sum_step"));
    assert!(!lean.contains("theorem odd_square_step"));
    assert!(!lean.contains("LitexObject"));
    assert!(!lean.contains("sorry"));
}

#[test]
fn odd_sum_canonical_translation_rejects_changed_proof_step_order() {
    let mut results = execute_odd_sum_to_square_flagship();
    let theorem = results
        .iter_mut()
        .find_map(|result| {
            let StmtResult::Success(SuccessStmtResult::Definition(
                SuccessDefinitionStmtResult::DefThmStmt(theorem),
            )) = result
            else {
                return None;
            };
            match theorem.verification.as_ref() {
                Some(verification) if verification.name == "sum_first_odds" => {
                    Some(theorem.as_mut())
                }
                _ => None,
            }
        })
        .expect("flagship retains the induction theorem");
    theorem
        .verification
        .as_mut()
        .expect("flagship theorem retains verification")
        .proof_steps
        .clear();

    let error = StmtResultToLeanCompiler::new("main.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("canonical translation cannot survive a changed verified proof-step order");
    assert!(error.contains("proof-step order"), "{error}");
}
