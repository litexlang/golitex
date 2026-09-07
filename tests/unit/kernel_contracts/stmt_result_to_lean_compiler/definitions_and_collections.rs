use super::super::*;

fn execute_concrete_predicate_and_by_definition() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        "prop is_unit_pair(x R, y R):\n    x = 1\n    y = 1\n\n1 = 1\nby def $is_unit_pair(1, 1)\n",
        "direct_by_definition.lit",
    )
    .expect("execute concrete predicate and by-definition")
}

#[test]
fn unique_existence_choice_function_compiles_from_retained_witness_and_uniqueness_results() {
    let source = r#"have fn successor_from_unique_output by exist!:
    ? forall x N:
        exist! y N st {y = x + 1}
    witness exist! y N st {y = x + 1} from x + 1:
        claim:
            ? forall y1, y2 N:
                y1 = x + 1
                y2 = x + 1
                =>:
                    y1 = y2
            y1 = x + 1 = y2

forall x N:
    successor_from_unique_output(x) = x + 1
"#;
    let results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            source,
            "have_fn_by_exist_unique.lit",
        )
        .expect("execute unique-existence function fixture");
    let StmtResult::Success(SuccessStmtResult::Definition(
        SuccessDefinitionStmtResult::HaveFnByForallExistUniqueStmt(definition),
    )) = &results[0]
    else {
        panic!("first Result must be the unique-existence function definition")
    };
    let verification = definition
        .verification
        .as_ref()
        .expect("verified choice function retains its proof Result");
    assert!(!verification.proof_scope.assumption_infers.is_empty());
    assert!(definition.published_property_well_definedness.is_some());

    let generated = StmtResultToLeanCompiler::new("have_fn_by_exist_unique.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile unique-existence choice and its reusable property");
    assert!(
        generated.contains("Classical.choose (successor_from_unique_output__exists"),
        "{generated}"
    );
    assert!(generated.contains("have __witness_unique"), "{generated}");
    assert!(generated.contains("theorem __fact2"), "{generated}");
    for forbidden in ["axiom ", "sorry", "admit", "by_contra hmagic"] {
        assert!(!generated.contains(forbidden), "{generated}");
    }
}

fn by_definition_result_mut(results: &mut [StmtResult]) -> &mut SuccessByDefStmtResult {
    let [_, _, StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByDefStmt(result)))] =
        results
    else {
        panic!("expected concrete predicate, fact, and by-definition Results")
    };
    result
}

#[test]
fn by_definition_combines_parameter_and_clause_results_directly() {
    let results = execute_concrete_predicate_and_by_definition();
    let mut compiler = StmtResultToLeanCompiler::new("direct_by_definition.lit");
    let StmtResult::Success(SuccessStmtResult::Definition(
        SuccessDefinitionStmtResult::DefPropStmt(definition),
    )) = &results[0]
    else {
        panic!("first Result is a concrete predicate definition")
    };
    let StmtResult::Success(SuccessStmtResult::Fact(fact)) = &results[1] else {
        panic!("second Result is the reusable clause fact")
    };
    let StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByDefStmt(by_definition))) =
        &results[2]
    else {
        panic!("third Result is by-definition")
    };

    compiler
        .compile_def_prop_stmt_result_to_lean_source(definition)
        .expect("compile concrete predicate directly");
    compiler
        .compile_fact_stmt_result_to_lean_source(fact)
        .expect("compile reusable clause fact directly");
    assert!(compiler
        .compile_by_definition_stmt_result_to_lean_source(by_definition)
        .expect("compile by-definition directly"));
    assert!(compiler.declarations[2].contains("unfold is_unit_pair"));
    assert!(compiler.declarations[2].contains("Litex.In.own Litex.R (1 : ℝ)"));
    assert!(compiler.declarations[2].contains("Litex.Same.realComplex ((1 : ℝ))"));
    assert!(compiler.declarations[2].contains("__fact0"));
}

#[test]
fn by_definition_rejects_a_missing_clause_child_result() {
    let mut results = execute_concrete_predicate_and_by_definition();
    by_definition_result_mut(&mut results)
        .verification
        .as_mut()
        .expect("by-definition retains verification")
        .clause_checks
        .pop();

    let error = StmtResultToLeanCompiler::new("direct_by_definition.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("missing clause child must fail closed");
    assert!(error.contains("changed its component arity"));
}

#[test]
fn by_definition_rejects_a_missing_target_fact_id() {
    let mut results = execute_concrete_predicate_and_by_definition();
    by_definition_result_mut(&mut results)
        .common
        .infers
        .store_fact_outputs[0]
        .fact_id = None;

    let error = StmtResultToLeanCompiler::new("direct_by_definition.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("by-definition target without FactId must fail closed");
    assert!(error.contains("by-definition target store has no FactId"));
}

#[test]
fn by_definition_preserves_an_ordinary_forall_implicit_host_carrier() {
    let source = r#"prop nested_natural_reflexivity(anchor R):
    forall n N:
        n = n

by def $nested_natural_reflexivity(0)
"#;
    let results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            source,
            "direct_by_definition_implicit_host_carrier.lit",
        )
        .expect("execute concrete predicate with an ordinary nested forall");
    let generated = StmtResultToLeanCompiler::new("direct_by_definition_implicit_host_carrier.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile nested ordinary forall through by-definition");

    assert!(
        generated.contains("∀ {__carrier1 : Type} (__p1 : __carrier1)"),
        "{generated}"
    );
    assert!(generated.contains("exact @__fact0"), "{generated}");
}

#[test]
fn concrete_sequence_predicate_retains_and_consumes_local_wd_evidence() {
    let source = r#"prop is_sequence_tail_close_to_limit(a seq(R), L R, epsilon R+, n0 N+):
    forall n N+:
        n >= n0
        =>:
            abs(a(n) - L) < epsilon
"#;
    let results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            source,
            "real_sequence_definition_result_contract.lit",
        )
        .expect("execute checked real-sequence definition");
    let [StmtResult::Success(SuccessStmtResult::Definition(
        SuccessDefinitionStmtResult::DefPropStmt(result),
    ))] = results.as_slice()
    else {
        panic!("expected one concrete predicate Result")
    };
    let local = result
        .run_in_local_env
        .as_ref()
        .expect("verified concrete predicate retains its local WD flow");
    assert_eq!(local.binder.parameter_groups.len(), 4);
    assert_eq!(local.body.len(), 1);
    assert!(local.body[0].store.fact_id.is_some());
    let lean = StmtResultToLeanCompiler::new("real_sequence_definition_result_contract.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile from retained sequence-definition evidence");
    assert!(
        lean.contains("∃ (__arg_type1 : Litex.In a (Litex.sequenceSet Litex.R))"),
        "{lean}"
    );
    assert!(lean.contains("Litex.fnApplyOwn"), "{lean}");
    assert!(!lean.contains("RealSequenceTailClose"), "{lean}");
    assert!(!lean.contains("axiom is_sequence_tail_close_to_limit"));
}

#[test]
fn concrete_predicate_reuses_the_exact_sequence_parameter_representative() {
    let source = r#"prop is_tail_epsilon_steady(a seq(R), epsilon R+, n0 N+):
    forall j, k N+:
        j >= n0
        k >= n0
        =>:
            abs(a(j) - a(k)) < epsilon

prop is_tail_lower_bound(a seq(R), n0 N+, B R):
    forall n N+:
        n >= n0
        =>:
            B <= a(n)

prop has_eventual_lower_bound(a seq(R), B R):
    exist n0 N+ st {$is_tail_lower_bound(a, n0, B)}

thm tail_stability_gives_eventual_lower_bound:
    ? forall a seq(R), n0 N+:
        $is_tail_epsilon_steady(a, 1, n0)
        =>:
            $has_eventual_lower_bound(a, a(n0) - 1)
    forall n N+:
        n >= n0
        =>:
            abs(a(n0) - a(n)) < 1
            a(n0) - a(n) <= abs(a(n0) - a(n)) < 1
            a(n0) - 1 < a(n0) - (a(n0) - a(n)) = a(n)
            a(n0) - 1 <= a(n)
    by def:
        ? $is_tail_lower_bound(a, n0, a(n0) - 1)
    witness $has_eventual_lower_bound(a, a(n0) - 1) from n0
"#;
    let results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            source,
            "eventual_lower_bound_transport.lit",
        )
        .expect("execute concrete predicate with an exact sequence argument");
    let generated = StmtResultToLeanCompiler::new("eventual_lower_bound_transport.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile exact sequence argument through a predicate existential");

    assert!(
        generated.contains("Litex.fnApplyOwn (domain := Litex.NPos) (codomain := Litex.R) a")
            && !generated.contains("Litex.In.rep a"),
        "{generated}"
    );
    for forbidden in ["LitexObject", "Litex.Object", "sorry", "axiom "] {
        assert!(
            !generated.contains(forbidden),
            "forbidden `{forbidden}` in:\n{generated}"
        );
    }
}

#[test]
fn concrete_sequence_predicate_rejects_missing_body_wd_evidence() {
    let source = r#"prop is_sequence_tail_close_to_limit(a seq(R), L R, epsilon R+, n0 N+):
    forall n N+:
        n >= n0
        =>:
            abs(a(n) - L) < epsilon
"#;
    let mut results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            source,
            "real_sequence_definition_missing_wd.lit",
        )
        .expect("execute checked real-sequence definition");
    let [StmtResult::Success(SuccessStmtResult::Definition(
        SuccessDefinitionStmtResult::DefPropStmt(result),
    ))] = results.as_mut_slice()
    else {
        panic!("expected one concrete predicate Result")
    };
    result
        .run_in_local_env
        .as_mut()
        .expect("verified definition retains local evidence")
        .body
        .clear();
    let error = StmtResultToLeanCompiler::new("real_sequence_definition_missing_wd.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("missing definition-body evidence must fail closed");
    assert!(
        error.contains("changed its binder or body arity"),
        "{error}"
    );
}

fn execute_named_real_function(source: &str) -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        source,
        "direct_named_real_function.lit",
    )
    .expect("execute named real function")
}

fn named_real_function_result_mut(results: &mut [StmtResult]) -> &mut SuccessHaveFnEqualStmtResult {
    let [StmtResult::Success(SuccessStmtResult::Definition(
        SuccessDefinitionStmtResult::HaveFnEqualStmt(result),
    ))] = results
    else {
        panic!("expected one named-function Result")
    };
    result
}

#[test]
fn named_real_function_compiles_return_check_in_child_environment() {
    let mut results = execute_named_real_function("have fn inc(x R) R = x + 1\n");
    let result = named_real_function_result_mut(&mut results);
    let defining_equality_fact_id = result.common.infers.store_fact_outputs[1]
        .fact_id
        .expect("defining equality retains FactId");
    let mut compiler = StmtResultToLeanCompiler::new("direct_named_real_function.lit");

    assert!(compiler
        .compile_have_fn_equal_stmt_result_to_lean_source(result)
        .expect("compile named real function directly"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    assert_eq!(compiler.declarations.len(), 3);
    assert!(compiler.declarations[0].contains("noncomputable def inc : Litex.Fn"));
    assert!(compiler.declarations[0].contains("Litex.In.rep __arg __arg_in + (1 : ℝ)"));
    let binding = compiler
        .environment_stack
        .named_function_definitions
        .get(&defining_equality_fact_id)
        .expect("direct function publishes its reduction binding");
    assert_eq!(binding.native_body_carrier, NativeFunctionBodyCarrier::Real);
}

#[test]
fn checked_named_function_reduction_uses_its_exact_definition_fact_id() {
    let results = execute_named_real_function("have fn inc(x R) R = x + 1\ninc(2) = 2 + 1\n");
    let reduction_result = results[1]
        .factual_success()
        .expect("second statement is a factual reduction");
    let SuccessFactProofResult::CheckedFunctionDefinitionReduction(reduction) = reduction_result
        .proof()
        .expect("verified reduction statement owns a proof")
    else {
        panic!("checked definition reduction must retain typed evidence")
    };
    let StmtResult::Success(SuccessStmtResult::Definition(
        SuccessDefinitionStmtResult::HaveFnEqualStmt(definition),
    )) = &results[0]
    else {
        panic!("first statement is the named-function definition")
    };
    assert_eq!(
        Some(reduction.verification.defining_equality_fact_id),
        definition.common.infers.store_fact_outputs[1].fact_id
    );

    let lean = StmtResultToLeanCompiler::new("direct_named_real_function.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile checked function reduction directly");
    assert!(lean.contains("unfold Litex.fnApplyCarrier inc"));
}

#[test]
fn checked_named_function_reduction_compiles_its_reduced_equality_child() {
    let results =
        execute_named_real_function("have fn sixth(t R) R = t / 3\nsixth(1 / 2) = 1 / 6\n");
    let reduction_result = results[1]
        .factual_success()
        .expect("second statement is a factual reduction");
    let SuccessFactProofResult::CheckedFunctionDefinitionReduction(reduction) = reduction_result
        .proof()
        .expect("verified reduction statement owns a proof")
    else {
        panic!("checked definition reduction must retain typed evidence")
    };
    let reduced = reduction
        .verification
        .reduced_equality
        .verified()
        .expect("checked reduction owns a successful reduced-equality Result");
    assert_eq!(reduced.fact().to_string(), "1 / 2 / 3 = 1 / 6");

    let lean = StmtResultToLeanCompiler::new("checked_bayes_reduction.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile the checked unfolding and its retained rational child");
    assert!(lean.contains("unfold Litex.fnApplyCarrier sixth"));
    assert!(lean.contains("Litex.Same.trans"));
    assert!(lean.contains("field_simp"));
}

#[test]
fn checked_named_function_reduction_rejects_a_wrong_definition_fact_id() {
    let mut results = execute_named_real_function("have fn inc(x R) R = x + 1\ninc(2) = 2 + 1\n");
    let StmtResult::Success(SuccessStmtResult::Fact(reduction_result)) = &mut results[1] else {
        panic!("second statement is a factual reduction")
    };
    let wrong_fact_id = reduction_result
        .store
        .fact_id
        .expect("outer reduction result retains a FactId");
    let verification = reduction_result
        .verification_mut()
        .expect("executed Result uniquely owns its verification in this corruption test");
    let SuccessFactProofResult::CheckedFunctionDefinitionReduction(reduction) =
        verification.proof_mut()
    else {
        panic!("checked definition reduction must retain typed evidence")
    };
    reduction.verification.defining_equality_fact_id = wrong_fact_id;

    let error = StmtResultToLeanCompiler::new("direct_named_real_function.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("wrong defining FactId must fail closed");
    assert!(error.contains("unavailable cited fact"), "{error}");
}

#[test]
fn checked_named_function_reduction_inside_forall_uses_wd_scope_fact_ids() {
    let results = execute_named_real_function(
            "have fn reciprocal(x R: x != 0) R = 1 / x\nforall a R:\n    a != 0\n    =>:\n        reciprocal(a) = 1 / a\n",
        );
    let [StmtResult::Success(SuccessStmtResult::Definition(
        SuccessDefinitionStmtResult::HaveFnEqualStmt(definition),
    )), StmtResult::Success(SuccessStmtResult::Fact(forall_result))] = results.as_slice()
    else {
        panic!("expected a function definition and one forall Result")
    };
    let mut compiler = StmtResultToLeanCompiler::new("direct_named_real_function.lit");
    assert!(compiler
        .compile_have_fn_equal_stmt_result_to_lean_source(definition)
        .expect("compile domain-constrained function definition directly"));
    assert!(compiler
        .compile_direct_forall_fact_result(forall_result)
        .expect("compile checked reduction under the forall Result environment"));
    assert!(
        compiler.declarations.last().is_some_and(|declaration| {
            declaration.contains("unfold Litex.fnApplyWhereOwn reciprocal")
                && declaration.contains("__domain1")
                && declaration.contains("Litex.Same.refl")
                // R/C forall binders use the native complex host carrier; the
                // checked WD fact remains the scope evidence we care about.
                && declaration.contains("∀ (__p1 : ℂ)")
        }),
        "generated declarations: {:?}",
        compiler.declarations
    );
}

#[test]
fn named_real_function_domain_fact_stays_inside_function_binder() {
    let mut results = execute_named_real_function("have fn reciprocal(x R: x != 0) R = 1 / x\n");
    let result = named_real_function_result_mut(&mut results);
    let mut compiler = StmtResultToLeanCompiler::new("direct_named_real_function.lit");

    assert!(compiler
        .compile_have_fn_equal_stmt_result_to_lean_source(result)
        .expect("compile domain-constrained real function directly"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    assert!(compiler.declarations[0].contains("Litex.FnWhere"));
    assert!(compiler.declarations[0].contains("__arg_domain"));
    assert!(compiler
        .environment_stack
        .fact_propositions
        .values()
        .all(|fact| fact.to_string() != "x != 0"));
}

#[test]
fn named_real_function_rejects_missing_local_parameter_fact_id() {
    let mut results = execute_named_real_function("have fn inc(x R) R = x + 1\n");
    named_real_function_result_mut(&mut results)
        .verification
        .as_mut()
        .expect("function retains verification")
        .assumption_infers
        .store_fact_outputs[0]
        .fact_id = None;

    let error = StmtResultToLeanCompiler::new("direct_named_real_function.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("missing local parameter FactId must fail closed");
    assert!(error.contains("named real function local assumptions store 0"));
    assert!(error.contains("has no FactId"));
}

fn execute_indexed_tuple_definition() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        "have tuple coordinates for index <= 3, coordinates[index] = index + 1\n",
        "direct_indexed_tuple.lit",
    )
    .expect("execute indexed tuple definition")
}

fn indexed_tuple_result_mut(results: &mut [StmtResult]) -> &mut SuccessHaveTupleStmtResult {
    let [StmtResult::Success(SuccessStmtResult::Definition(
        SuccessDefinitionStmtResult::HaveTupleStmt(result),
    ))] = results
    else {
        panic!("expected one indexed tuple Result")
    };
    result
}

#[test]
fn indexed_tuple_compiles_value_well_definedness_in_child_environment() {
    let mut results = execute_indexed_tuple_definition();
    let result = indexed_tuple_result_mut(&mut results);
    let verification = result
        .verification
        .as_ref()
        .expect("indexed tuple retains combined verification");
    match verification.value_well_definedness.as_ref() {
        SuccessVerifyObjWellDefinedResult::Direct(value) => {
            assert_eq!(
                obj_equality_key(&value.object),
                obj_equality_key(&result.statement.value)
            );
        }
        other => panic!("expected direct tuple value WD Result, found {other:?}"),
    }
    let mut compiler = StmtResultToLeanCompiler::new("direct_indexed_tuple.lit");

    assert!(compiler
        .compile_have_tuple_stmt_result_to_lean_source(result)
        .expect("compile indexed tuple directly"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    assert_eq!(compiler.declarations.len(), 6);
    assert!(
        compiler.declarations[2].contains("noncomputable def coordinates : Litex.IndexedTuple 3 ℂ")
    );
    assert!(compiler.declarations[2].contains("__index.val"));
    assert!(compiler.declarations[2].contains("+ (1 : ℂ)"));
    assert!(compiler.declarations[5].contains("∀ {__tuple_index_carrier : Type}"));
    assert!(!compiler
        .environment_stack
        .symbol_names
        .contains_key(&result.statement.index_binding.id()));
}

#[test]
fn indexed_tuple_rejects_a_coordinate_store_without_fact_id() {
    let mut results = execute_indexed_tuple_definition();
    indexed_tuple_result_mut(&mut results)
        .common
        .infers
        .store_fact_outputs[2]
        .fact_id = None;

    let error = StmtResultToLeanCompiler::new("direct_indexed_tuple.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("coordinate store without a FactId must fail closed");
    assert!(error.contains("lost its FactId"));
}

fn execute_indexed_sequence_definition() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        "have seq identity_sequence seq(R) for index, identity_sequence(index) = index + 1\n",
        "direct_indexed_sequence.lit",
    )
    .expect("execute indexed sequence definition")
}

fn indexed_sequence_result_mut(results: &mut [StmtResult]) -> &mut SuccessHaveSeqStmtResult {
    let [StmtResult::Success(SuccessStmtResult::Definition(
        SuccessDefinitionStmtResult::HaveSeqStmt(result),
    ))] = results
    else {
        panic!("expected one indexed sequence Result")
    };
    result
}

#[test]
fn indexed_sequence_compiles_return_check_in_its_index_environment() {
    let mut results = execute_indexed_sequence_definition();
    let result = indexed_sequence_result_mut(&mut results);
    let verification = result
        .verification
        .as_ref()
        .expect("sequence retains combined verification");
    let parameter_fact_id = verification.assumption_infers.store_fact_outputs[0]
        .fact_id
        .expect("sequence index membership retains its local FactId");
    let defining_equality_fact_id = result.common.infers.store_fact_outputs[1]
        .fact_id
        .expect("sequence equality retains its outer FactId");
    let mut compiler = StmtResultToLeanCompiler::new("direct_indexed_sequence.lit");

    assert!(compiler
        .compile_have_sequence_stmt_result_to_lean_source(result)
        .expect("compile indexed sequence directly"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    assert_eq!(compiler.declarations.len(), 4);
    assert!(compiler.declarations[0]
        .contains("noncomputable def identity_sequence : Litex.Fn Litex.NPos Litex.R"));
    assert!(compiler.declarations[0].contains("(Litex.In.rep __arg __arg_in).val : ℕ"));
    assert!(compiler.declarations[0].contains("+ (1 : ℝ)"));
    assert!(compiler.declarations[1].contains("Litex.sequenceSet Litex.R"));
    assert!(compiler.declarations[2].contains("Litex.fnSet Litex.NPos Litex.R"));
    assert!(!compiler
        .environment_stack
        .symbol_names
        .contains_key(&result.statement.index_binding.id()));
    assert!(!compiler
        .environment_stack
        .fact_names
        .contains_key(&parameter_fact_id));
    assert!(compiler
        .environment_stack
        .named_function_definitions
        .contains_key(&defining_equality_fact_id));
}

#[test]
fn indexed_sequence_rejects_a_missing_local_parameter_fact_id() {
    let mut results = execute_indexed_sequence_definition();
    indexed_sequence_result_mut(&mut results)
        .verification
        .as_mut()
        .expect("sequence retains verification")
        .assumption_infers
        .store_fact_outputs[0]
        .fact_id = None;

    let error = StmtResultToLeanCompiler::new("direct_indexed_sequence.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("sequence index without a local FactId must fail closed");
    assert!(error.contains("sequence index parameter store has no FactId"));
}

fn execute_finite_sequence_definition() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "have finite_seq bounded_sequence finite_seq(R, 3) for index <= 3, bounded_sequence(index) = index + 1\nbounded_sequence(2) = 2 + 1\n",
            "direct_finite_sequence.lit",
        )
        .expect("execute finite-sequence definition and application")
}

fn finite_sequence_result_mut(results: &mut [StmtResult]) -> &mut SuccessHaveFiniteSeqStmtResult {
    let [StmtResult::Success(SuccessStmtResult::Definition(
        SuccessDefinitionStmtResult::HaveFiniteSeqStmt(result),
    )), _] = results
    else {
        panic!("expected a finite-sequence definition followed by an application fact")
    };
    result
}

#[test]
fn finite_sequence_compiles_bound_scope_and_application_from_recursive_results() {
    let mut results = execute_finite_sequence_definition();
    let result = finite_sequence_result_mut(&mut results);
    let verification = result
        .verification
        .as_ref()
        .expect("finite sequence retains combined verification");
    assert_eq!(verification.bound_checks.len(), 2);
    assert_eq!(verification.assumption_infers.store_fact_outputs.len(), 2);
    let parameter_fact_id = verification.assumption_infers.store_fact_outputs[0]
        .fact_id
        .expect("finite-sequence parameter membership retains its local FactId");
    let domain_fact_id = verification.assumption_infers.store_fact_outputs[1]
        .fact_id
        .expect("finite-sequence domain premise retains its local FactId");
    let defining_equality_fact_id = result.common.infers.store_fact_outputs[1]
        .fact_id
        .expect("finite-sequence equality retains its outer FactId");
    let mut compiler = StmtResultToLeanCompiler::new("direct_finite_sequence.lit");

    assert!(compiler
        .compile_have_finite_sequence_stmt_result_to_lean_source(result)
        .expect("compile finite sequence directly"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    assert_eq!(compiler.declarations.len(), 4);
    assert!(compiler.declarations[0]
        .contains("noncomputable def bounded_sequence : Litex.FnTelescope.Carrier"));
    assert!(compiler.declarations[0].contains("Litex.FnTelescope.requirement"));
    assert!(compiler.declarations[0].contains("fun __arg_domain => ULift.up"));
    assert!(compiler.declarations[1].contains("Litex.finiteSequenceSet.{0} Litex.R (3 : Nat)"));
    assert!(compiler.declarations[2].contains("Litex.fnTelescopeSet"));
    assert!(!compiler
        .environment_stack
        .symbol_names
        .contains_key(&result.statement.index_binding.id()));
    assert!(!compiler
        .environment_stack
        .fact_names
        .contains_key(&parameter_fact_id));
    assert!(!compiler
        .environment_stack
        .fact_names
        .contains_key(&domain_fact_id));
    assert!(compiler
        .environment_stack
        .named_function_definitions
        .contains_key(&defining_equality_fact_id));
}

#[test]
fn finite_sequence_rejects_a_missing_local_domain_fact_id() {
    let mut results = execute_finite_sequence_definition();
    finite_sequence_result_mut(&mut results)
        .verification
        .as_mut()
        .expect("finite sequence retains verification")
        .assumption_infers
        .store_fact_outputs[1]
        .fact_id = None;

    let error = StmtResultToLeanCompiler::new("direct_finite_sequence.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("finite-sequence domain without a local FactId must fail closed");
    assert!(error.contains("finite-sequence domain store has no FactId"));
}

fn execute_matrix_definition() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "have matrix entry_matrix matrix(R, 2, 3) for row <= 2, column <= 3, entry_matrix(row, column) = row + column\nentry_matrix(2, 3) = 2 + 3\n",
            "direct_matrix.lit",
        )
        .expect("execute matrix definition and application")
}

fn matrix_result_mut(results: &mut [StmtResult]) -> &mut SuccessHaveMatrixStmtResult {
    let [StmtResult::Success(SuccessStmtResult::Definition(
        SuccessDefinitionStmtResult::HaveMatrixStmt(result),
    )), _] = results
    else {
        panic!("expected a matrix definition followed by an application fact")
    };
    result
}

#[test]
fn matrix_compiles_two_parameter_and_two_domain_results_in_one_child_environment() {
    let mut results = execute_matrix_definition();
    let result = matrix_result_mut(&mut results);
    let verification = result
        .verification
        .as_ref()
        .expect("matrix retains combined verification");
    assert_eq!(verification.bound_checks.len(), 4);
    assert_eq!(verification.assumption_infers.store_fact_outputs.len(), 4);
    let local_fact_ids = verification
        .assumption_infers
        .store_fact_outputs
        .iter()
        .map(|store| store.fact_id.expect("matrix local store retains FactId"))
        .collect::<Vec<_>>();
    let defining_equality_fact_id = result.common.infers.store_fact_outputs[1]
        .fact_id
        .expect("matrix equality retains its outer FactId");
    let mut compiler = StmtResultToLeanCompiler::new("direct_matrix.lit");

    assert!(compiler
        .compile_have_matrix_stmt_result_to_lean_source(result)
        .expect("compile matrix directly"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    assert_eq!(compiler.declarations.len(), 4);
    assert!(compiler.declarations[0]
        .contains("noncomputable def entry_matrix : Litex.FnTelescope.Carrier"));
    assert!(compiler.declarations[0].contains("__arg1"));
    assert!(compiler.declarations[0].contains("__arg2"));
    assert!(compiler.declarations[0].contains("fun __arg_domain => ULift.up"));
    assert!(compiler.declarations[1].contains("Litex.matrixSet.{0} Litex.R (2 : Nat) (3 : Nat)"));
    assert!(compiler.declarations[2].contains("Litex.fnTelescopeSet"));
    for fact_id in local_fact_ids {
        assert!(!compiler.environment_stack.fact_names.contains_key(&fact_id));
    }
    assert!(!compiler
        .environment_stack
        .symbol_names
        .contains_key(&result.statement.row_index_binding.id()));
    assert!(!compiler
        .environment_stack
        .symbol_names
        .contains_key(&result.statement.col_index_binding.id()));
    assert!(compiler
        .environment_stack
        .named_function_definitions
        .contains_key(&defining_equality_fact_id));
}

#[test]
fn matrix_rejects_a_missing_local_column_domain_fact_id() {
    let mut results = execute_matrix_definition();
    matrix_result_mut(&mut results)
        .verification
        .as_mut()
        .expect("matrix retains verification")
        .assumption_infers
        .store_fact_outputs[3]
        .fact_id = None;

    let error = StmtResultToLeanCompiler::new("direct_matrix.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("matrix column domain without a local FactId must fail closed");
    assert!(error.contains("matrix domain store 1 has no FactId"));
}
