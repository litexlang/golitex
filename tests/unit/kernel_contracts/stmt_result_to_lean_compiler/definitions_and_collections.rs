use super::super::*;

fn execute_concrete_predicate_and_by_definition() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        "prop is_unit_pair(x R, y R):\n    x = 1\n    y = 1\n\n1 = 1\nby def $is_unit_pair(1, 1)\n",
        "direct_by_definition.lit",
    )
    .expect("execute concrete predicate and by-definition")
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
    let StmtResult::Success(SuccessStmtResult::DefPredicateStmt(
        SuccessDefPredicateStmtResult::DefPropStmt(definition),
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
    assert!(compiler.declarations[2].contains(
            "exact ⟨Litex.Rules.complexRealInR (1 : ℝ), Litex.Rules.complexRealInR (1 : ℝ), __fact0, __fact0⟩"
        ));
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

fn execute_named_real_function(source: &str) -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        source,
        "direct_named_real_function.lit",
    )
    .expect("execute named real function")
}

fn named_real_function_result_mut(results: &mut [StmtResult]) -> &mut SuccessHaveFnEqualStmtResult {
    let [StmtResult::Success(SuccessStmtResult::DefObjStmt(
        SuccessDefObjStmtResult::HaveFnEqualStmt(result),
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
    assert!(binding.uses_native_real_body);
}

#[test]
fn checked_named_function_reduction_uses_its_exact_definition_fact_id() {
    let results = execute_named_real_function("have fn inc(x R) R = x + 1\ninc(2) = 2 + 1\n");
    let reduction_result = results[1]
        .factual_success()
        .expect("second statement is a factual reduction");
    let SuccessFactProofResult::CheckedFunctionDefinitionReduction(reduction) =
        reduction_result.proof()
    else {
        panic!("checked definition reduction must retain typed evidence")
    };
    let StmtResult::Success(SuccessStmtResult::DefObjStmt(
        SuccessDefObjStmtResult::HaveFnEqualStmt(definition),
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
    assert!(lean.contains("unfold Litex.fnApplyOwn inc"));
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
    let verification = std::rc::Rc::get_mut(&mut reduction_result.verification)
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
    let [StmtResult::Success(SuccessStmtResult::DefObjStmt(
        SuccessDefObjStmtResult::HaveFnEqualStmt(definition),
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
    assert!(compiler.declarations.last().is_some_and(|declaration| {
        declaration.contains("unfold Litex.fnApplyWhereOwn reciprocal")
            && declaration.contains("__domain1")
            && declaration.contains("Litex.Same.realComplex ((Litex.In.rep a ")
            && !declaration.contains("Litex.Same.symm (Litex.In.same_rep a (__h8_1))")
    }));
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
    let [StmtResult::Success(SuccessStmtResult::DefObjStmt(SuccessDefObjStmtResult::HaveTupleStmt(
        result,
    )))] = results
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
    let [StmtResult::Success(SuccessStmtResult::DefObjStmt(SuccessDefObjStmtResult::HaveSeqStmt(
        result,
    )))] = results
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
    let [StmtResult::Success(SuccessStmtResult::DefObjStmt(
        SuccessDefObjStmtResult::HaveFiniteSeqStmt(result),
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
    let [StmtResult::Success(SuccessStmtResult::DefObjStmt(
        SuccessDefObjStmtResult::HaveMatrixStmt(result),
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
