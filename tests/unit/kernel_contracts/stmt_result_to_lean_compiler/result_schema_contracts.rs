use super::super::*;
use crate::output::display_stmt_result_json_v2;

#[test]
fn def_struct_result_retains_each_local_verification_phase_without_synthetic_statements() {
    let results = crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_to_stmt_results(
            "struct ValueBox<S set>:\n    value S\n    <=>:\n        value = value\n",
            "def_struct_result_contract.lit",
        )
        .expect("execute struct Result contract fixture");
    let [StmtResult::Success(SuccessStmtResult::DefInterfaceStmt(
        SuccessDefInterfaceStmtResult::DefStructStmt(result),
    ))] = results.as_slice()
    else {
        panic!("expected one successful def-struct Result")
    };

    let local = result
        .run_in_local_env
        .as_ref()
        .expect("verified struct must retain its local verification flow");
    assert!(local.structure_parameter_definition.is_some());
    assert!(local.structure_domains.is_empty());
    assert_eq!(local.field_types.len(), 1);
    assert_eq!(local.field_types[0].field_index, 0);
    assert_eq!(local.field_types[0].binding.name(), "value");

    let field_scope = &local.field_scope_run_in_local_env;
    assert_eq!(field_scope.field_definitions.len(), 1);
    assert_eq!(field_scope.field_definitions[0].field_index, 0);
    assert_eq!(field_scope.equivalent_facts.len(), 1);
    assert!(field_scope.equivalent_facts[0].store.fact_id.is_some());
    let json = display_stmt_result_json_v2(&results[0]);
    assert!(json.contains("\"run_in_local_env\""), "{json}");
    assert!(json.contains("\"equivalent_facts\""), "{json}");
    let compiler_error = StmtResultToLeanCompiler::new("def_struct_result_contract.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("unsupported struct lowering must fail closed");
    assert!(compiler_error.contains("DefStructStmt"), "{compiler_error}");
}

#[test]
fn def_algo_result_retains_retagged_parameters_and_the_exact_default_check() {
    let results = crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_to_stmt_results(
            "have fn identity(x R) R = x\nhave algo for identity(x):\n    x\n",
            "def_algo_result_contract.lit",
        )
        .expect("execute algorithm Result contract fixture");
    let [_, StmtResult::Success(SuccessStmtResult::DefAlgoStmt(result))] = results.as_slice()
    else {
        panic!("expected function declaration followed by def-algo Result")
    };

    let local = result
        .run_in_local_env
        .as_ref()
        .expect("verified algorithm must retain its local verification flow");
    assert_eq!(local.parameter_retagging.len(), 1);
    assert_eq!(local.parameter_retagging[0].parameter_index, 0);
    assert_eq!(local.parameter_retagging[0].source_binding.name(), "x");
    assert!(!local.requirement_facts.is_empty());
    assert!(local.cases.is_empty());
    assert!(local.default_return.is_some());
    assert!(local.coverage.is_none());
    assert!(local
        .default_return
        .as_ref()
        .expect("default check")
        .verification
        .is_true());
    let mut child_results = Vec::new();
    let StmtResult::Success(success) = &results[1] else {
        unreachable!("the statement was already matched as successful")
    };
    success.visit_child_results(&mut |child| child_results.push(child.statement()));
    assert_eq!(
        child_results.len(),
        1,
        "the generic Result visitor must expose the exact default-return check"
    );
    let json = display_stmt_result_json_v2(&results[1]);
    assert!(json.contains("\"parameter_retagging\""), "{json}");
    assert!(json.contains("\"default_return\""), "{json}");
    let compiler_error = StmtResultToLeanCompiler::new("def_algo_result_contract.lit")
        .compile_stmt_results_to_lean_source(&results[1..])
        .expect_err("unsupported algorithm lowering must fail closed");
    assert!(compiler_error.contains("DefAlgoStmt"), "{compiler_error}");
}

#[test]
fn inductive_function_result_retains_both_local_flows_and_recursive_cases() {
    let results = crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_to_stmt_results(
            r#"have fn step(x R+) R+ = (x + 2 / x) / 2
have fn iterate(n N) R+ by induc n from 0:
    case n = 0: 1
    case n > 0: step(iterate(n - 1))
"#,
            "have_fn_by_induc_result_contract.lit",
        )
        .expect("execute inductive-function Result contract fixture");
    let [_, StmtResult::Success(SuccessStmtResult::DefObjStmt(
        SuccessDefObjStmtResult::HaveFnByInducStmt(result),
    ))] = results.as_slice()
    else {
        panic!("expected helper function followed by inductive-function Result")
    };

    let verification = result
        .verification
        .as_ref()
        .expect("verified inductive function must retain verification");
    assert_eq!(
        verification
            .well_definedness_run_in_local_env
            .parameters_and_domain
            .parameter_groups
            .len(),
        1
    );
    let local = &verification.verification_run_in_local_env;
    assert!(local.measure.measure_integer_check.is_true());
    assert!(local.measure.lower_bound_integer_check.is_true());
    assert!(local.measure.lower_bound_check.is_true());
    assert!(local.recursive_function.membership_store.fact_id.is_some());
    assert!(local.cases.coverage_check.is_true());
    assert_eq!(local.cases.mutual_exclusions.len(), 1);
    assert_eq!(local.cases.mutual_exclusions[0].left_case_index, 0);
    assert_eq!(local.cases.mutual_exclusions[0].right_case_index, 1);
    assert!(local.cases.mutual_exclusions[0]
        .negated_atom_check
        .is_true());
    assert_eq!(local.cases.cases.len(), 2);
    for case in &local.cases.cases {
        assert!(case.assumption_store.fact_id.is_some());
        let SuccessVerifyHaveFnByInducCaseBodyResult::EqualTo(body) = &case.body else {
            panic!("fixture cases must retain equal-to bodies")
        };
        assert!(body.return_membership_check.is_true());
    }
    let mut visited_children = 0;
    let StmtResult::Success(success) = &results[1] else {
        unreachable!("the statement was already matched as successful")
    };
    success.visit_child_results(&mut |_| visited_children += 1);
    assert_eq!(
        visited_children, 7,
        "the generic Result visitor must expose three measure checks, coverage, one disjointness check, and two return checks"
    );
    let json = display_stmt_result_json_v2(&results[1]);
    assert!(
        json.contains("\"well_definedness_run_in_local_env\""),
        "{json}"
    );
    assert!(json.contains("\"mutual_exclusions\""), "{json}");
    let compiler_error = StmtResultToLeanCompiler::new("have_fn_by_induc_result_contract.lit")
        .compile_stmt_results_to_lean_source(&results[1..])
        .expect_err("unsupported inductive-function lowering must fail closed");
    assert!(
        compiler_error.contains("HaveFnByInducStmt"),
        "{compiler_error}"
    );
}

#[test]
fn trusted_definition_results_do_not_invent_verification_evidence() {
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("trusted_definition_results.lit");
    runtime.replace_current_execution_mode(ExecutionMode::Trusted);
    let (results, error) = crate::pipeline::pipeline::run_source_code(
        r#"struct TrustedBox:
    value R
have fn trustedIdentity(x R) R = x
have algo for trustedIdentity(x):
    x
have fn trustedIterate(n N) R by induc n from 0:
    case n = 0: 0
    case n > 0: trustedIterate(n - 1)
"#,
        &mut runtime,
    );
    assert!(error.is_none(), "{error:?}");
    assert_eq!(results.len(), 4);

    let StmtResult::Success(SuccessStmtResult::DefInterfaceStmt(
        SuccessDefInterfaceStmtResult::DefStructStmt(result),
    )) = &results[0]
    else {
        panic!("expected trusted struct Result")
    };
    assert!(result.run_in_local_env.is_none());

    let StmtResult::Success(SuccessStmtResult::DefAlgoStmt(result)) = &results[2] else {
        panic!("expected trusted algorithm Result")
    };
    assert!(result.run_in_local_env.is_none());

    let StmtResult::Success(SuccessStmtResult::DefObjStmt(
        SuccessDefObjStmtResult::HaveFnByInducStmt(result),
    )) = &results[3]
    else {
        panic!("expected trusted inductive-function Result")
    };
    assert!(result.verification.is_none());
}
