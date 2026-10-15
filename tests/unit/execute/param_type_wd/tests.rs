use crate::prelude::*;

#[test]
fn successful_parameter_checks_preserve_group_order_and_object_subject() {
    let mut rt = runtime();
    let parameters = parameters(&mut rt, "A set, B nonempty_set, F finite_set, x R");
    let results = rt
        .verify_typed_parameters_well_definedness(&parameters, VerifyState::top_level())
        .unwrap();
    use VerifyParamTypeWellDefinedResult::Success;
    let [Success(ParamTypeWellDefinedProof::Set), Success(ParamTypeWellDefinedProof::NonemptySet), Success(ParamTypeWellDefinedProof::FiniteSet), Success(ParamTypeWellDefinedProof::Obj(proof))] =
        results.as_slice()
    else {
        panic!("one successful proof per parameter group, in source order");
    };
    let ParamType::Obj(carrier) = &parameters.groups[3].param_type else {
        panic!("expected the real carrier");
    };
    assert_eq!(proof.obj().ir(), carrier.ir());
}

#[test]
fn failed_parameter_check_preserves_subject_and_division_requirement() {
    let mut rt = runtime();
    let parameters = parameters(&mut rt, "x (1 / 0)");
    let param_type = &parameters.groups[0].param_type;
    let checked = rt
        .verify_param_type_well_definedness(param_type, VerifyState::top_level())
        .expect("invalid carrier is an ordinary verification failure");
    assert!(checked.is_failed());
    let VerifyParamTypeWellDefinedResult::Failed { obj, reason } = checked else {
        panic!("division by zero cannot produce parameter WD evidence");
    };
    let ParamType::Obj(carrier) = param_type else {
        panic!("expected an object carrier");
    };
    assert_eq!(obj.ir(), carrier.ir());
    let FailToVerifyObjWellDefinedResult::ArithmeticOperator(
        FailToVerifyArithmeticOperatorObjWellDefinedResult::Div(failure),
    ) = reason
    else {
        panic!("preserve the division failure reason");
    };
    let FailToVerifyObjWellDefinedByDefCommon::Requirement { result, .. } = failure.0 else {
        panic!("preserve the unmet division requirement");
    };
    assert!(result.is_failed());
}

#[test]
fn failed_parameter_declaration_rolls_back_and_retry_retains_only_success_evidence() {
    let mut rt = runtime();
    let failed = rt.run_litex_code("have value (1 / 0) = 0").unwrap();
    assert!(!failed.success);
    assert!(failed.session_error.is_none());
    assert_eq!(failed.statement_results.len(), 1);
    assert!(matches!(
        &failed.statement_results[0],
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Failed(
                crate::execute::ExecHaveObjEqualStmtFailed::ParamType(
                    VerifyObjWellDefinedResult::Failed { .. }
                )
            ))
        ))
    ));
    assert_eq!(rt.execution_environments_stack.len(), 1);
    assert!(!rt.execution_environments_stack[0]
        .definitions
        .identifiers
        .contains_key("value"));

    let retry = rt.run_litex_code("have value R = 0\nvalue = 0").unwrap();
    assert!(retry.success && retry.session_error.is_none());
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(proof)),
    )) = &retry.statement_results[0]
    else {
        panic!("the failed declaration must leave its name available");
    };
    let [ParamTypeWellDefinedProof::Obj(wd)] =
        proof.type_preflight.param_type_well_defined.as_slice()
    else {
        panic!("the accepted declaration retains successful object WD evidence");
    };
    assert_eq!(wd.obj().ir(), Obj::StandardSet(StandardSet::R).ir());
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

fn parameters(rt: &mut Runtime, signature: &str) -> TypedParameterList {
    let code = format!("forall {signature}:\n    x = x\n");
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize(&code, rt.current_file.clone())
        .unwrap();
    let statements = rt.parse(&tokens).unwrap();
    let Stmt::Fact(Fact::ForallFact(fact)) = &statements[0] else {
        panic!("expected a quantified fact");
    };
    fact.typed_parameters.clone()
}
