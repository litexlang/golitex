use super::LitexToLeanCompiler;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::normalize_function_body::{
    FunctionBodyExpansionProof, FunctionBodyNormalizationProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::{
    by_fn_application::EqualitySearchProofByFnApplicationObjectDefinition,
    EqualitySearchProofByObjectDefinition,
};
use crate::prelude::*;

const SOURCE: &str = "have fn abs_context_inner(t R) R = t + 1\n\
have fn abs_context_outer(t R) R = |abs_context_inner(t)|\n\
forall x R:\n    abs_context_outer(x) = |abs_context_inner(x)|\n";

const EMBEDDED_SOURCE: &str = "have fn abs_context_inner(t R) R = t + 1\n\
have fn abs_context_outer(t R) R = |abs_context_inner(t)|\n\
forall x R:\n    abs_context_outer(x) = |x + 1|\n";

fn checked() -> (RunLitexCodeResult, LitexToLeanCompiler) {
    checked_source(SOURCE)
}

fn checked_source(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let result = runtime.run_litex_code(source).expect("source run");
    assert!(result.success && result.session_error.is_none());
    (result, LitexToLeanCompiler::new(runtime))
}

fn normalization(result: &mut RunLitexCodeResult) -> &mut FunctionBodyNormalizationProof {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        &mut result.statement_results[2]
    else {
        panic!("original forall statement");
    };
    let VerifyFactResult::ForallFact(forall) = &mut statement.verify_result else {
        panic!("original forall proof");
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(forall)) =
        forall.as_mut()
    else {
        panic!("original local forall");
    };
    let VerifyFactResult::Equality(equality) = &mut forall.proved_then_facts[0].verify_result
    else {
        panic!("original defining equality");
    };
    let VerifyEqualityResult::Success(equality) = equality.as_mut() else {
        panic!("checked equality");
    };
    let EqualFactSearchedProof::ByObjectDefinition(
        EqualitySearchProofByObjectDefinition::ByFnApplication(
            EqualitySearchProofByFnApplicationObjectDefinition::HaveFnEqual(proof),
        ),
    ) = &mut equality.searched_proof
    else {
        panic!("actual source function normalization route");
    };
    &mut proof.normalization
}

#[test]
fn absolute_value_function_normalization_preserves_original_call_and_context() {
    let (mut result, compiler) = checked();
    let proof = normalization(&mut result);
    assert!(matches!(
        proof.expanded_body,
        Obj::ArithmeticOperator(ArithmeticOperator::Abs(_))
    ));
    assert_eq!(proof.expansions.len(), 1);
    let lean = compiler
        .compile_run(&result, "abs_function_normalization")
        .expect("original absolute-value body normalization compiles");
    assert!(lean.contains("Litex.absValue (M := M)"));
    assert!(lean.contains("Litex.callFormula_denote"));
    assert!(lean.contains("Litex.abs"));
    assert!(!lean.contains("M.absValue"));
}

#[test]
fn absolute_value_context_embeds_its_actual_second_beta_expansion() {
    let (mut result, compiler) = checked_source(EMBEDDED_SOURCE);
    let proof = normalization(&mut result);
    assert_eq!(proof.expansions.len(), 2);
    let FunctionBodyExpansionProof::Anonymous(first) = &proof.expansions[0] else {
        panic!("original outer beta expansion");
    };
    let FunctionBodyExpansionProof::Anonymous(second) = &proof.expansions[1] else {
        panic!("original inner beta expansion");
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Abs(body)) = &first.continued_body else {
        panic!("original absolute-value context after the first expansion");
    };
    assert_eq!(body.arg.ir(), second.application.ir());
    let Obj::ArithmeticOperator(ArithmeticOperator::Abs(body)) = &proof.expanded_body else {
        panic!("final original absolute-value context");
    };
    assert_eq!(body.arg.ir(), second.continued_body.ir());
    let lean = compiler
        .compile_run(&result, "abs_embedded_function_normalization")
        .expect("original chronological inner beta under absolute value compiles");
    assert!(lean.contains("congrArg (Litex.absValue (M := M))"));
}

#[test]
fn absolute_value_normalization_rejects_changed_substituted_argument() {
    let (mut result, compiler) = checked();
    let proof = normalization(&mut result);
    let FunctionBodyExpansionProof::Anonymous(expansion) = &mut proof.expansions[0] else {
        panic!("actual anonymous expansion");
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Abs(body)) = &mut expansion.expanded_body
    else {
        panic!("original absolute-value body");
    };
    let Obj::FnObj(call) = body.arg.as_ref() else {
        panic!("original nested function call");
    };
    body.arg = call.body[0][0].clone();
    expansion.continued_body = expansion.expanded_body.clone();
    let error = compiler
        .compile_run(&result, "changed_abs_beta_argument")
        .unwrap_err();
    assert_eq!(error.route, "FunctionDefinition/Substitution");
}

#[test]
fn absolute_value_normalization_rejects_missing_original_expansion() {
    let (mut result, compiler) = checked();
    normalization(&mut result).expansions.clear();
    let error = compiler
        .compile_run(&result, "missing_abs_beta_expansion")
        .unwrap_err();
    assert_eq!(error.route, "FunctionDefinition/ExpansionArity");
}
