use super::source_position::{SourceOwner, SourcePosition};
use super::LitexToLeanCompiler;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::EqualFactSearchedProofByMatchingOneArgByOne;
use crate::execute::{
    ExecHaveFnByInducStmtResult, ExecHaveFnByInducStmtSuccessResult, InducCaseBodySuccess,
};
use crate::prelude::*;

const SOURCE: &str = "claim:\n    ? forall n N:\n        n = 0 or n > 0\n    n >= 0\n\n\
claim:\n    ? forall n N:\n        n > 0\n        =>:\n            n - 1 >= 0\n    n - 1 $in N\n    n - 1 >= 0\n\n\
have fn repeated_one(n N) R by induc n from 0:\n    case n = 0: 1\n    case n > 0: repeated_one(n - 1)\n\n\
repeated_one(0) = 1\n\n\
forall n N:\n    n > 0\n    =>:\n        repeated_one(n) = repeated_one(n - 1)\n";

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
    assert!(
        result.success && result.session_error.is_none(),
        "checked recursive source"
    );
    (result, LitexToLeanCompiler::new(runtime))
}

fn recursive_call_congruence_source() -> String {
    format!("{SOURCE}\nforall n N:\n    (n + 1) - 1 = n\n    repeated_one((n + 1) - 1) = repeated_one(n)\n")
}

fn call_congruence_mut(
    result: &mut RunLitexCodeResult,
) -> &mut EqualFactSearchedProofByMatchingOneArgByOne {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) = result
        .statement_results
        .last_mut()
        .expect("last source statement")
    else {
        panic!("successful congruence forall");
    };
    let VerifyFactResult::ForallFact(forall) = &mut statement.verify_result else {
        panic!("source forall");
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(forall)) =
        forall.as_mut()
    else {
        panic!("original local forall");
    };
    let VerifyFactResult::Equality(equality) = &mut forall.proved_then_facts[1].verify_result
    else {
        panic!("source call equality");
    };
    let VerifyEqualityResult::Success(equality) = equality.as_mut() else {
        panic!("checked call equality");
    };
    let EqualFactSearchedProof::ByMatchingOneArgByOne(proof) = &mut equality.searched_proof else {
        panic!("actual argument then head congruence certificate");
    };
    proof
}

#[test]
fn recursive_call_congruence_replays_ordered_argument_and_head_proofs() {
    let (mut result, compiler) = checked_source(&recursive_call_congruence_source());
    assert_eq!(
        call_congruence_mut(&mut result)
            .corresponding_arg_equal_proofs
            .len(),
        2
    );
    let lean = compiler
        .compile_run(&result, "recursive_call_congruence")
        .expect("captured call congruence compiles");
    assert!(lean.contains("Litex.callCongr"));
}

#[test]
fn recursive_call_congruence_rejects_reordered_children() {
    let (mut result, compiler) = checked_source(&recursive_call_congruence_source());
    call_congruence_mut(&mut result)
        .corresponding_arg_equal_proofs
        .swap(0, 1);
    let error = compiler
        .compile_run(&result, "reordered_call_congruence")
        .unwrap_err();
    assert_eq!(error.route, "FunctionCongruence/ChildSubject");
}

#[test]
fn recursive_call_congruence_rejects_missing_head_proof() {
    let (mut result, compiler) = checked_source(&recursive_call_congruence_source());
    call_congruence_mut(&mut result)
        .corresponding_arg_equal_proofs
        .pop();
    let error = compiler
        .compile_run(&result, "missing_call_head_congruence")
        .unwrap_err();
    assert_eq!(error.route, "FunctionCongruence/Children");
}

fn declaration(result: &mut RunLitexCodeResult) -> &mut ExecHaveFnByInducStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
        ExecHaveFnByInducStmtResult::Success(proof),
    )) = &mut result.statement_results[2]
    else {
        panic!("successful recursive declaration");
    };
    proof
}

#[test]
fn recursive_graph_consumes_source_case_stores_and_smaller_call_guards() {
    let (result, compiler) = checked();
    let lean = compiler
        .compile_run(&result, "recursive_source_graph")
        .expect("owned recursive graph compiles");
    assert!(lean.contains("Litex.recursiveNatFnTarget"));
    assert!(lean.contains("Litex.recursiveNatFnInFnSet"));
    assert!(lean.contains("Litex.recursiveNatFn_zero"));
    assert!(lean.contains("Litex.recursiveNatFn_succ"));
    assert!(lean.contains("_agree"));
    assert!(!lean.contains("sorry"));
}

#[test]
fn recursive_declaration_without_later_calls_retains_function_semantics() {
    let source = SOURCE
        .split("\n\nrepeated_one(0)")
        .next()
        .expect("original source declaration prefix");
    let (result, compiler) = checked_source(source);
    assert_eq!(result.statement_results.len(), 3);
    let lean = compiler
        .compile_run(&result, "recursive_declaration_only")
        .expect("completed declaration compiles without a later call");
    assert!(lean.contains("variable [_functionSemantics : Litex.FunctionSemantics M]"));
    assert!(lean.contains("Litex.recursiveNatFnTarget"));
}

#[test]
fn recursive_graph_rejects_missing_original_binder_store() {
    let (mut result, compiler) = checked();
    let proof = declaration(&mut result);
    proof
        .binder_introduction
        .defined_params
        .store_and_infer_results
        .clear();
    proof
        .binder_introduction
        .defined_params
        .stored_fact_ids
        .clear();
    let error = compiler
        .compile_run(&result, "missing_recursive_binder")
        .unwrap_err();
    assert!(error.route.contains("BinderCapture"), "{error}");
}

#[test]
fn recursive_graph_rejects_forged_membership_id_view() {
    let (mut result, compiler) = checked();
    let proof = declaration(&mut result);
    proof.store_and_infer_result.membership_fact_id =
        proof.restricted_self_membership.primary_fact_id();
    let error = compiler
        .compile_run(&result, "wrong_recursive_store")
        .unwrap_err();
    assert!(error.route.contains("StoreCapture"), "{error}");
}

#[test]
fn recursive_graph_rejects_missing_smaller_index_evidence() {
    let (mut result, compiler) = checked();
    let proof = declaration(&mut result);
    let InducCaseBodySuccess::EqualTo {
        well_defined:
            VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::FnObj(call),
                ..
            }),
        ..
    } = &mut proof.case_checks.cases[1].body
    else {
        panic!("original recursive call formation");
    };
    call.requirement_fact_verified.pop();
    let error = compiler
        .compile_run(&result, "missing_recursive_guard")
        .unwrap_err();
    assert!(
        error.route.contains("StageArity") || error.route.contains("CallSelfEvidence"),
        "{error}"
    );
}

#[test]
fn recursive_graph_rejects_future_restricted_self_store() {
    let (result, compiler) = checked();
    let statement = &result.statement_results[2];
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
        ExecHaveFnByInducStmtResult::Success(proof),
    )) = statement
    else {
        panic!("source declaration");
    };
    let root = SourcePosition::new(None, SourceOwner::Run(&result), 2);
    let formation = SourcePosition::new(Some(&root), SourceOwner::RecursiveFunction(proof), 6);
    let error = formation
        .visible_fact(
            proof.restricted_self_membership.primary_fact_id(),
            &compiler.runtime,
        )
        .unwrap_err();
    assert!(error.route.contains("FutureProducer"), "{error}");
    assert!(formation
        .visible_recursive_self(&proof.statement.name.id)
        .is_err());
    let StoreFactResult::AtomicFact(stored) = &proof.restricted_self_membership.store else {
        panic!("actual restricted membership");
    };
    let AtomicFact::InFact(member) = &stored.fact else {
        panic!("actual restricted fnset");
    };
    assert!(formation
        .generated_recursive_signature(&member.set)
        .is_none());
}

#[test]
fn recursive_graph_rejects_future_final_equation_store() {
    let (result, compiler) = checked();
    let statement = &result.statement_results[2];
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
        ExecHaveFnByInducStmtResult::Success(proof),
    )) = statement
    else {
        panic!("source declaration");
    };
    let root = SourcePosition::new(None, SourceOwner::Run(&result), 2);
    let formation = SourcePosition::new(Some(&root), SourceOwner::Statement(statement), 7);
    let error = formation
        .visible_fact(
            proof.store_and_infer_result.case_defining_fact_ids[1],
            &compiler.runtime,
        )
        .unwrap_err();
    assert!(error.route.contains("FutureProducer"), "{error}");
}

#[test]
fn recursive_graph_rejects_escaped_branch_assumption() {
    let (result, compiler) = checked();
    let statement = &result.statement_results[2];
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
        ExecHaveFnByInducStmtResult::Success(proof),
    )) = statement
    else {
        panic!("source declaration");
    };
    let after_declaration = SourcePosition::new(None, SourceOwner::Run(&result), 3);
    assert!(after_declaration
        .visible_fact(
            proof.case_checks.cases[1]
                .assumption_stored
                .primary_fact_id(),
            &compiler.runtime
        )
        .is_err());
}

#[test]
fn recursive_graph_rejects_authored_domain_extension() {
    let source = SOURCE.replace(
        "have fn repeated_one(n N) R",
        "have fn repeated_one(n N: n >= 0) R",
    );
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let result = runtime
        .run_litex_code(&source)
        .expect("checked guarded source");
    assert!(result.success && result.session_error.is_none());
    let error = LitexToLeanCompiler::new(runtime)
        .compile_run(&result, "authored_recursive_domain")
        .unwrap_err();
    assert_eq!(error.route, "RecursiveFunction/UnaryNaturalCases");
}
