use super::LitexToLeanCompiler;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicExceptEqualityResult, InferAtomicFactResult, InferFactResult,
};

const NONZERO: &str = "prop nonzero(x R):\n    x != 0\n$nonzero(1)\nby def $nonzero(1)\n1 != 0";
const SQUARE: &str = "prop square_is_one(x R):\n    x * x = 1\n$square_is_one(1)\n1 * 1 = 1";
const GUARDED: &str =
    "prop guarded_identity(x R):\n    x != 0\n    x / x = 1\n$guarded_identity(1)\n1 / 1 = 1";

fn checked(source: &str) -> (Runtime, RunLitexCodeResult) {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let result = runtime.run_litex_code(source).unwrap();
    assert!(result.success && result.session_error.is_none(), "{source}");
    (runtime, result)
}

#[test]
fn concrete_prop_retains_domains_and_actual_explicit_definition_route() {
    let (runtime, result) = checked(NONZERO);
    let ExecStmtResult::By(ExecByStmtResult::Def(
        crate::execute::execute_by_stmt::ExecByDefStmtResult::Success(by_def),
    )) = &result.statement_results[2]
    else {
        panic!("explicit definition request");
    };
    let VerifyFactResult::AtomicExceptEquality(proof) = &by_def.proof else {
        panic!("atomic definition proof");
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_ref() else {
        panic!("successful definition proof");
    };
    assert!(matches!(
        &proof.searched_proof,
        AtomicExceptEqualityFactSearchedProof::ByDefinition(_)
    ));
    let output = LitexToLeanCompiler::new(runtime)
        .compile_run(&result, "concrete_nonzero")
        .unwrap();
    assert!(output.contains("def prop_1"));
    assert!(output.contains("∃ (h_"));
    assert!(output.contains("Litex.In _value_i"));
    assert!(output.contains("Exists.intro"));
    assert!(output.contains("rcases"));
}

#[test]
fn concrete_prop_inference_retains_actual_constructor_formation_before_store() {
    let (runtime, result) = checked(SQUARE);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(seed)) = &result.statement_results[1]
    else {
        panic!("predicate seed");
    };
    let Some(InferFactResult::AtomicFact(InferAtomicFactResult::ExceptEquality(rules))) =
        &seed.store_and_infer_result.infer
    else {
        panic!("predicate infer dispatcher");
    };
    let InferAtomicExceptEqualityResult::NormalAtomicParamTypes(members) = &rules[0] else {
        panic!("ordered parameter projections");
    };
    let InferAtomicExceptEqualityResult::NormalAtomicExpandDefinition(body) = &rules[1] else {
        panic!("ordered definition expansion");
    };
    assert_eq!(members.derived.len(), 1);
    assert_eq!(body.derived.len(), 1);
    let derived = &body.derived[0];
    let StoreFactResult::AtomicFact(stored) = &derived.store else {
        panic!("atomic defining clause");
    };
    let AtomicFact::EqualFact(equality) = &stored.fact else {
        panic!("square defining equality");
    };
    let FactWellDefinedProof::Equality(wd) = &derived.well_defined else {
        panic!("captured equality formation");
    };
    assert_eq!(wd.left.obj().ir(), equality.left.ir());
    assert_eq!(wd.right.obj().ir(), equality.right.ir());
    let actual_id = derived.store.primary_fact_id();
    assert!(seed
        .store_and_infer_result
        .stored_fact_ids()
        .contains(&actual_id));
    let output = LitexToLeanCompiler::new(runtime)
        .compile_run(&result, "concrete_square")
        .unwrap();
    assert!(output.contains(&format!("theorem h_{}", actual_id.value())));
    assert!(output.contains("Litex.mul"));
    assert!(output.contains("rcases"));
}

#[test]
fn concrete_prop_earlier_clause_certifies_later_guarded_constructor() {
    let (runtime, result) = checked(GUARDED);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
        crate::execute::ExecDefPropStmtResult::Success(definition),
    )) = &result.statement_results[0]
    else {
        panic!("concrete definition");
    };
    assert_eq!(definition.assumed_iff_facts.len(), 2);
    let nonzero_id = definition.assumed_iff_facts[0]
        .store_and_infer
        .primary_fact_id();
    let output = LitexToLeanCompiler::new(runtime)
        .compile_run(&result, "concrete_guarded")
        .unwrap();
    assert!(output.contains(&format!("∃ (h_{}", nonzero_id.value())));
    assert!(output.contains("Litex.div"));
}

#[test]
fn concrete_prop_cannot_resolve_a_removed_definition_from_final_runtime() {
    let (runtime, mut result) = checked(NONZERO);
    result.statement_results.remove(0);
    let error = LitexToLeanCompiler::new(runtime)
        .compile_run(&result, "missing_prop")
        .unwrap_err();
    assert!(error.route.starts_with("Prop/"), "{error:?}");
}

#[test]
fn concrete_prop_rejects_definition_requirements_without_their_actual_proof_ids() {
    let (runtime, mut result) = checked(NONZERO);
    let ExecStmtResult::By(ExecByStmtResult::Def(
        crate::execute::execute_by_stmt::ExecByDefStmtResult::Success(by_def),
    )) = &mut result.statement_results[2]
    else {
        panic!("explicit definition request");
    };
    let VerifyFactResult::AtomicExceptEquality(proof) = &mut by_def.proof else {
        panic!("atomic definition proof");
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_mut() else {
        panic!("successful definition proof");
    };
    let AtomicExceptEqualityFactSearchedProof::ByDefinition(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactSearchProofByDefinition::UserDefinedProp(definition)) = &mut proof.searched_proof else { panic!("selected concrete fold"); };
    definition.proof_of_requirement_facts.pop();
    let error = LitexToLeanCompiler::new(runtime)
        .compile_run(&result, "missing_fold_child")
        .unwrap_err();
    assert_eq!(error.route, "Prop/FoldArity");
}

#[test]
fn concrete_prop_rejects_reordered_domain_and_body_inferences() {
    let (runtime, mut result) = checked(SQUARE);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(seed)) = &mut result.statement_results[1]
    else {
        panic!("predicate seed");
    };
    let Some(InferFactResult::AtomicFact(InferAtomicFactResult::ExceptEquality(rules))) =
        &mut seed.store_and_infer_result.infer
    else {
        panic!("predicate infer dispatcher");
    };
    rules.swap(0, 1);
    let error = LitexToLeanCompiler::new(runtime)
        .compile_run(&result, "reordered_prop_inference")
        .unwrap_err();
    assert!(error.route.starts_with("Prop/Infer"), "{error:?}");
}
