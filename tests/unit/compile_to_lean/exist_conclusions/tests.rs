use crate::compile_to_lean::LitexToLeanCompiler;
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::{
    ExistShapedFactSearchProofByBuiltinRule, ExistShapedFactSearchedProof,
};
use crate::prelude::*;

const NAMED_CASES: &str = "thm geo_cases_plain_exist_probe:\n    ? forall geo_cases_seed R:\n        exist geo_cases_copy R st {geo_cases_copy = geo_cases_seed}\n    by cases:\n        ? exist geo_cases_copy R st {geo_cases_copy = geo_cases_seed}\n        case geo_cases_seed = 0:\n            witness exist geo_cases_copy R st {geo_cases_copy = geo_cases_seed} from geo_cases_seed\n        case geo_cases_seed != 0:\n            witness exist geo_cases_copy R st {geo_cases_copy = geo_cases_seed} from geo_cases_seed\n";
const FORALL: &str = "forall geo_forall_order_seed R:\n    exist geo_forall_order_copy R st {geo_forall_order_copy = geo_forall_order_seed}\n    exist geo_forall_order_zero R st {geo_forall_order_zero = 0}\n    =>:\n        exist geo_forall_order_output R st {geo_forall_order_output = geo_forall_order_seed}\n        exist geo_forall_order_zero_output R st {geo_forall_order_zero_output = 0}\n";

fn checked(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let run = runtime.run_litex_code(source).expect("source execution");
    assert!(
        run.success && run.session_error.is_none(),
        "{}",
        crate::json_output::emit_run_detailed(&run, &runtime, "exist_conclusions", None)
    );
    (run, LitexToLeanCompiler::new(runtime))
}

fn named(run: &mut RunLitexCodeResult) -> &mut ExecDefThmStmtSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(proof),
    )) = &mut run.statement_results[0]
    else {
        panic!("original named theorem")
    };
    proof
}

fn forall(run: &mut RunLitexCodeResult) -> &mut VerifyForallFactSuccess {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        &mut run.statement_results[0]
    else {
        panic!("original fact statement")
    };
    let VerifyFactResult::ForallFact(verification) = &mut statement.verify_result else {
        panic!("original forall verification")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(proof)) =
        verification.as_mut()
    else {
        panic!("original local introduction")
    };
    proof
}

fn real_line_requirements(
    verification: &mut VerifyFactResult,
) -> (&mut Vec<Fact>, &mut Vec<VerifyFactResult>) {
    let VerifyFactResult::ExistShapedFact(result) = verification else {
        panic!("original existential conclusion")
    };
    let VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Success(proof)) =
        result.as_mut()
    else {
        panic!("original successful plain-exist result")
    };
    let ExistShapedFactSearchedProof::ByBuiltinRule(
        ExistShapedFactSearchProofByBuiltinRule::RealLineComparisonWitness(proof),
    ) = &mut proof.searched_proof
    else {
        panic!("actual selected real-line witness rule")
    };
    (
        &mut proof.requirement_facts,
        &mut proof.proof_of_requirement_facts,
    )
}

#[test]
fn geo_named_exist_conclusion_replays_original_cases_and_witnesses() {
    let (mut run, compiler) = checked(NAMED_CASES);
    let ExecDefThmBodyProof::Forall(body) = &mut named(&mut run).body else {
        panic!("original named forall body")
    };
    let (requirements, children) = real_line_requirements(&mut body.conclusion_proofs[0]);
    assert_eq!((requirements.len(), children.len()), (1, 1));
    let lean = compiler
        .compile_run(&run, "named_exist_cases")
        .expect("plain exist conclusion");
    assert!(lean.contains("Classical.em"));
    assert!(lean.contains("Litex.semanticObject"));
    assert!(lean.contains("Litex.Obj (M := M) M.Value"));
    assert!(!lean.contains("sorry"));
}

#[test]
fn geo_forall_exist_conclusions_replay_original_ordered_verifications_and_stores() {
    let (mut run, compiler) = checked(FORALL);
    let ids = forall(&mut run)
        .proved_then_facts
        .iter()
        .map(|proof| proof.store_and_infer.primary_fact_id())
        .collect::<Vec<_>>();
    assert_eq!(ids.len(), 2);
    let lean = compiler
        .compile_run(&run, "forall_exist_ordered")
        .expect("plain exist conclusions");
    // The first existential must close before the next conjunction component;
    // otherwise Lean reads `exists x, P x ∧ exists y, Q y` instead of the two
    // source conclusions proved by the original And.intro.
    assert!(lean.contains(") ∧ (∃"));
    for id in ids {
        assert!(lean.contains(&format!("have h_{} :", id.value())));
    }
}

#[test]
fn geo_named_exist_conclusion_rejects_missing_original_body_formation() {
    let (mut run, compiler) = checked(NAMED_CASES);
    let VerifyFactWellDefinedResult::Success(FactWellDefinedProof::ForallFact(goal)) =
        &mut named(&mut run).goal_wd
    else {
        panic!("original forall goal formation")
    };
    let FactWellDefinedProof::ExistFact(exist) = &mut goal.then[0] else {
        panic!("original existential conclusion formation")
    };
    exist.assumed_body_facts.clear();
    assert_eq!(
        compiler
            .compile_run(&run, "missing_exist_formation")
            .unwrap_err()
            .route,
        "Exist/FormationStages"
    );
}

#[test]
fn geo_named_exist_conclusion_rejects_missing_original_verification() {
    let (mut run, compiler) = checked(NAMED_CASES);
    let ExecDefThmBodyProof::Forall(body) = &mut named(&mut run).body else {
        panic!("original forall body")
    };
    body.conclusion_proofs.clear();
    assert_eq!(
        compiler
            .compile_run(&run, "missing_named_conclusion")
            .unwrap_err()
            .route,
        "Theorem/Stages"
    );
}

#[test]
fn geo_forall_exist_conclusion_rejects_missing_original_verification() {
    let (mut run, compiler) = checked(FORALL);
    forall(&mut run).proved_then_facts.pop();
    assert_eq!(
        compiler
            .compile_run(&run, "missing_forall_conclusion")
            .unwrap_err()
            .route,
        "Forall/Then"
    );
}

#[test]
fn geo_forall_exist_conclusion_rejects_reordered_original_verifications() {
    let (mut run, compiler) = checked(FORALL);
    forall(&mut run).proved_then_facts.swap(0, 1);
    assert_eq!(
        compiler
            .compile_run(&run, "reordered_forall_conclusions")
            .unwrap_err()
            .route,
        "Forall/Then"
    );
}

#[test]
fn geo_forall_exist_conclusion_rejects_reordered_original_stores() {
    let (mut run, compiler) = checked(FORALL);
    let (first, rest) = forall(&mut run).proved_then_facts.split_at_mut(1);
    std::mem::swap(&mut first[0].store_and_infer, &mut rest[0].store_and_infer);
    assert_eq!(
        compiler
            .compile_run(&run, "reordered_forall_stores")
            .unwrap_err()
            .route,
        "Store/Subject"
    );
}

#[test]
fn geo_exist_real_equality_rejects_missing_original_requirement() {
    let (mut run, compiler) = checked(FORALL);
    real_line_requirements(&mut forall(&mut run).proved_then_facts[0].verify_result)
        .0
        .clear();
    assert_eq!(
        compiler
            .compile_run(&run, "missing_real_requirement")
            .unwrap_err()
            .route,
        "Exist/RealLineComparisonRequirements"
    );
}

#[test]
fn geo_exist_real_equality_rejects_missing_original_child() {
    let (mut run, compiler) = checked(FORALL);
    real_line_requirements(&mut forall(&mut run).proved_then_facts[0].verify_result)
        .1
        .clear();
    assert_eq!(
        compiler
            .compile_run(&run, "missing_real_child")
            .unwrap_err()
            .route,
        "Exist/RealLineComparisonRequirements"
    );
}

#[test]
fn geo_exist_real_equality_rejects_another_original_requirement() {
    let (mut run, compiler) = checked(FORALL);
    let (first, rest) = forall(&mut run).proved_then_facts.split_at_mut(1);
    let first = real_line_requirements(&mut first[0].verify_result).0;
    let second = real_line_requirements(&mut rest[0].verify_result).0;
    std::mem::swap(first, second);
    assert_eq!(
        compiler
            .compile_run(&run, "wrong_real_requirement")
            .unwrap_err()
            .route,
        "Exist/RealLineComparisonMembership"
    );
}

#[test]
fn geo_exist_real_equality_rejects_another_successful_child() {
    let (mut run, compiler) = checked(FORALL);
    let (first, rest) = forall(&mut run).proved_then_facts.split_at_mut(1);
    let first = real_line_requirements(&mut first[0].verify_result).1;
    let second = real_line_requirements(&mut rest[0].verify_result).1;
    std::mem::swap(first, second);
    assert_eq!(
        compiler
            .compile_run(&run, "wrong_real_child")
            .unwrap_err()
            .route,
        "Exist/RealLineComparisonChild"
    );
}

#[test]
fn real_line_comparison_witnesses_replay_every_relation_and_orientation() {
    let (run, compiler) = checked(include_str!(
        "../../../../lean/examples/real_line_witnesses/statement.lit"
    ));
    let lean = compiler.compile_run(&run, "real_line_comparisons").unwrap();
    assert!(lean.contains("Litex.existsRealAbove"));
    assert!(lean.contains("Litex.existsRealBelow"));
    assert!(lean.contains("Litex.ltNotSame"));
    assert!(lean.contains("Litex.ltToLe"));
}

#[test]
fn real_line_comparison_rejects_missing_membership_child() {
    let (mut run, compiler) = checked("forall c R:\n    exist x R st {x > c}\n");
    real_line_requirements(&mut forall(&mut run).proved_then_facts[0].verify_result)
        .1
        .clear();
    assert_eq!(
        compiler
            .compile_run(&run, "missing_comparison_child")
            .unwrap_err()
            .route,
        "Exist/RealLineComparisonRequirements"
    );
}

#[test]
fn real_line_two_binder_rule_rejects_extra_requirements() {
    let (mut run, compiler) =
        checked("forall c R:\n    exist x R st {x > c}\n    exist x, y R st {x > y}\n");
    let (one, two) = forall(&mut run).proved_then_facts.split_at_mut(1);
    *real_line_requirements(&mut two[0].verify_result).0 =
        real_line_requirements(&mut one[0].verify_result).0.clone();
    assert_eq!(
        compiler
            .compile_run(&run, "extra_comparison_requirement")
            .unwrap_err()
            .route,
        "Exist/RealLineComparisonRequirements"
    );
}
