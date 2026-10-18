use crate::compile_to_lean::LitexToLeanCompiler;
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

#[test]
fn geo_named_exist_conclusion_replays_original_cases_and_witnesses() {
    let (run, compiler) = checked(NAMED_CASES);
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
