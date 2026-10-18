use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::LitexToLeanCompiler;
use crate::execute::execute_by_stmt::{
    ByCasesBranchClosingSuccess, ExecByCasesStmtResult, ExecByCasesStmtSuccess,
    ExecByContraStmtResult, ExecByContraStmtSuccess,
};
use crate::prelude::*;

const CONTRA: &str = "have a C\nby contra:\n    ? a = a\n    a = a\n    impossible a = a\na = a\n";
const CASES: &str = "have a R\nby cases:\n    ? a = a\n    case a = 0:\n        a = a\n    case a != 0:\n        a = a\na = a\n";

fn checked(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let result = runtime.run_litex_code(source).expect("source execution");
    assert!(
        result.success && result.session_error.is_none(),
        "source rejected: {source}"
    );
    (result, LitexToLeanCompiler::new(runtime))
}

fn contra(result: &mut RunLitexCodeResult) -> &mut ExecByContraStmtSuccess {
    let ExecStmtResult::By(ExecByStmtResult::Contra(ExecByContraStmtResult::Success(proof))) =
        &mut result.statement_results[1]
    else {
        panic!("original contra result")
    };
    proof
}

fn cases(result: &mut RunLitexCodeResult) -> &mut ExecByCasesStmtSuccess {
    let ExecStmtResult::By(ExecByStmtResult::Cases(ExecByCasesStmtResult::Success(proof))) =
        &mut result.statement_results[1]
    else {
        panic!("original cases result")
    };
    proof
}

#[test]
fn contra_replays_original_steps_and_exports_the_goal() {
    let (mut result, compiler) = checked(CONTRA);
    let proof = contra(&mut result);
    assert_eq!(proof.proof_steps.len(), 1);
    let id = proof.reverse_assumption_fact_id;
    let lean = compiler
        .compile_run(&result, "contra_original_steps")
        .expect("contra compiles");
    assert!(lean.contains(&format!("intro h_{}", id.value())));
}

#[test]
fn contra_negative_goal_uses_double_negation_elimination() {
    let (result, compiler) = checked("by contra:\n    ? 1 != 0\n    impossible 1 = 0\n");
    let lean = compiler
        .compile_run(&result, "contra_negative_goal")
        .expect("negative goal compiles");
    assert!(lean.contains("Classical.byContradiction _litex_negated_goal"));
}

#[test]
fn contra_rejects_changed_reverse_assumption() {
    let (mut result, compiler) = checked(CONTRA);
    let proof = contra(&mut result);
    proof.reverse_assumption = proof.goal.clone();
    assert_eq!(
        compiler
            .compile_run(&result, "contra_wrong_reverse")
            .unwrap_err()
            .route,
        "By/NegationSubject"
    );
}

#[test]
fn contra_rejects_missing_assumption_capture() {
    let (mut result, compiler) = checked(CONTRA);
    contra(&mut result).assumption_components.clear();
    assert_eq!(
        compiler
            .compile_run(&result, "contra_missing_capture")
            .unwrap_err()
            .route,
        "By/AssumptionCapture"
    );
}

#[test]
fn contra_rejects_changed_impossible_subject() {
    let (mut result, compiler) = checked(CONTRA);
    let proof = contra(&mut result);
    proof.closing.impossible_fact = proof.reverse_assumption.clone();
    assert_eq!(
        compiler
            .compile_run(&result, "contra_wrong_closing")
            .unwrap_err()
            .route,
        "By/ImpossibleSubject"
    );
}

#[test]
fn cases_replays_complementary_coverage_and_both_original_branches() {
    let (mut result, compiler) = checked(CASES);
    let proof = cases(&mut result);
    assert_eq!(proof.branches.len(), 2);
    let ids: Vec<_> = proof
        .branches
        .iter()
        .map(|p| p.assumption_fact_id)
        .collect();
    let lean = compiler
        .compile_run(&result, "cases_original_branches")
        .expect("cases compile");
    assert!(lean.contains("Classical.em"));
    for id in ids {
        assert!(lean.contains(&format!("fun (h_{} :", id.value())));
    }
}

#[test]
fn cases_rejects_reordered_branches() {
    let (mut result, compiler) = checked(CASES);
    cases(&mut result).branches.swap(0, 1);
    assert_eq!(
        compiler
            .compile_run(&result, "cases_wrong_order")
            .unwrap_err()
            .route,
        "Cases/CoverageBranches"
    );
}

#[test]
fn cases_rejects_missing_branch_conclusion() {
    let (mut result, compiler) = checked(CASES);
    let ByCasesBranchClosingSuccess::ThenFacts { proved_then_facts } =
        &mut cases(&mut result).branches[0].closing
    else {
        panic!("ordinary branch closing")
    };
    proved_then_facts.clear();
    assert_eq!(
        compiler
            .compile_run(&result, "cases_missing_conclusion")
            .unwrap_err()
            .route,
        "Cases/ClosingArity"
    );
}

#[test]
fn cases_rejects_missing_output_formation() {
    let (mut result, compiler) = checked(CASES);
    cases(&mut result).stored_wd.clear();
    assert_eq!(
        compiler
            .compile_run(&result, "cases_missing_output_wd")
            .unwrap_err()
            .route,
        "Cases/Stages"
    );
}

#[test]
fn branch_assumptions_are_not_visible_after_the_cases_statement() {
    let (mut result, compiler) = checked(CASES);
    let id = cases(&mut result).branches[0].assumption_fact_id;
    let completed = SourcePosition::new(
        None,
        SourceOwner::Run(&result),
        result.statement_results.len(),
    );
    assert!(compiler.cited_fact_reference(id, &completed).is_err());
}

#[test]
fn contra_goal_is_not_visible_before_its_caller_output_store() {
    let (mut result, compiler) = checked(CONTRA);
    let id = contra(&mut result).stored.primary_fact_id();
    let run = SourcePosition::new(None, SourceOwner::Run(&result), 1);
    let output_wd_complete = SourcePosition::new(
        Some(&run),
        SourceOwner::Statement(&result.statement_results[1]),
        3,
    );
    assert!(compiler
        .cited_fact_reference(id, &output_wd_complete)
        .is_err());
    let stored = SourcePosition {
        before: 4,
        ..output_wd_complete
    };
    assert!(compiler.cited_fact_reference(id, &stored).is_ok());
}

#[test]
fn cases_goal_is_not_visible_before_its_caller_output_store() {
    let (mut result, compiler) = checked(CASES);
    let proof = cases(&mut result);
    let id = proof.stored[0].primary_fact_id();
    let head = proof.then_facts_wd.len() + 2;
    let run = SourcePosition::new(None, SourceOwner::Run(&result), 1);
    let output_wd_complete = SourcePosition::new(
        Some(&run),
        SourceOwner::Statement(&result.statement_results[1]),
        head + 1,
    );
    assert!(compiler
        .cited_fact_reference(id, &output_wd_complete)
        .is_err());
    let stored = SourcePosition {
        before: head + 2,
        ..output_wd_complete
    };
    assert!(compiler.cited_fact_reference(id, &stored).is_ok());
}

#[test]
fn a_case_cannot_cite_another_branch_assumption() {
    let (mut result, compiler) = checked(CASES);
    let id = cases(&mut result).branches[0].assumption_fact_id;
    let ExecStmtResult::By(ExecByStmtResult::Cases(ExecByCasesStmtResult::Success(proof))) =
        &result.statement_results[1]
    else {
        panic!("cases result")
    };
    let run = SourcePosition::new(None, SourceOwner::Run(&result), 1);
    let caller = SourcePosition::new(
        Some(&run),
        SourceOwner::Statement(&result.statement_results[1]),
        proof.then_facts_wd.len() + 1,
    );
    let sibling = SourcePosition::new(
        Some(&caller),
        SourceOwner::CasesBranch(&proof.branches[1]),
        2,
    );
    assert!(compiler.cited_fact_reference(id, &sibling).is_err());
}
