use crate::execute::execute_by_stmt::{
    ExecByStmtResult, ExecByThmStmtResult, ExecByThmStmtSuccess, ExecReleaseThmStmtResult,
    ExecReleaseThmStmtSuccess,
};
use crate::execute::execute_proof_block_stmt::{
    ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult,
};
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

const UNIQUE: &str =
    include_str!("../../../lean/examples/function_limit_at_unique_by_theorem/statement.lit");
const EXISTS: &str =
    include_str!("../../../lean/examples/function_limit_at_exists_by_theorem/statement.lit");
const SELECTED: &str =
    include_str!("../../../lean/examples/function_limit_at_selected_by_theorem/statement.lit");

pub(super) fn step(run: &mut RunLitexCodeResult) -> &mut ExecStmtResult {
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Success(
        p,
    ))) = &mut run.statement_results[0]
    else {
        panic!("claim")
    };
    let ExecClaimBodyProof::Forall(p) = &mut p.body else {
        panic!("forall")
    };
    &mut p.proof_steps[0]
}

fn invocation(run: &mut RunLitexCodeResult) -> &mut ExecByThmStmtSuccess {
    let ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(p))) = step(run)
    else {
        panic!("by theorem")
    };
    p
}

fn release(run: &mut RunLitexCodeResult) -> &mut ExecReleaseThmStmtSuccess {
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(p),
    )) = step(run)
    else {
        panic!("release theorem")
    };
    p
}

#[test]
fn explicit_limit_uniqueness_replays_all_five_approaches() {
    for source in [
        UNIQUE,
        include_str!("../../../lean/examples/function_limit_left_unique_by_theorem/statement.lit"),
        include_str!("../../../lean/examples/function_limit_right_unique_by_theorem/statement.lit"),
        include_str!(
            "../../../lean/examples/function_limit_pos_inf_unique_by_theorem/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/function_limit_neg_inf_unique_by_theorem/statement.lit"
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "explicit_limit_unique")
            .unwrap()
            .contains("FunctionLimitCandidatesEqual"));
    }
}

#[test]
fn explicit_limit_existence_replays_all_five_approaches() {
    for source in [
        EXISTS,
        include_str!("../../../lean/examples/function_limit_left_exists_by_theorem/statement.lit"),
        include_str!("../../../lean/examples/function_limit_right_exists_by_theorem/statement.lit"),
        include_str!(
            "../../../lean/examples/function_limit_pos_inf_exists_by_theorem/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/function_limit_neg_inf_exists_by_theorem/statement.lit"
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "explicit_limit_exists")
            .unwrap()
            .contains("FunctionLimitExists"));
    }
}

#[test]
fn explicit_limit_selection_replays_all_five_approaches() {
    for source in [
        SELECTED,
        include_str!(
            "../../../lean/examples/function_limit_left_selected_by_theorem/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/function_limit_right_selected_by_theorem/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/function_limit_pos_inf_selected_by_theorem/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/function_limit_neg_inf_selected_by_theorem/statement.lit"
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "explicit_limit_selected")
            .unwrap()
            .contains("FunctionLimitSelected"));
    }
}

#[test]
fn explicit_limit_uniqueness_rejects_changed_evidence_and_candidates() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(UNIQUE);
        let p = invocation(&mut run);
        match mutation {
            0 => p.dom_proofs.swap(0, 1),
            1 => {
                p.dom_stores.pop();
            }
            2 => {
                let Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f)) =
                    p.builtin.as_mut().unwrap().requirements.last_mut().unwrap()
                else {
                    panic!("candidate")
                };
                f.approach = LimitApproach::AtPositiveInfinity;
            }
            _ => p.builtin.as_mut().unwrap().arguments[0] = Obj::StandardSet(StandardSet::R),
        }
        compiler
            .compile_run(&run, "changed_limit_invocation")
            .expect_err("original invocation and every ordered premise required");
    }
}

#[test]
fn explicit_limit_existence_rejects_a_missing_candidate_proof() {
    let (mut run, compiler) = super::execute(EXISTS);
    release(&mut run).dom_proofs.pop();
    compiler
        .compile_run(&run, "missing_limit_candidate")
        .expect_err("original candidate required");
}

#[test]
fn explicit_limit_selection_rejects_a_different_selected_approach() {
    let (mut run, compiler) = super::execute(SELECTED);
    let p = release(&mut run).builtin.as_mut().unwrap();
    let Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f)) = &mut p.conclusions[0] else {
        panic!("selected candidate")
    };
    let Obj::LimitOperator(LimitOperator::Function(p)) = &mut f.value else {
        panic!("selector")
    };
    p.approach = LimitApproach::AtNegativeInfinity;
    compiler
        .compile_run(&run, "changed_selected_approach")
        .expect_err("selected object keeps its source function and approach");
}
