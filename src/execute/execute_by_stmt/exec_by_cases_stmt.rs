use super::helper::{
    and_chain_fact, assume_fact, close_by_contradiction, or_fact_from_and_chains,
    proof_verify_state, store_goal_fact, verify_goal_fact,
};
use super::result::{
    ByCasesBranchClosingSuccess, ByCasesBranchFailed, ByCasesBranchSuccess, ExecByCasesStmtFailed,
    ExecByCasesStmtResult, ExecByCasesStmtSuccess, ExecByStmtResult,
};
use crate::ast::fact::Fact;
use crate::ast::stmt::ByCasesStmt;
use crate::execute::execute_proof_block_stmt::run_proof_body_stmts;
use crate::runtime::{Runtime, RuntimeResult};

pub fn exec_by_cases_stmt(
    runtime: &mut Runtime,
    stmt: &ByCasesStmt,
) -> RuntimeResult<ExecByStmtResult> {
    let n = stmt.cases.len();
    if n == 0
        || stmt.proofs.len() != n
        || stmt.impossible_facts.len() != n
        || stmt.then_facts.is_empty()
    {
        return Ok(ExecByStmtResult::Cases(ExecByCasesStmtResult::Failed(
            ExecByCasesStmtFailed::LengthMismatch(
                "by cases: cases / proofs / impossible_facts length mismatch or empty then_facts"
                    .to_string(),
            ),
        )));
    }

    let mut then_facts_wd = Vec::with_capacity(stmt.then_facts.len());
    for (index, fact) in stmt.then_facts.iter().enumerate() {
        let wd = runtime.verify_fact_well_definedness(fact, proof_verify_state())?;
        if wd.is_failed() {
            return Ok(ExecByStmtResult::Cases(ExecByCasesStmtResult::Failed(
                ExecByCasesStmtFailed::ThenFactWd { index, result: wd },
            )));
        }
        then_facts_wd.push(wd);
    }

    let coverage_fact = Fact::OrFact(or_fact_from_and_chains(
        runtime,
        &stmt.cases,
        &stmt.line_file,
    ));
    let coverage = verify_goal_fact(runtime, &coverage_fact)?;
    if coverage.is_failed() {
        return Ok(ExecByStmtResult::Cases(ExecByCasesStmtResult::Failed(
            ExecByCasesStmtFailed::Coverage(coverage),
        )));
    }

    let mut branches = Vec::with_capacity(n);
    for index in 0..n {
        match exec_one_case_branch(runtime, stmt, index)? {
            Ok(branch) => branches.push(branch),
            Err(failed) => {
                return Ok(ExecByStmtResult::Cases(ExecByCasesStmtResult::Failed(
                    ExecByCasesStmtFailed::Branch { index, failed },
                )));
            }
        }
    }

    let mut stored = Vec::with_capacity(stmt.then_facts.len());
    for (index, fact) in stmt.then_facts.iter().enumerate() {
        match store_goal_fact(runtime, fact)? {
            Ok(s) => stored.push(s),
            Err(message) => {
                return Ok(ExecByStmtResult::Cases(ExecByCasesStmtResult::Failed(
                    ExecByCasesStmtFailed::Store { index, message },
                )));
            }
        }
    }

    Ok(ExecByStmtResult::Cases(ExecByCasesStmtResult::Success(
        ExecByCasesStmtSuccess {
            then_facts_wd,
            coverage,
            branches,
            stored,
        },
    )))
}

fn exec_one_case_branch(
    runtime: &mut Runtime,
    stmt: &ByCasesStmt,
    index: usize,
) -> RuntimeResult<Result<ByCasesBranchSuccess, ByCasesBranchFailed>> {
    let assumption = stmt.cases[index].clone();
    let case_fact = and_chain_fact(&assumption);
    let (outcome, local_env) = runtime.run_in_local_env_and_take_env(|rt| {
        let assumptions_stored = match assume_fact(rt, &case_fact)? {
            Ok(s) => s,
            Err(msg) => return Ok(Err(ByCasesBranchFailed::AssumeCase(msg))),
        };
        let assumption_fact_id = assumptions_stored.primary_fact_id();
        let assumption_components = assumptions_stored.atomic_components();
        let proof_steps = match run_proof_body_stmts(rt, &stmt.proofs[index])? {
            Ok(steps) => steps,
            Err(failed) => return Ok(Err(ByCasesBranchFailed::ProofBody(failed))),
        };
        let closing = if let Some(impossible) = &stmt.impossible_facts[index] {
            match close_by_contradiction(rt, &impossible.clone().into())? {
                Ok(c) => ByCasesBranchClosingSuccess::Impossible(c),
                Err(failed) => {
                    return Ok(Err(ByCasesBranchFailed::ClosingImpossible(failed)));
                }
            }
        } else {
            let mut checks = Vec::with_capacity(stmt.then_facts.len());
            let mut conclusion_fact_ids = Vec::with_capacity(stmt.then_facts.len());
            for (then_index, then_fact) in stmt.then_facts.iter().enumerate() {
                let proof = verify_goal_fact(rt, then_fact)?;
                if proof.is_failed() {
                    return Ok(Err(ByCasesBranchFailed::ClosingThen {
                        then_index,
                        result: proof,
                    }));
                }
                let stored = rt.store_fact_and_infer(
                    then_fact,
                    crate::execute::execute_fact_stmt::VerifyState::top_level(),
                )?;
                conclusion_fact_ids.push(Some(stored.primary_fact_id()));
                checks.push(proof);
            }
            ByCasesBranchClosingSuccess::ThenFacts {
                checks,
                conclusion_fact_ids,
            }
        };
        Ok(Ok((
            assumption_fact_id,
            assumption_components,
            assumptions_stored,
            proof_steps,
            closing,
        )))
    })?;

    match outcome {
        Ok((
            assumption_fact_id,
            assumption_components,
            assumptions_stored,
            proof_steps,
            closing,
        )) => Ok(Ok(ByCasesBranchSuccess {
            assumption,
            assumption_fact_id,
            assumption_components,
            assumptions_stored,
            proof_steps,
            closing,
            local_env,
        })),
        Err(failed) => Ok(Err(failed)),
    }
}
