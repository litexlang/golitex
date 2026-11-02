use super::helper::{
    and_chain_fact, assume_fact_with_wd, close_by_contradiction, or_fact_from_and_chains,
    proof_verify_state, store_goal_fact_with_wd, verify_goal_fact,
};
use super::result::{
    ByCasesBranchClosingSuccess, ByCasesBranchFailed, ByCasesBranchSuccess,
    ByCasesEnteredBranchFailed, ExecByCasesStmtFailed, ExecByCasesStmtResult,
    ExecByCasesStmtSuccess, ExecByStmtResult,
};
use super::ByCasesBranchFailure;
use crate::ast::fact::{AtomicFact, Fact};
use crate::ast::stmt::ByCasesStmt;
use crate::execute::execute_fact_stmt::{AssumeDomFactResult, ProveAndStoreThenFactResult};
use crate::execute::execute_proof_block_stmt::run_proof_body_stmts;
use crate::runtime::{FactId, Runtime, RuntimeResult};

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
                    ExecByCasesStmtFailed::Branch {
                        then_facts_wd,
                        coverage,
                        branches,
                        index,
                        failed,
                    },
                )));
            }
        }
    }

    let mut stored_wd = Vec::with_capacity(stmt.then_facts.len());
    let mut stored = Vec::with_capacity(stmt.then_facts.len());
    for (index, fact) in stmt.then_facts.iter().enumerate() {
        match store_goal_fact_with_wd(runtime, fact)? {
            Ok((wd, store)) => {
                stored_wd.push(wd);
                stored.push(store);
            }
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
            stored_wd,
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
        let assumed = match assume_fact_with_wd(rt, &case_fact)? {
            Ok(s) => s,
            Err(msg) => return Ok(Err(CaseBranchCheckFailed::AssumeCase(msg))),
        };
        let assumption_fact_id = assumed.store_and_infer.primary_fact_id();
        let assumption_components = assumed.store_and_infer.atomic_components();
        let proof_steps = match run_proof_body_stmts(rt, &stmt.proofs[index])? {
            Ok(steps) => steps,
            Err(failed) => {
                return Ok(Err(CaseBranchCheckFailed::Entered {
                    assumption_fact_id,
                    assumption_components,
                    assumed,
                    failure: ByCasesEnteredBranchFailed::ProofBody(failed),
                }))
            }
        };
        let closing = if let Some(impossible) = &stmt.impossible_facts[index] {
            match close_by_contradiction(rt, &impossible.clone().into())? {
                Ok(c) => ByCasesBranchClosingSuccess::Impossible(c),
                Err(failed) => {
                    return Ok(Err(CaseBranchCheckFailed::Entered {
                        assumption_fact_id,
                        assumption_components,
                        assumed,
                        failure: ByCasesEnteredBranchFailed::ClosingImpossible {
                            proof_steps,
                            failed,
                        },
                    }));
                }
            }
        } else {
            let mut proved_then_facts = Vec::with_capacity(stmt.then_facts.len());
            for (then_index, then_fact) in stmt.then_facts.iter().enumerate() {
                let proof = verify_goal_fact(rt, then_fact)?;
                if proof.is_failed() {
                    return Ok(Err(CaseBranchCheckFailed::Entered {
                        assumption_fact_id,
                        assumption_components,
                        assumed,
                        failure: ByCasesEnteredBranchFailed::ClosingThen {
                            proof_steps,
                            proved_then_facts,
                            then_index,
                            result: proof,
                        },
                    }));
                }
                let stored = rt.store_fact_and_infer(
                    then_fact,
                    crate::execute::execute_fact_stmt::VerifyState::top_level(),
                )?;
                proved_then_facts.push(ProveAndStoreThenFactResult {
                    verify_result: proof,
                    store_and_infer: stored,
                });
            }
            ByCasesBranchClosingSuccess::ThenFacts { proved_then_facts }
        };
        Ok(Ok((
            assumption_fact_id,
            assumption_components,
            assumed,
            proof_steps,
            closing,
        )))
    })?;

    match outcome {
        Ok((assumption_fact_id, assumption_components, assumed, proof_steps, closing)) => {
            Ok(Ok(ByCasesBranchSuccess {
                assumption,
                assumption_fact_id,
                assumption_components,
                assumption_wd: assumed.well_defined,
                assumptions_stored: assumed.store_and_infer,
                proof_steps,
                closing,
                local_env,
            }))
        }
        Err(CaseBranchCheckFailed::AssumeCase(message)) => {
            Ok(Err(ByCasesBranchFailed::AssumeCase(message)))
        }
        Err(CaseBranchCheckFailed::Entered {
            assumption_fact_id,
            assumption_components,
            assumed,
            failure,
        }) => Ok(Err(ByCasesBranchFailed::AfterAssumption(
            ByCasesBranchFailure {
                assumption,
                assumption_fact_id,
                assumption_components,
                assumed,
                failure,
                local_env,
            },
        ))),
    }
}

enum CaseBranchCheckFailed {
    AssumeCase(String),
    Entered {
        assumption_fact_id: FactId,
        assumption_components: Vec<(FactId, AtomicFact)>,
        assumed: AssumeDomFactResult,
        failure: ByCasesEnteredBranchFailed,
    },
}
