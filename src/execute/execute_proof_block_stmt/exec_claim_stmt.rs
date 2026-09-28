use super::helper::{
    claim_proof_verify_state, claim_store_goal_fact, claim_verify_goal_fact, run_proof_body_stmts,
};
use super::result::{
    ExecClaimStmtFailed, ExecClaimStmtResult, ExecClaimStmtSuccess, ExecProofBlockStmtResult,
};
use crate::ast::fact::{Fact, ForallFact};
use crate::ast::stmt::{ClaimStmt, Stmt};
use crate::execute::exec_stmt_result::ExecStmtResult;
use crate::execute::execute_fact_stmt::VerifyFactResult;
use crate::runtime::{Runtime, RuntimeResult};

// claim: prove `? fact` in a child scope; store only the target outside.
//
// Condition: goal is well-defined; body stmts succeed; conclusions hold in
// the local env (forall then-clauses, or the goal itself).
// After: parent gets the goal fact (helpers stay in discarded local_env).
//
// Example:
//   claim:
//       ? 1 = 1
pub fn exec_claim_stmt(
    runtime: &mut Runtime,
    stmt: &ClaimStmt,
) -> RuntimeResult<ExecProofBlockStmtResult> {
    if matches!(stmt.fact, Fact::ForallFactWithIff(_)) {
        return Ok(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Failed(
            ExecClaimStmtFailed::GoalUnsupported(
                "claim: forall ... <=> goals are not supported".to_string(),
            ),
        )));
    }

    let goal_wd =
        runtime.verify_fact_well_definedness(&stmt.fact, claim_proof_verify_state())?;
    if goal_wd.is_failed() {
        return Ok(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Failed(
            ExecClaimStmtFailed::GoalWd(goal_wd),
        )));
    }

    let (local_outcome, local_env) = runtime.run_in_local_env_and_take_env(|rt| {
        match &stmt.fact {
            Fact::ForallFact(forall) => exec_claim_forall_body(rt, forall, &stmt.proof),
            _ => {
                let proof_steps = match run_proof_body_stmts(rt, &stmt.proof)? {
                    Ok(steps) => steps,
                    Err(failed) => return Ok(Err(ExecClaimStmtFailed::ProofBody(failed))),
                };
                let proof = claim_verify_goal_fact(rt, &stmt.fact)?;
                if proof.is_failed() {
                    return Ok(Err(ExecClaimStmtFailed::Conclusion {
                        index: 0,
                        result: proof,
                    }));
                }
                Ok(Ok((proof_steps, vec![proof])))
            }
        }
    })?;

    let (proof_steps, conclusion_proofs) = match local_outcome {
        Ok(v) => v,
        Err(failed) => {
            return Ok(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Failed(
                failed,
            )));
        }
    };

    let stored = match claim_store_goal_fact(runtime, &stmt.fact)? {
        Ok(s) => s,
        Err(msg) => {
            return Ok(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Failed(
                ExecClaimStmtFailed::Store(msg),
            )));
        }
    };

    Ok(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Success(
        ExecClaimStmtSuccess {
            goal_wd,
            proof_steps,
            conclusion_proofs,
            local_env,
            stored,
        },
    )))
}

fn exec_claim_forall_body(
    runtime: &mut Runtime,
    forall: &ForallFact,
    proof: &[Stmt],
) -> RuntimeResult<Result<(Vec<ExecStmtResult>, Vec<VerifyFactResult>), ExecClaimStmtFailed>> {
    if runtime
        .introduce_typed_parameters(&forall.typed_parameters, claim_proof_verify_state())?
        .is_err()
    {
        return Ok(Err(ExecClaimStmtFailed::Introduce(
            "claim: failed to introduce forall parameters".to_string(),
        )));
    }

    for dom in &forall.dom_facts {
        let wd = runtime.verify_fact_well_definedness(dom, claim_proof_verify_state())?;
        if wd.is_failed() {
            return Ok(Err(ExecClaimStmtFailed::Introduce(
                "claim: forall domain fact is not well-defined".to_string(),
            )));
        }
        let _ = runtime.store_fact_and_infer(dom)?;
    }

    let proof_steps = match run_proof_body_stmts(runtime, proof)? {
        Ok(steps) => steps,
        Err(failed) => return Ok(Err(ExecClaimStmtFailed::ProofBody(failed))),
    };

    let mut conclusion_proofs = Vec::with_capacity(forall.then_facts.len());
    for (index, then) in forall.then_facts.iter().enumerate() {
        let then_fact: Fact = then.clone().into();
        let proof = claim_verify_goal_fact(runtime, &then_fact)?;
        if proof.is_failed() {
            return Ok(Err(ExecClaimStmtFailed::Conclusion { index, result: proof }));
        }
        conclusion_proofs.push(proof);
    }

    Ok(Ok((proof_steps, conclusion_proofs)))
}
