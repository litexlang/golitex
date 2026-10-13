use super::helper::{
    claim_proof_verify_state, claim_store_goal_fact, claim_verify_goal_fact, run_proof_body_stmts,
};
use super::result::{
    ExecClaimBodyProof, ExecClaimForallProof, ExecClaimNonForallProof, ExecClaimStmtFailed,
    ExecClaimStmtResult, ExecClaimStmtSuccess, ExecProofBlockStmtResult,
};
use crate::ast::fact::{Fact, ForallFact};
use crate::ast::stmt::{ClaimStmt, Stmt};
use crate::execute::execute_fact_stmt::{AssumeDomFactResult, VerifyFactWellDefinedResult};
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
//       1 = 1
pub fn exec_claim_stmt(
    runtime: &mut Runtime,
    stmt: &ClaimStmt,
) -> RuntimeResult<ExecProofBlockStmtResult> {
    if matches!(stmt.fact, Fact::ForallFactWithIff(_)) {
        return Ok(ExecProofBlockStmtResult::Claim(
            ExecClaimStmtResult::Failed(ExecClaimStmtFailed::GoalUnsupported(
                "claim: forall ... <=> goals are not supported".to_string(),
            )),
        ));
    }

    let goal_wd = runtime.verify_fact_well_definedness(&stmt.fact, claim_proof_verify_state())?;
    if goal_wd.is_failed() {
        return Ok(ExecProofBlockStmtResult::Claim(
            ExecClaimStmtResult::Failed(ExecClaimStmtFailed::GoalWd(goal_wd)),
        ));
    }

    let (local_outcome, local_env) =
        runtime.run_in_local_env_and_take_env(|rt| match &stmt.fact {
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
                Ok(Ok(ExecClaimBodyProof::NonForall(ExecClaimNonForallProof {
                    proof_steps,
                    conclusion_proof: proof,
                })))
            }
        })?;

    let body = match local_outcome {
        Ok(v) => v,
        Err(failed) => {
            return Ok(ExecProofBlockStmtResult::Claim(
                ExecClaimStmtResult::Failed(failed),
            ));
        }
    };

    let stored = match claim_store_goal_fact(runtime, &stmt.fact)? {
        Ok(s) => s,
        Err(msg) => {
            return Ok(ExecProofBlockStmtResult::Claim(
                ExecClaimStmtResult::Failed(ExecClaimStmtFailed::Store(msg)),
            ));
        }
    };

    Ok(ExecProofBlockStmtResult::Claim(
        ExecClaimStmtResult::Success(ExecClaimStmtSuccess {
            statement: stmt.clone(),
            goal_wd,
            body,
            local_env,
            stored,
        }),
    ))
}

fn exec_claim_forall_body(
    runtime: &mut Runtime,
    forall: &ForallFact,
    proof: &[Stmt],
) -> RuntimeResult<Result<ExecClaimBodyProof, ExecClaimStmtFailed>> {
    let introduced_params = match runtime
        .introduce_typed_parameters(&forall.typed_parameters, claim_proof_verify_state())?
    {
        Ok(introduced) => introduced,
        Err(_) => {
            return Ok(Err(ExecClaimStmtFailed::Introduce(
                "claim: failed to introduce forall parameters".to_string(),
            )))
        }
    };

    let mut assumed_dom_facts = Vec::with_capacity(forall.dom_facts.len());
    for dom in &forall.dom_facts {
        let well_defined =
            match runtime.verify_fact_well_definedness(dom, claim_proof_verify_state())? {
                VerifyFactWellDefinedResult::Success(proof) => proof,
                VerifyFactWellDefinedResult::Failed(_) => {
                    return Ok(Err(ExecClaimStmtFailed::Introduce(
                        "claim: forall domain fact is not well-defined".to_string(),
                    )))
                }
            };
        let store_and_infer = runtime.store_fact_and_infer(
            dom,
            crate::execute::execute_fact_stmt::VerifyState::top_level(),
        )?;
        assumed_dom_facts.push(AssumeDomFactResult {
            well_defined,
            store_and_infer,
        });
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
            return Ok(Err(ExecClaimStmtFailed::Conclusion {
                index,
                result: proof,
            }));
        }
        conclusion_proofs.push(proof);
    }

    Ok(Ok(ExecClaimBodyProof::Forall(ExecClaimForallProof {
        introduced_params,
        assumed_dom_facts,
        proof_steps,
        conclusion_proofs,
    })))
}
