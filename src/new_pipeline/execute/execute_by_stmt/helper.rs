use crate::new_pipeline::ast::fact::{
    and_chain_as_fact, negate_atomic_fact, AndChainAtomicFact, AtomicFact, Fact, OrFact,
};
use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::ast::stmt::Stmt;
use crate::new_pipeline::execute::execute_by_stmt::result::{
    ByContradictionClosingFailed, ByContradictionClosingSuccess, ByProofBodyFailed,
    ByProofStepResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::{
    VerifyFactResult, VerifyFactWellDefinedResult, VerifyState,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::StoreFactAndInferResult;

pub(super) fn proof_verify_state() -> VerifyState {
    VerifyState {
        can_use_forall_fact: true,
        can_use_rewrite: true,
        store_well_defined_fact: true,
    }
}

pub(super) fn run_fact_only_proof_steps(
    runtime: &mut Runtime,
    proof: &[Stmt],
) -> RuntimeResult<Result<Vec<ByProofStepResult>, ByProofBodyFailed>> {
    let mut steps = Vec::with_capacity(proof.len());
    for (step_index, stmt) in proof.iter().enumerate() {
        let Stmt::Fact(fact) = stmt else {
            return Ok(Err(ByProofBodyFailed::NonFactStmt { step_index }));
        };
        let result = runtime.execute_fact_statement(fact)?;
        if result.is_failed() {
            return Ok(Err(ByProofBodyFailed::FactStep { step_index, result }));
        }
        steps.push(ByProofStepResult::Fact(result));
    }
    Ok(Ok(steps))
}

pub(super) fn assume_fact(
    runtime: &mut Runtime,
    fact: &Fact,
) -> RuntimeResult<Result<StoreFactAndInferResult, String>> {
    let wd = runtime.verify_fact_well_definedness(fact, proof_verify_state())?;
    if wd.is_failed() {
        return Ok(Err("assumption well-definedness failed".to_string()));
    }
    Ok(Ok(runtime.store_fact_and_infer(fact)?))
}

pub(super) fn verify_goal_fact(
    runtime: &mut Runtime,
    fact: &Fact,
) -> RuntimeResult<VerifyFactResult> {
    runtime.verify_fact(fact, proof_verify_state())
}

pub(super) fn store_goal_fact(
    runtime: &mut Runtime,
    fact: &Fact,
) -> RuntimeResult<Result<StoreFactAndInferResult, String>> {
    let wd = runtime.verify_fact_well_definedness(fact, proof_verify_state())?;
    if let VerifyFactWellDefinedResult::Failed(_) = &wd {
        return Ok(Err("goal well-definedness failed at store".to_string()));
    }
    Ok(Ok(runtime.store_fact_and_infer(fact)?))
}

pub(super) fn negate_fact_for_contra(runtime: &mut Runtime, fact: &Fact) -> Result<Fact, String> {
    match fact {
        Fact::AtomicFact(atomic) => {
            let neg = negate_atomic_fact(atomic, runtime.ids.allocate_fact_id())
                .ok_or_else(|| "by contra: cannot negate this atomic fact".to_string())?;
            Ok(Fact::AtomicFact(neg))
        }
        _ => Err(
            "by contra: first cut only supports atomic `?` goals (negate not wired for compound facts)"
                .to_string(),
        ),
    }
}

pub(super) fn close_by_contradiction(
    runtime: &mut Runtime,
    impossible: &AtomicFact,
) -> RuntimeResult<Result<ByContradictionClosingSuccess, ByContradictionClosingFailed>> {
    let impossible_fact: Fact = impossible.clone().into();
    let impossible_proof = verify_goal_fact(runtime, &impossible_fact)?;
    if impossible_proof.is_failed() {
        return Ok(Err(ByContradictionClosingFailed::Impossible(
            impossible_proof,
        )));
    }
    let Some(negated_atomic) =
        negate_atomic_fact(impossible, runtime.ids.allocate_fact_id())
    else {
        return Ok(Err(
            ByContradictionClosingFailed::NegateImpossibleUnsupported(
                "cannot negate impossible atomic fact".to_string(),
            ),
        ));
    };
    let negated_fact: Fact = negated_atomic.into();
    let negated_proof = verify_goal_fact(runtime, &negated_fact)?;
    if negated_proof.is_failed() {
        return Ok(Err(ByContradictionClosingFailed::NegatedImpossible(
            negated_proof,
        )));
    }
    Ok(Ok(ByContradictionClosingSuccess {
        impossible: impossible_proof,
        negated_impossible: negated_proof,
    }))
}

pub(super) fn or_fact_from_and_chains(
    runtime: &mut Runtime,
    branches: &[AndChainAtomicFact],
    line_file: &LineFile,
) -> OrFact {
    OrFact {
        fact_id: runtime.ids.allocate_fact_id(),
        facts: branches.to_vec(),
        line_file: Some(line_file.clone()),
    }
}

pub(super) fn and_chain_fact(branch: &AndChainAtomicFact) -> Fact {
    and_chain_as_fact(branch)
}
