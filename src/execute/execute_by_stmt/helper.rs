use crate::ast::fact::{and_chain_as_fact, AndChainAtomicFact, Fact, OrFact};
use crate::ast::line_file::SourceLine;
use crate::execute::execute_by_stmt::result::{
    ByContradictionClosingFailed, ByContradictionClosingSuccess,
};
use crate::execute::execute_fact_stmt::{
    VerifyFactResult, VerifyFactWellDefinedResult, VerifyState,
};
use crate::runtime::{FactId, Runtime, RuntimeResult};
use crate::store_fact_and_infer::StoreFactAndInferResult;

pub(super) use super::negate_fact_for_contra::negate_fact_for_contra;

pub(crate) fn proof_verify_state() -> VerifyState {
    VerifyState::top_level()
}

pub(super) fn assume_fact_with_wd(
    runtime: &mut Runtime,
    fact: &Fact,
) -> RuntimeResult<Result<crate::execute::execute_fact_stmt::AssumeDomFactResult, String>> {
    let wd = runtime.verify_fact_well_definedness(fact, proof_verify_state())?;
    let VerifyFactWellDefinedResult::Success(well_defined) = wd else {
        return Ok(Err("assumption well-definedness failed".to_string()));
    };
    let store_and_infer = runtime.store_fact_and_infer(
        fact,
        crate::execute::execute_fact_stmt::VerifyState::top_level(),
    )?;
    Ok(Ok(crate::execute::execute_fact_stmt::AssumeDomFactResult {
        well_defined,
        store_and_infer,
    }))
}

pub(crate) fn verify_goal_fact(
    runtime: &mut Runtime,
    fact: &Fact,
) -> RuntimeResult<VerifyFactResult> {
    runtime.verify_fact(fact, proof_verify_state())
}

pub(crate) fn store_goal_fact(
    runtime: &mut Runtime,
    fact: &Fact,
) -> RuntimeResult<Result<StoreFactAndInferResult, String>> {
    Ok(store_goal_fact_with_wd(runtime, fact)?.map(|(_, stored)| stored))
}

pub(crate) fn store_goal_fact_with_wd(
    runtime: &mut Runtime,
    fact: &Fact,
) -> RuntimeResult<
    Result<
        (
            crate::execute::execute_fact_stmt::FactWellDefinedProof,
            StoreFactAndInferResult,
        ),
        String,
    >,
> {
    let wd = runtime.verify_fact_well_definedness(fact, proof_verify_state())?;
    let VerifyFactWellDefinedResult::Success(wd) = wd else {
        return Ok(Err("goal well-definedness failed at store".to_string()));
    };
    let stored = runtime.store_fact_and_infer(
        fact,
        crate::execute::execute_fact_stmt::VerifyState::top_level(),
    )?;
    Ok(Ok((wd, stored)))
}

pub(super) fn close_by_contradiction(
    runtime: &mut Runtime,
    impossible: &Fact,
) -> RuntimeResult<Result<ByContradictionClosingSuccess, ByContradictionClosingFailed>> {
    let impossible_proof = verify_goal_fact(runtime, impossible)?;
    if impossible_proof.is_failed() {
        return Ok(Err(ByContradictionClosingFailed::Impossible(
            impossible_proof,
        )));
    }
    let negated_fact = match negate_fact_for_contra(runtime, impossible) {
        Ok(fact) => fact,
        Err(message) => {
            return Ok(Err(
                ByContradictionClosingFailed::NegateImpossibleUnsupported(message),
            ));
        }
    };
    let negated_proof = verify_goal_fact(runtime, &negated_fact)?;
    if negated_proof.is_failed() {
        return Ok(Err(ByContradictionClosingFailed::NegatedImpossible(
            negated_proof,
        )));
    }
    let impossible_fact_id = lookup_known_fact_id(runtime, impossible);
    let negated_impossible_fact_id = lookup_known_fact_id(runtime, &negated_fact);
    Ok(Ok(ByContradictionClosingSuccess {
        impossible_fact: impossible.clone(),
        impossible: impossible_proof,
        negated_impossible: negated_proof,
        impossible_fact_id,
        negated_impossible_fact_id,
    }))
}

pub(super) fn or_fact_from_and_chains(
    runtime: &mut Runtime,
    branches: &[AndChainAtomicFact],
    line_file: &SourceLine,
) -> OrFact {
    OrFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        facts: branches.to_vec(),
        line_file: Some(line_file.clone()),
    }
}

pub(super) fn and_chain_fact(branch: &AndChainAtomicFact) -> Fact {
    and_chain_as_fact(branch)
}

fn lookup_known_fact_id(runtime: &Runtime, fact: &Fact) -> Option<FactId> {
    let target = fact.ir();
    for (id, known) in &runtime.top_exec_env().facts.facts_by_id {
        if known.ir() == target {
            return Some(*id);
        }
    }
    None
}

#[cfg(test)]
#[path = "../../../tests/unit/execute/contra_compound_closing/tests.rs"]
mod compound_closing_tests;
