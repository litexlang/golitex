use crate::ast::fact::{
    and_chain_as_fact, negate_atomic_fact, AndChainAtomicFact, AtomicFact, Fact, OrFact,
};
use crate::ast::line_file::SourceLine;
use crate::ast::stmt::Stmt;
use crate::execute::execute_by_stmt::result::{
    ByContradictionClosingFailed, ByContradictionClosingSuccess, ByProofBodyFailed,
    ByProofStepResult,
};
use crate::execute::execute_fact_stmt::{
    VerifyFactResult, VerifyFactWellDefinedResult, VerifyState,
};
use crate::runtime::{FactId, Runtime, RuntimeResult};
use crate::store_fact_and_infer::StoreFactAndInferResult;

pub(crate) fn proof_verify_state() -> VerifyState {
    VerifyState {
        can_use_builtin_rule_round: VerifyState::TOP_BUILTIN_RULE_ROUND,
        can_use_def_and_known_forall_and_known_strategy: true,
        can_use_rewrite: true,
        store_well_defined_fact: true,
    }
}

pub(crate) fn run_fact_only_proof_steps(
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
    let wd = runtime.verify_fact_well_definedness(fact, proof_verify_state())?;
    if let VerifyFactWellDefinedResult::Failed(_) = &wd {
        return Ok(Err("goal well-definedness failed at store".to_string()));
    }
    Ok(Ok(runtime.store_fact_and_infer(fact)?))
}

pub(super) fn negate_fact_for_contra(runtime: &mut Runtime, fact: &Fact) -> Result<Fact, String> {
    match fact {
        Fact::AtomicFact(atomic) => {
            let neg = negate_atomic_fact(atomic, runtime.global_ids.allocate_fact_id())
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
        negate_atomic_fact(impossible, runtime.global_ids.allocate_fact_id())
    else {
        return Ok(Err(
            ByContradictionClosingFailed::NegateImpossibleUnsupported(
                "cannot negate impossible atomic fact".to_string(),
            ),
        ));
    };
    let negated_fact: Fact = negated_atomic.clone().into();
    let negated_proof = verify_goal_fact(runtime, &negated_fact)?;
    if negated_proof.is_failed() {
        return Ok(Err(ByContradictionClosingFailed::NegatedImpossible(
            negated_proof,
        )));
    }
    let impossible_fact_id = lookup_known_atomic_fact_id(runtime, impossible);
    let negated_impossible_fact_id = lookup_known_atomic_fact_id(runtime, &negated_atomic);
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

pub(super) fn lookup_known_atomic_fact_id(
    runtime: &Runtime,
    atomic: &AtomicFact,
) -> Option<FactId> {
    let target = atomic.ir();
    for (id, fact) in &runtime.top_exec_env().facts.facts_by_id {
        if let Fact::AtomicFact(known) = fact {
            if known.ir() == target {
                return Some(*id);
            }
        }
    }
    None
}
