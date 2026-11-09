//! Borrow an exact earlier atomic formation; this reader never searches for a new fact.
use super::source_position::{claim_steps, local_steps, named_steps, SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_by_stmt::{
    ExecByStmtResult, ExecByThmStmtResult, ExecReleaseThmStmtResult,
};
use crate::execute::execute_proof_block_stmt::ExecClaimBodyProof;
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

impl LitexToLeanCompiler {
    /// An obtained atomic clause is renamed, rather than re-verified. Its
    /// argument can still have an earlier exact carrier store from that same
    /// obtain. Consume that original store without inventing a predicate WD.
    pub(super) fn cited_obtained_argument_membership(
        &self,
        id: FactId,
        object: &Obj,
        set: &StandardSet,
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        let (actual, _) = self.cited_fact_reference(id, position)?;
        let Fact::AtomicFact(actual) = actual else {
            return Err(invalid("AtomicSubject"));
        };
        if !atomic_fact_args_ref(actual)
            .iter()
            .any(|arg| arg.ir() == object.ir())
        {
            return Err(invalid("ObtainedArgumentSubject"));
        }
        position.with_visible_obtain(&mut |declaration, _| {
            let stores = match declaration {
                ExecDefineObjStmtResult::ObtainObjFromExistFact(
                    crate::execute::ExecObtainObjFromExistFactStmtResult::Success(p),
                ) => &p.store_and_infer_result,
                ExecDefineObjStmtResult::ObtainObjFromAtomicFact(
                    crate::execute::ExecObtainObjFromAtomicFactStmtResult::Success(p),
                ) => &p.store_and_infer_result,
                ExecDefineObjStmtResult::HaveObjByExistFacts(
                    crate::execute::ExecHaveObjByExistFactsStmtResult::Success(p),
                ) => &p.store_and_infer_result,
                _ => return Ok(None),
            };
            let Some(index) = stores
                .store_and_infer_results
                .iter()
                .position(|stored| stored.primary_fact_id() == id)
            else {
                return Ok(None);
            };
            let StoreFactResult::AtomicFact(stored) = &stores.store_and_infer_results[index].store
            else {
                return Err(invalid("ObtainedAtomic"));
            };
            if stored.fact != *actual || stored.fact.fact_id() != id {
                return Err(invalid("ObtainedIdentity"));
            }
            for member in stores.store_and_infer_results.iter().take(index).rev() {
                let StoreFactResult::AtomicFact(stored) = &member.store else {
                    continue;
                };
                if !matches!(&stored.fact, AtomicFact::InFact(f)
                    if f.element.ir() == object.ir() && f.set == Obj::StandardSet(set.clone()))
                {
                    continue;
                }
                let (checked, reference) =
                    self.cited_fact_reference(member.primary_fact_id(), position)?;
                if !matches!(checked, Fact::AtomicFact(f) if f == &stored.fact) {
                    return Err(invalid("ObtainedCarrierIdentity"));
                }
                return Ok(Some(reference));
            }
            Ok(None)
        })
    }

    pub(super) fn with_cited_atomic_formation<T>(
        &self,
        id: FactId,
        position: &SourcePosition<'_>,
        callback: &mut impl FnMut(
            &AtomicFact,
            &AtomicFactWellDefinedProof,
            &SourcePosition<'_>,
        ) -> Result<T, LeanCompileError>,
    ) -> Result<T, LeanCompileError> {
        // The ordinary source cursor owns publication, visibility and ID validation.
        let (actual, _) = self.cited_fact_reference(id, position)?;
        let Fact::AtomicFact(actual) = actual else {
            return Err(invalid("AtomicSubject"));
        };
        let mut cursor = Some(position);
        while let Some(current) = cursor {
            // Invocation prerequisites are verified, stored and inferred one at
            // a time. Borrow the original earlier verification's WD, before its
            // own store; a matching future prerequisite is never visible here.
            let prerequisites = match current.owner {
                SourceOwner::Call(p) => Some((p.type_proofs.as_slice(), p.dom_proofs.as_slice())),
                SourceOwner::ThmRelease(p) => {
                    Some((p.type_proofs.as_slice(), p.dom_proofs.as_slice()))
                }
                _ => None,
            };
            if let Some((types, domains)) = prerequisites {
                for index in (0..current.before.min(types.len() + domains.len())).rev() {
                    let proof = if index < types.len() {
                        &types[index]
                    } else {
                        &domains[index - types.len()]
                    };
                    let prior = SourcePosition {
                        before: index,
                        ..*current
                    };
                    if let Some(value) = verified_formation(proof, id, actual, &prior, callback)? {
                        return Ok(value);
                    }
                }
            }
            let header = match current.owner {
                SourceOwner::Forall(p) => {
                    Some((&p.fact.typed_parameters, p.assumed_dom_facts.as_slice()))
                }
                SourceOwner::ForallWD(f, p) => Some((
                    &f.typed_parameters,
                    p.detailed_ref().assumed_dom_facts.as_slice(),
                )),
                SourceOwner::Named(p) => match (&p.statement.fact, &p.body) {
                    (Fact::ForallFact(f), ExecDefThmBodyProof::Forall(b)) => {
                        Some((&f.typed_parameters, b.assumed_dom_facts.as_slice()))
                    }
                    _ => None,
                },
                SourceOwner::Claim(p) => match (&p.statement.fact, &p.body) {
                    (Fact::ForallFact(f), ExecClaimBodyProof::Forall(b)) => {
                        Some((&f.typed_parameters, b.assumed_dom_facts.as_slice()))
                    }
                    _ => None,
                },
                _ => None,
            };
            if let Some((parameters, assumptions)) = header {
                let head = parameters
                    .groups
                    .iter()
                    .map(|g| g.params.len())
                    .sum::<usize>();
                for (i, assumed) in assumptions
                    .iter()
                    .take(current.before.saturating_sub(head))
                    .enumerate()
                    .rev()
                {
                    if assumed.store_and_infer.primary_fact_id() != id {
                        continue;
                    }
                    let (
                        StoreFactResult::AtomicFact(stored),
                        FactWellDefinedProof::AtomicExceptEquality(wd),
                    ) = (&assumed.store_and_infer.store, &assumed.well_defined)
                    else {
                        return Err(invalid("AssumptionCapture"));
                    };
                    if stored.fact != *actual || stored.fact.fact_id() != id {
                        return Err(invalid("AssumptionIdentity"));
                    }
                    let prior = SourcePosition {
                        before: head + i,
                        ..*current
                    };
                    return callback(&stored.fact, &wd, &prior);
                }
            }
            let steps = match current.owner {
                SourceOwner::Run(run) | SourceOwner::ModuleFile { run, .. } => {
                    Some((run.statement_results.as_slice(), 0))
                }
                SourceOwner::Named(p) => Some(named_steps(p)),
                SourceOwner::Claim(p) => Some(claim_steps(p)),
                owner => local_steps(owner),
            };
            if let Some((steps, head)) = steps {
                for (i, statement) in steps
                    .iter()
                    .take(current.before.saturating_sub(head))
                    .enumerate()
                    .rev()
                {
                    let prior = SourcePosition {
                        before: head + i,
                        ..*current
                    };
                    if let Some(value) =
                        statement_formation(statement, id, actual, &prior, callback)?
                    {
                        return Ok(value);
                    }
                }
            }
            cursor = current.parent;
        }
        Err(invalid("OriginalProducerProfile"))
    }
}

#[cfg(test)]
#[path = "../../tests/unit/compile_to_lean/round2_cited_formation_tests.rs"]
mod round2_cited_formation_tests;
fn verified_formation<T>(
    result: &VerifyFactResult,
    id: FactId,
    actual: &AtomicFact,
    prior: &SourcePosition<'_>,
    callback: &mut impl FnMut(
        &AtomicFact,
        &AtomicFactWellDefinedProof,
        &SourcePosition<'_>,
    ) -> Result<T, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    let VerifyFactResult::AtomicExceptEquality(result) = result else {
        return Ok(None);
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_ref() else {
        return Ok(None);
    };
    if proof.fact.fact_id() != id {
        return Ok(None);
    }
    if proof.fact != *actual {
        return Err(invalid("PrerequisiteIdentity"));
    }
    let source = SourcePosition::new(Some(prior), SourceOwner::AtomicVerify(proof), 0);
    callback(&proof.fact, &proof.well_defined_proof, &source).map(Some)
}
fn statement_formation<T>(
    statement: &ExecStmtResult,
    id: FactId,
    actual: &AtomicFact,
    prior: &SourcePosition<'_>,
    callback: &mut impl FnMut(
        &AtomicFact,
        &AtomicFactWellDefinedProof,
        &SourcePosition<'_>,
    ) -> Result<T, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    match statement {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(p))
            if p.store_and_infer_result.primary_fact_id() == id =>
        {
            let VerifyFactResult::AtomicExceptEquality(result) = &p.verify_result else {
                return Err(invalid("VerifiedAtomic"));
            };
            let VerifyAtomicExceptEqualityFactResult::Success(p) = result.as_ref() else {
                return Err(invalid("VerifiedSuccess"));
            };
            if p.fact != *actual {
                return Err(invalid("VerifiedIdentity"));
            }
            let source = SourcePosition::new(Some(prior), SourceOwner::AtomicVerify(p), 0);
            callback(&p.fact, &p.well_defined_proof, &source).map(Some)
        }
        ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
            ExecReleaseThmStmtResult::Success(p),
        )) => {
            if p.stored.len() != p.stored_wd.len() {
                return Err(invalid("ReleasedStages"));
            }
            for (index, (stored, wd)) in p.stored.iter().zip(&p.stored_wd).enumerate() {
                if stored.primary_fact_id() != id {
                    continue;
                }
                let (
                    StoreFactResult::AtomicFact(stored),
                    FactWellDefinedProof::AtomicExceptEquality(wd),
                ) = (&stored.store, wd)
                else {
                    return Err(invalid("ReleasedAtomic"));
                };
                if stored.fact != *actual {
                    return Err(invalid("ReleasedIdentity"));
                }
                let scope =
                    SourcePosition::new(Some(prior), SourceOwner::Statement(statement), 2 * index);
                return callback(&stored.fact, wd, &scope).map(Some);
            }
            Ok(None)
        }
        ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(p)))
            if p.stored.primary_fact_id() == id =>
        {
            let (
                StoreFactResult::AtomicFact(stored),
                FactWellDefinedProof::AtomicExceptEquality(wd),
            ) = (&p.stored.store, &p.selected_wd)
            else {
                return Err(invalid("SelectedAtomic"));
            };
            if stored.fact != *actual {
                return Err(invalid("SelectedIdentity"));
            }
            let scope = SourcePosition::new(Some(prior), SourceOwner::Statement(statement), 0);
            callback(&stored.fact, wd, &scope).map(Some)
        }
        _ => Ok(None),
    }
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("CitedAtomicFormation/{stage}"))
}
