use super::sequence_limit::*;
use super::well_defined_results::verify_obj::*;
use crate::prelude::*;
impl Runtime {
    // Consume only already proved candidates or existence. Never analyze the body.
    pub(crate) fn verify_sequence_liminf_well_definedness(
        &mut self,
        value: &SequenceLiminf,
        state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let obj: Obj = value.clone().into();
        let sequence_wd = match self.verify_obj_well_definedness(&value.sequence, state.clone())? {
            VerifyObjWellDefinedResult::Success(p) => p,
            VerifyObjWellDefinedResult::Failed { reason, .. } => {
                return Ok(VerifyObjWellDefinedResult::Failed { obj, reason })
            }
        };
        let sequence_domain =
            if let Some(source) = self.checked_real_sequence_domain(&value.sequence, state)? {
                RealSequenceDomainProof::CompleteSignature(Box::new(source))
            } else {
                let membership_fact = sequence_membership(self, *value.sequence.clone());
                let membership = self.verify_fact(&membership_fact, state)?;
                if membership.is_failed() {
                    return Ok(liminf_wd_failure(obj, membership));
                }
                RealSequenceDomainProof::Membership(Box::new(membership))
            };
        let mut convergence = None;
        for candidate in self.known_sequence_liminf_candidates() {
            let fact = self.sequence_liminf_candidate(*value.sequence.clone(), candidate.value);
            if let Some(proof) = self.lookup_known_atomic_premise(fact.clone().into()) {
                convergence = Some(SequenceConvergenceProof::Candidate(proof));
                break;
            }
        }
        let convergence = match convergence {
            Some(p) => p,
            None => {
                let existence = self.sequence_liminf_existence(*value.sequence.clone());
                let result = self.verify_fact(&existence, state)?;
                if result.is_failed() {
                    return Ok(liminf_wd_failure(obj, result));
                }
                SequenceConvergenceProof::Existence {
                    fact: existence,
                    proof: Box::new(result),
                }
            }
        };
        Ok(VerifyObjWellDefinedResult::Success(
            ObjWellDefinedProof::ByDef {
                obj,
                proof: ObjWellDefinedProofByDef::LimitOperator(
                    LimitOperatorObjWellDefinedProofByDef::SequenceLiminf(
                        SequenceLiminfObjWellDefinedProof {
                            sequence_wd: Box::new(sequence_wd),
                            sequence_domain,
                            convergence,
                        },
                    ),
                ),
            },
        ))
    }

    pub(crate) fn known_sequence_liminf_candidates(&self) -> Vec<HasSequenceLiminfFact> {
        let key = (
            AtomicName::Plain {
                name: "has_seq_liminf".into(),
            },
            true,
        );
        let mut result = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(facts) = env
                .facts
                .known_atomic_except_equality_facts
                .by_prop
                .get(&key)
            {
                for fact in facts {
                    if let AtomicFact::HasSequenceLiminfFact(f) = fact {
                        result.push(f.clone());
                    }
                }
            }
        }
        result
    }

    pub(crate) fn sequence_liminf_candidate(
        &mut self,
        sequence: Obj,
        value: Obj,
    ) -> HasSequenceLiminfFact {
        HasSequenceLiminfFact {
            fact_id: self.global_ids.allocate_fact_id(),
            sequence,
            value,
            line_file: None,
        }
    }

    pub(crate) fn sequence_liminf_existence(&mut self, sequence: Obj) -> Fact {
        let l = self.fresh_internal_param();
        let candidate = self.sequence_liminf_candidate(sequence, identifier(&l));
        Fact::ExistFact(PlainExistFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: typed(l, real()),
            facts: vec![QuantifierFreeFact::AtomicFact(candidate.into())],
            line_file: None,
        })
    }
}

fn liminf_wd_failure(obj: Obj, result: VerifyFactResult) -> VerifyObjWellDefinedResult {
    VerifyObjWellDefinedResult::Failed {
        obj: obj.clone(),
        reason: FailToVerifyObjWellDefinedResult::LimitOperator(
            FailToVerifyLimitOperatorObjWellDefinedResult::SequenceLiminf(
                FailToVerifySequenceLiminfObjWellDefined {
                    obj,
                    result: Box::new(result),
                },
            ),
        ),
    }
}
