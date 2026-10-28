//! Finite real suprema/infima consume proved legacy extremal certificates.
use super::function_limit::function_limit_exists;
use super::sequence_limit::{identifier, real};
use super::well_defined_results::verify_obj::*;
use crate::prelude::*;

impl Runtime {
    pub(crate) fn real_bound_certificate(
        &mut self,
        set: Obj,
        value: Obj,
        direction: RealBoundDirection,
    ) -> AtomicFact {
        NormalAtomicFact {
            fact_id: self.global_ids.allocate_fact_id(),
            predicate: AtomicName::plain(
                match direction {
                    RealBoundDirection::Upper => "is_real_least_upper_bound",
                    RealBoundDirection::Lower => "is_real_greatest_lower_bound",
                }
                .into(),
            ),
            body: vec![set, value],
            line_file: None,
        }
        .into()
    }
    pub(crate) fn real_bound_existence(&mut self, set: Obj, direction: RealBoundDirection) -> Fact {
        let value = self.fresh_internal_param();
        let candidate = self.real_bound_certificate(set, identifier(&value), direction);
        function_limit_exists(self, value, real(), vec![candidate])
    }
    pub(crate) fn known_real_bound_candidates(
        &self,
        direction: RealBoundDirection,
    ) -> Vec<NormalAtomicFact> {
        let name = match direction {
            RealBoundDirection::Upper => "is_real_least_upper_bound",
            RealBoundDirection::Lower => "is_real_greatest_lower_bound",
        };
        let key = (AtomicName::plain(name.into()), true);
        let mut result = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(facts) = env
                .facts
                .known_atomic_except_equality_facts
                .by_prop
                .get(&key)
            {
                for fact in facts {
                    if let AtomicFact::NormalAtomicFact(f) = fact {
                        if f.body.len() == 2 {
                            result.push(f.clone());
                        }
                    }
                }
            }
        }
        result
    }

    pub(crate) fn verify_bound_operator_well_definedness(
        &mut self,
        value: &BoundOperator,
        state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let (obj, set, direction) = match value {
            BoundOperator::Supremum(x) => (
                Obj::from(x.clone()),
                x.set.as_ref(),
                RealBoundDirection::Upper,
            ),
            BoundOperator::Infimum(x) => (
                Obj::from(x.clone()),
                x.set.as_ref(),
                RealBoundDirection::Lower,
            ),
        };
        let set_wd = match self.verify_obj_well_definedness(set, state)? {
            VerifyObjWellDefinedResult::Success(proof) => proof,
            VerifyObjWellDefinedResult::Failed { reason, .. } => {
                return Ok(VerifyObjWellDefinedResult::Failed { obj, reason })
            }
        };
        let requirement = Fact::from(SubsetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: set.clone(),
            right: real(),
            line_file: None,
        });
        let real_set = self.verify_fact(&requirement, state)?;
        if real_set.is_failed() {
            return Ok(bound_failure(obj, real_set, direction));
        }
        let mut selected = None;
        for candidate in self.known_real_bound_candidates(direction) {
            let candidate =
                self.real_bound_certificate(set.clone(), candidate.body[1].clone(), direction);
            if self
                .lookup_known_atomic_premise(candidate.clone())
                .is_some()
            {
                selected = Some(self.verify_fact(&candidate.into(), state)?);
                break;
            }
        }
        let selection = match selected {
            Some(proof) => proof,
            None => {
                let existence = self.real_bound_existence(set.clone(), direction);
                self.verify_fact(&existence, state)?
            }
        };
        if selection.is_failed() {
            return Ok(bound_failure(obj, selection, direction));
        }
        // Every valid certificate includes a nonempty real set in its contract.
        // Selection keeps that candidate/existence evidence, without guessing a value.
        let proof = match value {
            BoundOperator::Supremum(_) => {
                BoundOperatorObjWellDefinedProofByDef::Supremum(SupremumObjWellDefinedProof {
                    set_wd: Box::new(set_wd),
                    real_set: Box::new(real_set),
                    selection: Box::new(selection),
                })
            }
            BoundOperator::Infimum(_) => {
                BoundOperatorObjWellDefinedProofByDef::Infimum(InfimumObjWellDefinedProof {
                    set_wd: Box::new(set_wd),
                    real_set: Box::new(real_set),
                    selection: Box::new(selection),
                })
            }
        };
        Ok(VerifyObjWellDefinedResult::Success(
            ObjWellDefinedProof::by_def(self.result_detail(), &(obj), None, || {
                ObjWellDefinedProofByDef::BoundOperator(proof)
            }),
        ))
    }
}
fn bound_failure(
    obj: Obj,
    result: VerifyFactResult,
    direction: RealBoundDirection,
) -> VerifyObjWellDefinedResult {
    let reason = match direction {
        RealBoundDirection::Upper => FailToVerifyBoundOperatorObjWellDefinedResult::Supremum(
            FailToVerifySupremumObjWellDefined {
                obj: obj.clone(),
                result: Box::new(result),
            },
        ),
        RealBoundDirection::Lower => FailToVerifyBoundOperatorObjWellDefinedResult::Infimum(
            FailToVerifyInfimumObjWellDefined {
                obj: obj.clone(),
                result: Box::new(result),
            },
        ),
    };
    VerifyObjWellDefinedResult::Failed {
        obj,
        reason: FailToVerifyObjWellDefinedResult::BoundOperator(reason),
    }
}
