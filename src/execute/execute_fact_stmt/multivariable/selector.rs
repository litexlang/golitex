//! Proof-consuming selectors. This module never starts limit or derivative search.
use super::super::function_domain::CompleteFunctionDomainProof;
use super::super::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use super::super::well_defined_results::verify_obj::*;
use super::helper::*;
use crate::prelude::*;

pub struct MultivariableSelectorWellDefinedStages {
    pub argument_well_defined: Vec<ObjWellDefinedProof>,
    pub function_domain: Box<CompleteFunctionDomainProof>,
    pub domains:
        Vec<super::super::verify_atomic_fact::well_defined_result::PredicateDomainWellDefinedProof>,
    pub selection: MultivariableSelectorSelectionProof,
}
pub enum MultivariableSelectorSelectionProof {
    Candidate(AtomicExceptEqualityFactKnownProof),
    Existence {
        fact: Fact,
        proof: Box<VerifyFactResult>,
    },
}
pub enum MultivariableSelectorFailureStage {
    Argument(Box<FailToVerifyObjWellDefinedResult>),
    FunctionDomain,
    Domain {
        requirement: Fact,
        proof: Box<VerifyFactResult>,
    },
    Selection {
        requirement: Fact,
        proof: Box<VerifyFactResult>,
    },
}
pub struct MultivariableScalarLimitWellDefinedProof {
    pub stages: MultivariableSelectorWellDefinedStages,
}
pub struct MultivariableScalarLimitWellDefinedFailure {
    pub stage: MultivariableSelectorFailureStage,
}
pub struct MultivariableVectorLimitWellDefinedProof {
    pub stages: MultivariableSelectorWellDefinedStages,
}
pub struct MultivariableVectorLimitWellDefinedFailure {
    pub stage: MultivariableSelectorFailureStage,
}
pub struct PartialDerivativeAtWellDefinedProof {
    pub stages: MultivariableSelectorWellDefinedStages,
}
pub struct PartialDerivativeAtWellDefinedFailure {
    pub stage: MultivariableSelectorFailureStage,
}
pub struct ScalarDifferentialAtWellDefinedProof {
    pub stages: MultivariableSelectorWellDefinedStages,
}
pub struct ScalarDifferentialAtWellDefinedFailure {
    pub stage: MultivariableSelectorFailureStage,
}
pub struct TotalDifferentialAtWellDefinedProof {
    pub stages: MultivariableSelectorWellDefinedStages,
}
pub struct TotalDifferentialAtWellDefinedFailure {
    pub stage: MultivariableSelectorFailureStage,
}
pub struct GradientAtWellDefinedProof {
    pub stages: MultivariableSelectorWellDefinedStages,
}
pub struct GradientAtWellDefinedFailure {
    pub stage: MultivariableSelectorFailureStage,
}
pub struct JacobianAtWellDefinedProof {
    pub stages: MultivariableSelectorWellDefinedStages,
}
pub struct JacobianAtWellDefinedFailure {
    pub stage: MultivariableSelectorFailureStage,
}
pub struct HessianAtWellDefinedProof {
    pub stages: MultivariableSelectorWellDefinedStages,
}
pub struct HessianAtWellDefinedFailure {
    pub stage: MultivariableSelectorFailureStage,
}
pub struct DivergenceAtWellDefinedProof {
    pub stages: MultivariableSelectorWellDefinedStages,
}
pub struct DivergenceAtWellDefinedFailure {
    pub stage: MultivariableSelectorFailureStage,
}
pub struct CurlAtWellDefinedProof {
    pub stages: MultivariableSelectorWellDefinedStages,
}
pub struct CurlAtWellDefinedFailure {
    pub stage: MultivariableSelectorFailureStage,
}
pub struct LaplacianAtWellDefinedProof {
    pub stages: MultivariableSelectorWellDefinedStages,
}
pub struct LaplacianAtWellDefinedFailure {
    pub stage: MultivariableSelectorFailureStage,
}

impl Runtime {
    pub(crate) fn verify_multivariable_selector_well_definedness(
        &mut self,
        obj: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let mut argument_well_defined = Vec::new();
        for arg in obj
            .multivariable_selector_args()
            .expect("multivariable selector")
        {
            match self.verify_obj_well_definedness(arg, state)? {
                VerifyObjWellDefinedResult::Success(p) => argument_well_defined.push(p),
                VerifyObjWellDefinedResult::Failed { reason, .. } => {
                    return Ok(selector_failure(
                        obj,
                        MultivariableSelectorFailureStage::Argument(Box::new(reason)),
                    ))
                }
            }
        }
        let prototype = selector_relation(obj, number(0)).expect("selector candidate shape");
        let Some((function_domain, requirements)) =
            self.multivariable_signature_requirements(&prototype, state)?
        else {
            return Ok(selector_failure(
                obj,
                MultivariableSelectorFailureStage::FunctionDomain,
            ));
        };
        let mut domains = Vec::new();
        for requirement in requirements {
            let proof = self.verify_fact(&requirement, state)?;
            if proof.is_failed() {
                return Ok(selector_failure(
                    obj,
                    MultivariableSelectorFailureStage::Domain {
                        requirement,
                        proof: Box::new(proof),
                    },
                ));
            }
            domains.push(super::super::verify_atomic_fact::well_defined_result::PredicateDomainWellDefinedProof {requirement,result:Box::new(proof)});
        }
        let selection =
            if let Some((_, candidate)) = self.known_multivariable_selector_candidate(obj) {
                MultivariableSelectorSelectionProof::Candidate(candidate)
            } else {
                let requirement = self.multivariable_candidate_existence(&prototype);
                let proof = self.verify_fact(&requirement, state)?;
                if proof.is_failed() {
                    return Ok(selector_failure(
                        obj,
                        MultivariableSelectorFailureStage::Selection {
                            requirement,
                            proof: Box::new(proof),
                        },
                    ));
                }
                MultivariableSelectorSelectionProof::Existence {
                    fact: requirement,
                    proof: Box::new(proof),
                }
            };
        let stages = MultivariableSelectorWellDefinedStages {
            argument_well_defined,
            function_domain: Box::new(function_domain),
            domains,
            selection,
        };
        Ok(VerifyObjWellDefinedResult::Success(
            ObjWellDefinedProof::ByDef {
                obj: obj.clone(),
                proof: selector_success(obj, stages),
            },
        ))
    }
    pub(crate) fn known_multivariable_selector_candidate(
        &mut self,
        obj: &Obj,
    ) -> Option<(Obj, AtomicExceptEqualityFactKnownProof)> {
        let prototype = selector_relation(obj, number(0))?;
        let key = (AtomicName::plain(prototype.predicate_name().into()), true);
        let mut values = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(facts) = env
                .facts
                .known_atomic_except_equality_facts
                .by_prop
                .get(&key)
            {
                for fact in facts {
                    if let AtomicFact::MultivariableAnalysisFact(f) = fact {
                        if let Some(value) = value(&f.relation) {
                            values.push(value.clone());
                        }
                    }
                }
            }
        }
        for value in values {
            let relation = selector_relation(obj, value.clone())?;
            let fact: AtomicFact = MultivariableAnalysisFact {
                fact_id: self.global_ids.allocate_fact_id(),
                relation,
                line_file: None,
            }
            .into();
            if let Some(proof) = self.lookup_known_atomic_premise(fact) {
                return Some((value, proof));
            }
        }
        None
    }
}
fn selector_success(
    obj: &Obj,
    stages: MultivariableSelectorWellDefinedStages,
) -> ObjWellDefinedProofByDef {
    match obj {
        Obj::LimitOperator(LimitOperator::MultivariableScalar(_)) => ObjWellDefinedProofByDef::LimitOperator(LimitOperatorObjWellDefinedProofByDef::MultivariableScalar(MultivariableScalarLimitWellDefinedProof {stages})),
        Obj::LimitOperator(LimitOperator::MultivariableVector(_)) => ObjWellDefinedProofByDef::LimitOperator(LimitOperatorObjWellDefinedProofByDef::MultivariableVector(MultivariableVectorLimitWellDefinedProof {stages})),
        Obj::DerivativeOperator(DerivativeOperator::Partial(_)) => ObjWellDefinedProofByDef::DerivativeOperator(super::super::function_derivative::DerivativeOperatorWellDefinedProof::Partial(PartialDerivativeAtWellDefinedProof {stages})),
        Obj::DerivativeOperator(DerivativeOperator::ScalarDifferential(_)) => ObjWellDefinedProofByDef::DerivativeOperator(super::super::function_derivative::DerivativeOperatorWellDefinedProof::ScalarDifferential(ScalarDifferentialAtWellDefinedProof {stages})),
        Obj::DerivativeOperator(DerivativeOperator::TotalDifferential(_)) => ObjWellDefinedProofByDef::DerivativeOperator(super::super::function_derivative::DerivativeOperatorWellDefinedProof::TotalDifferential(TotalDifferentialAtWellDefinedProof {stages})),
        Obj::DerivativeOperator(DerivativeOperator::Gradient(_)) => ObjWellDefinedProofByDef::DerivativeOperator(super::super::function_derivative::DerivativeOperatorWellDefinedProof::Gradient(GradientAtWellDefinedProof {stages})),
        Obj::DerivativeOperator(DerivativeOperator::Jacobian(_)) => ObjWellDefinedProofByDef::DerivativeOperator(super::super::function_derivative::DerivativeOperatorWellDefinedProof::Jacobian(JacobianAtWellDefinedProof {stages})),
        Obj::DerivativeOperator(DerivativeOperator::Hessian(_)) => ObjWellDefinedProofByDef::DerivativeOperator(super::super::function_derivative::DerivativeOperatorWellDefinedProof::Hessian(HessianAtWellDefinedProof {stages})),
        Obj::DerivativeOperator(DerivativeOperator::Divergence(_)) => ObjWellDefinedProofByDef::DerivativeOperator(super::super::function_derivative::DerivativeOperatorWellDefinedProof::Divergence(DivergenceAtWellDefinedProof {stages})),
        Obj::DerivativeOperator(DerivativeOperator::Curl(_)) => ObjWellDefinedProofByDef::DerivativeOperator(super::super::function_derivative::DerivativeOperatorWellDefinedProof::Curl(CurlAtWellDefinedProof {stages})),
        Obj::DerivativeOperator(DerivativeOperator::Laplacian(_)) => ObjWellDefinedProofByDef::DerivativeOperator(super::super::function_derivative::DerivativeOperatorWellDefinedProof::Laplacian(LaplacianAtWellDefinedProof {stages})),
        _=>unreachable!("multivariable selector"),
    }
}
fn selector_failure(
    obj: &Obj,
    stage: MultivariableSelectorFailureStage,
) -> VerifyObjWellDefinedResult {
    let reason=match obj {
        Obj::LimitOperator(LimitOperator::MultivariableScalar(_)) => FailToVerifyObjWellDefinedResult::LimitOperator(FailToVerifyLimitOperatorObjWellDefinedResult::MultivariableScalar(MultivariableScalarLimitWellDefinedFailure {stage})),
        Obj::LimitOperator(LimitOperator::MultivariableVector(_)) => FailToVerifyObjWellDefinedResult::LimitOperator(FailToVerifyLimitOperatorObjWellDefinedResult::MultivariableVector(MultivariableVectorLimitWellDefinedFailure {stage})),
        Obj::DerivativeOperator(DerivativeOperator::Partial(_)) => FailToVerifyObjWellDefinedResult::DerivativeOperator(super::super::function_derivative::DerivativeOperatorWellDefinedFailure::Partial(PartialDerivativeAtWellDefinedFailure {stage})),
        Obj::DerivativeOperator(DerivativeOperator::ScalarDifferential(_)) => FailToVerifyObjWellDefinedResult::DerivativeOperator(super::super::function_derivative::DerivativeOperatorWellDefinedFailure::ScalarDifferential(ScalarDifferentialAtWellDefinedFailure {stage})),
        Obj::DerivativeOperator(DerivativeOperator::TotalDifferential(_)) => FailToVerifyObjWellDefinedResult::DerivativeOperator(super::super::function_derivative::DerivativeOperatorWellDefinedFailure::TotalDifferential(TotalDifferentialAtWellDefinedFailure {stage})),
        Obj::DerivativeOperator(DerivativeOperator::Gradient(_)) => FailToVerifyObjWellDefinedResult::DerivativeOperator(super::super::function_derivative::DerivativeOperatorWellDefinedFailure::Gradient(GradientAtWellDefinedFailure {stage})),
        Obj::DerivativeOperator(DerivativeOperator::Jacobian(_)) => FailToVerifyObjWellDefinedResult::DerivativeOperator(super::super::function_derivative::DerivativeOperatorWellDefinedFailure::Jacobian(JacobianAtWellDefinedFailure {stage})),
        Obj::DerivativeOperator(DerivativeOperator::Hessian(_)) => FailToVerifyObjWellDefinedResult::DerivativeOperator(super::super::function_derivative::DerivativeOperatorWellDefinedFailure::Hessian(HessianAtWellDefinedFailure {stage})),
        Obj::DerivativeOperator(DerivativeOperator::Divergence(_)) => FailToVerifyObjWellDefinedResult::DerivativeOperator(super::super::function_derivative::DerivativeOperatorWellDefinedFailure::Divergence(DivergenceAtWellDefinedFailure {stage})),
        Obj::DerivativeOperator(DerivativeOperator::Curl(_)) => FailToVerifyObjWellDefinedResult::DerivativeOperator(super::super::function_derivative::DerivativeOperatorWellDefinedFailure::Curl(CurlAtWellDefinedFailure {stage})),
        Obj::DerivativeOperator(DerivativeOperator::Laplacian(_)) => FailToVerifyObjWellDefinedResult::DerivativeOperator(super::super::function_derivative::DerivativeOperatorWellDefinedFailure::Laplacian(LaplacianAtWellDefinedFailure {stage})),
        _=>unreachable!("multivariable selector"),
    };
    VerifyObjWellDefinedResult::Failed {
        obj: obj.clone(),
        reason,
    }
}
