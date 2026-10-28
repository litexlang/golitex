//! Classical finite real derivatives. Selection consumes already proved evidence.
use super::function_limit::{function_limit_exists, RealFunctionLimitDomainProof};
use super::real_analysis::analysis_apply;
use super::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use super::well_defined_results::verify_obj::*;
use crate::ast::param::{SetBoundParameterGroup, SetBoundParameterList};
use crate::prelude::*;
use crate::rational_expression::helper::{div_objs, sub_objs};

pub enum DerivativeOperatorWellDefinedProof {
    Partial(crate::execute::execute_fact_stmt::multivariable::selector::PartialDerivativeAtWellDefinedProof),
    ScalarDifferential(crate::execute::execute_fact_stmt::multivariable::selector::ScalarDifferentialAtWellDefinedProof),
    TotalDifferential(crate::execute::execute_fact_stmt::multivariable::selector::TotalDifferentialAtWellDefinedProof),
    Gradient(crate::execute::execute_fact_stmt::multivariable::selector::GradientAtWellDefinedProof),
    Jacobian(crate::execute::execute_fact_stmt::multivariable::selector::JacobianAtWellDefinedProof),
    Hessian(crate::execute::execute_fact_stmt::multivariable::selector::HessianAtWellDefinedProof),
    Divergence(crate::execute::execute_fact_stmt::multivariable::selector::DivergenceAtWellDefinedProof),
    Curl(crate::execute::execute_fact_stmt::multivariable::selector::CurlAtWellDefinedProof),
    Laplacian(crate::execute::execute_fact_stmt::multivariable::selector::LaplacianAtWellDefinedProof),
    AtPoint(DerivativeAtWellDefinedProof),
}
pub struct DerivativeAtWellDefinedProof {
    pub function_wd: Box<ObjWellDefinedProof>,
    pub point_wd: Box<ObjWellDefinedProof>,
    pub domain: Box<RealFunctionLimitDomainProof>,
    pub point_in_domain: Box<VerifyFactResult>,
    pub convergence: DerivativeConvergenceProof,
}
pub enum DerivativeConvergenceProof {
    Candidate(AtomicExceptEqualityFactKnownProof),
    Existence {
        fact: Fact,
        proof: Box<VerifyFactResult>,
    },
}
pub enum DerivativeOperatorWellDefinedFailure {
    Partial(crate::execute::execute_fact_stmt::multivariable::selector::PartialDerivativeAtWellDefinedFailure),
    ScalarDifferential(crate::execute::execute_fact_stmt::multivariable::selector::ScalarDifferentialAtWellDefinedFailure),
    TotalDifferential(crate::execute::execute_fact_stmt::multivariable::selector::TotalDifferentialAtWellDefinedFailure),
    Gradient(crate::execute::execute_fact_stmt::multivariable::selector::GradientAtWellDefinedFailure),
    Jacobian(crate::execute::execute_fact_stmt::multivariable::selector::JacobianAtWellDefinedFailure),
    Hessian(crate::execute::execute_fact_stmt::multivariable::selector::HessianAtWellDefinedFailure),
    Divergence(crate::execute::execute_fact_stmt::multivariable::selector::DivergenceAtWellDefinedFailure),
    Curl(crate::execute::execute_fact_stmt::multivariable::selector::CurlAtWellDefinedFailure),
    Laplacian(crate::execute::execute_fact_stmt::multivariable::selector::LaplacianAtWellDefinedFailure),
    AtPoint(DerivativeAtWellDefinedFailure),
}
pub struct DerivativeAtWellDefinedFailure {
    pub obj: Obj,
    pub stage: DerivativeWellDefinedFailureStage,
}
pub enum DerivativeWellDefinedFailureStage {
    Domain,
    PointInDomain(Box<VerifyFactResult>),
    Convergence(Box<VerifyFactResult>),
}
impl Runtime {
    pub(crate) fn derivative_candidate(
        &mut self,
        function: Obj,
        point: Obj,
        value: Obj,
    ) -> AtomicFact {
        HasDerivativeAtFact {
            fact_id: self.global_ids.allocate_fact_id(),
            function,
            point,
            value,
            line_file: None,
        }
        .into()
    }
    pub(crate) fn derivative_existence(&mut self, function: Obj, point: Obj) -> Fact {
        let name = self.fresh_internal_param();
        let value = Obj::Identifier(IdentifierObj::from_bound_name(&name));
        let candidate = self.derivative_candidate(function, point, value);
        function_limit_exists(
            self,
            name,
            Obj::StandardSet(StandardSet::R),
            vec![candidate.into()],
        )
    }
    pub(crate) fn known_derivative_candidates(&self) -> Vec<HasDerivativeAtFact> {
        let key = (AtomicName::plain("has_derivative_at".into()), true);
        let mut result = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(facts) = env
                .facts
                .known_atomic_except_equality_facts
                .by_prop
                .get(&key)
            {
                for fact in facts {
                    if let AtomicFact::HasDerivativeAtFact(f) = fact {
                        result.push(f.clone());
                    }
                }
            }
        }
        result
    }
    pub(crate) fn derivative_interior_condition(&mut self, domain: Obj, point: Obj) -> Fact {
        let radius = self.fresh_internal_param();
        let x = self.fresh_internal_param();
        let x_obj = Obj::Identifier(IdentifierObj::from_bound_name(&x));
        let radius_obj = Obj::Identifier(IdentifierObj::from_bound_name(&radius));
        let distance = Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs {
            arg: Box::new(sub_objs(x_obj, point)),
        }));
        let condition: AtomicFact = LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: distance,
            right: radius_obj,
            line_file: None,
        }
        .into();
        let ball = Obj::SetFormer(SetFormer::SetBuilder(SetBuilder {
            param_binding: x,
            param_set: Box::new(Obj::StandardSet(StandardSet::R)),
            facts: vec![QuantifierFreeFact::AtomicFact(condition)],
        }));
        let subset: AtomicFact = SubsetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: ball,
            right: domain,
            line_file: None,
        }
        .into();
        function_limit_exists(
            self,
            radius,
            Obj::StandardSet(StandardSet::RPos),
            vec![subset],
        )
    }
    pub(crate) fn derivative_difference_quotient(
        &mut self,
        function: Obj,
        point: Obj,
        domain: Obj,
    ) -> Obj {
        let x = self.fresh_internal_param();
        let x_obj = Obj::Identifier(IdentifierObj::from_bound_name(&x));
        let difference = sub_objs(x_obj.clone(), point.clone());
        let nonzero: AtomicFact = NotEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: difference.clone(),
            right: Obj::Literal(Literal::Number(Number::new("0".into()))),
            line_file: None,
        }
        .into();
        let numerator = sub_objs(
            analysis_apply(function.clone(), x_obj),
            analysis_apply(function, point),
        );
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(AnonymousFn {
            body: FnSet {
                set_bound_parameters: SetBoundParameterList {
                    groups: vec![SetBoundParameterGroup {
                        params: vec![x],
                        param_type: Box::new(domain),
                    }],
                },
                dom_facts: vec![QuantifierFreeFact::AtomicFact(nonzero)],
                ret_set: Box::new(Obj::StandardSet(StandardSet::R)),
            },
            equal_to: Box::new(div_objs(numerator, difference)),
        }))
    }
    pub(crate) fn derivative_defining_clauses(
        &mut self,
        fact: &AtomicFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<Vec<Fact>>> {
        match fact {
            AtomicFact::HasDerivativeAtFact(f) => {
                let Some(domain) = self.checked_real_function_limit_domain(&f.function, state)?
                else {
                    return Ok(None);
                };
                let interior =
                    self.derivative_interior_condition(domain.domain.clone(), f.point.clone());
                let quotient = self.derivative_difference_quotient(
                    f.function.clone(),
                    f.point.clone(),
                    domain.domain,
                );
                let candidate = self.function_limit_candidate(
                    quotient,
                    LimitApproach::AtPoint(Box::new(f.point.clone())),
                    f.value.clone(),
                );
                Ok(Some(vec![interior, candidate.into()]))
            }
            AtomicFact::FunctionDifferentiableAtFact(f) => {
                Ok(Some(vec![self.derivative_existence(
                    f.function.clone(),
                    f.point.clone(),
                )]))
            }
            _ => Ok(None),
        }
    }
    pub(crate) fn verify_derivative_well_definedness(
        &mut self,
        derivative: &DerivativeAt,
        state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let obj: Obj = derivative.clone().into();
        let function_wd = match self.verify_obj_well_definedness(&derivative.function, state)? {
            VerifyObjWellDefinedResult::Success(p) => p,
            VerifyObjWellDefinedResult::Failed { reason, .. } => {
                return Ok(VerifyObjWellDefinedResult::Failed { obj, reason })
            }
        };
        let point_wd = match self.verify_obj_well_definedness(&derivative.point, state)? {
            VerifyObjWellDefinedResult::Success(p) => p,
            VerifyObjWellDefinedResult::Failed { reason, .. } => {
                return Ok(VerifyObjWellDefinedResult::Failed { obj, reason })
            }
        };
        let Some(domain) = self.checked_real_function_limit_domain(&derivative.function, state)?
        else {
            return Ok(failure(obj, DerivativeWellDefinedFailureStage::Domain));
        };
        let member: Fact = InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: *derivative.point.clone(),
            set: domain.domain.clone(),
            line_file: None,
        }
        .into();
        let point_in_domain = self.verify_fact(&member, state)?;
        if point_in_domain.is_failed() {
            return Ok(failure(
                obj,
                DerivativeWellDefinedFailureStage::PointInDomain(Box::new(point_in_domain)),
            ));
        }
        let mut known = None;
        for candidate in self.known_derivative_candidates() {
            let query = self.derivative_candidate(
                *derivative.function.clone(),
                *derivative.point.clone(),
                candidate.value,
            );
            if let Some(proof) = self.lookup_known_atomic_premise(query) {
                known = Some(DerivativeConvergenceProof::Candidate(proof));
                break;
            }
        }
        let convergence = match known {
            Some(proof) => proof,
            None => {
                let fact = self
                    .derivative_existence(*derivative.function.clone(), *derivative.point.clone());
                let proof = self.verify_fact(&fact, state)?;
                if proof.is_failed() {
                    return Ok(failure(
                        obj,
                        DerivativeWellDefinedFailureStage::Convergence(Box::new(proof)),
                    ));
                }
                DerivativeConvergenceProof::Existence {
                    fact,
                    proof: Box::new(proof),
                }
            }
        };
        Ok(VerifyObjWellDefinedResult::Success(
            ObjWellDefinedProof::by_def(self.result_detail(), &(obj), None, || {
                ObjWellDefinedProofByDef::DerivativeOperator(
                    DerivativeOperatorWellDefinedProof::AtPoint(DerivativeAtWellDefinedProof {
                        function_wd: Box::new(function_wd),
                        point_wd: Box::new(point_wd),
                        domain: Box::new(domain),
                        point_in_domain: Box::new(point_in_domain),
                        convergence,
                    }),
                )
            }),
        ))
    }
}
fn failure(obj: Obj, stage: DerivativeWellDefinedFailureStage) -> VerifyObjWellDefinedResult {
    VerifyObjWellDefinedResult::Failed {
        obj: obj.clone(),
        reason: FailToVerifyObjWellDefinedResult::DerivativeOperator(
            DerivativeOperatorWellDefinedFailure::AtPoint(DerivativeAtWellDefinedFailure {
                obj,
                stage,
            }),
        ),
    }
}
