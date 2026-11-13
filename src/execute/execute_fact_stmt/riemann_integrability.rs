//! Riemann integrability is closed under arithmetic without computing an integral.
//! A continuous, nowhere-zero denominator on the compact interval has a positive
//! absolute lower bound, so its reciprocal is continuous and integrable.
use super::function_domain::{function_domains_alpha_equal, CheckedFunctionBodyProof};
use super::function_limit::{
    function_limit_forall, function_limit_typed, RealFunctionLimitDomainProof,
};
use super::pointwise_continuity::PointwiseContinuityExpressionProof;
use super::pointwise_elementary::ElementaryRealFunction;
use super::real_analysis::analysis_apply;
use super::riemann_integral::helper::{id, member, num, real, sorted_interval};
use super::structural_riemann_integral::{depends, function_head, is_parameter};
use crate::execute::introduce_typed_parameters::IntroduceTypedParametersResult;
use crate::prelude::*;
use std::collections::HashMap;

pub struct RiemannIntegrabilityProof {
    pub function: Obj,
    pub lower: Obj,
    pub upper: Obj,
    pub domain: Box<RealFunctionLimitDomainProof>,
    pub interval_requirements: Vec<VerifyFactResult>,
    pub source: RiemannIntegrabilitySource,
    pub interval_stores: Vec<StoreFactAndInferResult>,
    pub introduced_point: IntroduceTypedParametersResult,
    pub continuity_premises: Vec<RiemannContinuityPremise>,
    pub expression: RiemannIntegrableExpressionProof,
    pub local_env: Box<crate::exec_env::ExecEnv>,
}

pub enum RiemannIntegrabilitySource {
    Defined {
        body: AnonymousFn,
        equality: KnownEqualityPathProof,
        well_defined: CheckedFunctionBodyProof,
    },
    Applied {
        parameter: crate::ast::names::BoundName,
    },
}

pub struct RiemannContinuityPremise {
    pub fact: AtomicFact,
    pub interval_continuity: Box<VerifyFactResult>,
    pub point_membership: Box<VerifyFactResult>,
    pub store: StoreFactAndInferResult,
}

pub struct RiemannIntegrableExpressionProof {
    pub expression: Obj,
    pub value: Obj,
    pub value_real: Box<VerifyFactResult>,
    pub constructor: RiemannIntegrableConstructorProof,
}

pub enum RiemannIntegrableConstructorProof {
    Constant,
    Variable,
    Neg {
        argument: Box<RiemannIntegrableExpressionProof>,
    },
    Abs {
        argument: Box<RiemannIntegrableExpressionProof>,
    },
    Add {
        left: Box<RiemannIntegrableExpressionProof>,
        right: Box<RiemannIntegrableExpressionProof>,
    },
    Sub {
        left: Box<RiemannIntegrableExpressionProof>,
        right: Box<RiemannIntegrableExpressionProof>,
    },
    Mul {
        left: Box<RiemannIntegrableExpressionProof>,
        right: Box<RiemannIntegrableExpressionProof>,
    },
    NaturalPower {
        base: Box<RiemannIntegrableExpressionProof>,
        exponent_natural: Box<VerifyFactResult>,
    },
    Quotient {
        numerator: Box<RiemannIntegrableExpressionProof>,
        denominator_continuity: PointwiseContinuityExpressionProof,
        denominator_nonzero: Box<VerifyFactResult>,
    },
    Application {
        function: Obj,
        integrability: Box<VerifyFactResult>,
    },
    Continuous(PointwiseContinuityExpressionProof),
}

impl Runtime {
    pub(crate) fn search_riemann_integrability_strategy(
        &mut self,
        goal: &AtomicFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<RiemannIntegrabilityProof>> {
        let AtomicFact::FunctionRiemannIntegrableFact(goal) = goal else {
            return Ok(None);
        };
        let Some(domain) = self.checked_real_function_limit_domain(&goal.function, state)? else {
            return Ok(None);
        };
        let requirements = self.riemann_domain_requirements(
            goal.lower.clone(),
            goal.upper.clone(),
            domain.domain.clone(),
        );
        let mut interval_requirements = Vec::new();
        for requirement in &requirements {
            let proof = self.verify_fact(requirement, state)?;
            if proof.is_failed() {
                return Ok(None);
            }
            interval_requirements.push(proof);
        }
        let mut sources = Vec::new();
        for (literal, path) in self
            .exact_property_object_values_of_shapes(&goal.function, &[EqualToObjShape::AnonymousFn])
        {
            let Obj::FunctionSpace(FunctionSpace::AnonymousFn(body)) = &literal else {
                continue;
            };
            if !function_domains_alpha_equal(&domain.source.signature, &body.body) {
                continue;
            }
            let parameters: Vec<_> = body
                .body
                .set_bound_parameters
                .groups
                .iter()
                .flat_map(|group| &group.params)
                .collect();
            if parameters.len() != 1 {
                continue;
            }
            let Some(well_defined) =
                self.checked_function_body_well_definedness(&goal.function, &literal, state)?
            else {
                continue;
            };
            sources.push((
                *body.equal_to.clone(),
                parameters[0].id,
                RiemannIntegrabilitySource::Defined {
                    body: body.clone(),
                    equality: KnownEqualityPathProof::new(path),
                    well_defined,
                },
            ));
        }
        // Direct application also handles opaque functions with supplied
        // interval-wide continuity through its actual application.
        let parameter = self.fresh_internal_param();
        sources.push((
            analysis_apply(goal.function.clone(), id(&parameter)),
            parameter.id,
            RiemannIntegrabilitySource::Applied { parameter },
        ));
        let mut budget = 512;
        for (body, parameter, source) in sources {
            if budget == 0 {
                break;
            }
            let point = self.fresh_internal_param();
            let point_value = id(&point);
            let interval = sorted_interval(goal.lower.clone(), goal.upper.clone());
            let (scoped, local_env) = self.run_in_local_env_and_take_env(|rt| {
                let mut interval_stores = Vec::new();
                for requirement in &requirements {
                    interval_stores.push(rt.store_fact_and_infer(requirement, state)?);
                }
                let params = function_limit_typed(point.clone(), interval.clone());
                let Ok(introduced_point) = rt.introduce_typed_parameters(&params, state)? else {
                    return Ok(None);
                };
                let continuity_premises = rt.prepare_riemann_continuity_premises(
                    &body,
                    parameter,
                    &point_value,
                    &interval,
                    state,
                )?;
                let Some(expression) = rt.prove_riemann_integrable_expression(
                    &body,
                    parameter,
                    &point_value,
                    &goal.lower,
                    &goal.upper,
                    state,
                    0,
                    &mut budget,
                )?
                else {
                    return Ok(None);
                };
                Ok(Some((
                    interval_stores,
                    introduced_point,
                    continuity_premises,
                    expression,
                )))
            })?;
            let Some((interval_stores, introduced_point, continuity_premises, expression)) = scoped
            else {
                continue;
            };
            return Ok(Some(RiemannIntegrabilityProof {
                function: goal.function.clone(),
                lower: goal.lower.clone(),
                upper: goal.upper.clone(),
                domain: Box::new(domain),
                interval_requirements,
                source,
                interval_stores,
                introduced_point,
                continuity_premises,
                expression,
                local_env,
            }));
        }
        Ok(None)
    }

    fn prepare_riemann_continuity_premises(
        &mut self,
        body: &Obj,
        parameter: IdentifierId,
        point: &Obj,
        interval: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<Vec<RiemannContinuityPremise>> {
        let mut pending = vec![body];
        let mut proofs = Vec::new();
        let mut remaining = 512;
        while let Some(expression) = pending.pop() {
            if remaining == 0 {
                break;
            }
            remaining -= 1;
            if let Some((_, argument)) = ElementaryRealFunction::from_expression(expression) {
                pending.push(argument);
                continue;
            }
            match expression {
                Obj::ArithmeticOperator(ArithmeticOperator::Add(a)) => {
                    pending.extend([a.left.as_ref(), a.right.as_ref()])
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(a)) => {
                    pending.extend([a.left.as_ref(), a.right.as_ref()])
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(a)) => {
                    pending.extend([a.left.as_ref(), a.right.as_ref()])
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Div(a)) => {
                    pending.extend([a.left.as_ref(), a.right.as_ref()])
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(a)) => pending.push(&a.base),
                Obj::ArithmeticOperator(ArithmeticOperator::Neg(a)) => pending.push(&a.arg),
                Obj::ArithmeticOperator(ArithmeticOperator::Abs(a)) => pending.push(&a.arg),
                Obj::FnObj(call) if call.body.len() == 1 && call.body[0].len() == 1 => {
                    pending.push(&call.body[0][0]);
                    let function = function_head(&call.head);
                    if depends(&function, parameter) {
                        continue;
                    }
                    let Ok(argument) = self.inst_obj(
                        &call.body[0][0],
                        &HashMap::from([(parameter, point.clone())]),
                    ) else {
                        continue;
                    };
                    let fact: AtomicFact = FunctionContinuousAtFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        function: function.clone(),
                        point: argument.clone(),
                        side: RealApproachSide::Both,
                        line_file: None,
                    }
                    .into();
                    if self.lookup_known_atomic_premise(fact.clone()).is_some() {
                        continue;
                    }
                    let mut regions = vec![interval.clone()];
                    if let Some(domain) =
                        self.checked_real_function_limit_domain(&function, state)?
                    {
                        if domain.domain != *interval {
                            regions.push(domain.domain);
                        }
                    }
                    for region in regions {
                        let membership: Fact =
                            member(self, argument.clone(), region.clone()).into();
                        let point_membership = self.verify_fact(&membership, state)?;
                        if point_membership.is_failed() {
                            continue;
                        }
                        let variable = self.fresh_internal_param();
                        let continuity: AtomicFact = FunctionContinuousAtFact {
                            fact_id: self.global_ids.allocate_fact_id(),
                            function: function.clone(),
                            point: id(&variable),
                            side: RealApproachSide::Both,
                            line_file: None,
                        }
                        .into();
                        let universal = function_limit_forall(
                            self,
                            variable,
                            region,
                            vec![],
                            vec![continuity.into()],
                        );
                        let interval_continuity = self.verify_fact(&universal, state)?;
                        if interval_continuity.is_failed() {
                            continue;
                        }
                        // Universal elimination uses the verified whole proposition
                        // and the checked point membership, preserving the search ceiling.
                        let store = self.store_fact_and_infer(&fact.clone().into(), state)?;
                        proofs.push(RiemannContinuityPremise {
                            fact: fact.clone(),
                            interval_continuity: Box::new(interval_continuity),
                            point_membership: Box::new(point_membership),
                            store,
                        });
                        break;
                    }
                }
                _ => {}
            }
        }
        Ok(proofs)
    }

    fn prove_riemann_integrable_expression(
        &mut self,
        expression: &Obj,
        parameter: IdentifierId,
        point: &Obj,
        lower: &Obj,
        upper: &Obj,
        state: VerifyState,
        depth: usize,
        budget: &mut usize,
    ) -> RuntimeResult<Option<RiemannIntegrableExpressionProof>> {
        if depth >= 64 || *budget == 0 {
            return Ok(None);
        }
        *budget -= 1;
        let Ok(value) = self.inst_obj(expression, &HashMap::from([(parameter, point.clone())]))
        else {
            return Ok(None);
        };
        let fact: Fact = member(self, value.clone(), real()).into();
        let value_real = self.verify_fact(&fact, state)?;
        if value_real.is_failed() {
            return Ok(None);
        }
        use RiemannIntegrableConstructorProof as C;
        let constructor = if !depends(expression, parameter) {
            C::Constant
        } else if is_parameter(expression, parameter) {
            C::Variable
        } else {
            match expression {
                Obj::ArithmeticOperator(ArithmeticOperator::Neg(a)) => {
                    let Some(argument) = self.prove_riemann_integrable_expression(
                        &a.arg,
                        parameter,
                        point,
                        lower,
                        upper,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    C::Neg {
                        argument: Box::new(argument),
                    }
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Abs(a)) => {
                    let Some(argument) = self.prove_riemann_integrable_expression(
                        &a.arg,
                        parameter,
                        point,
                        lower,
                        upper,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    C::Abs {
                        argument: Box::new(argument),
                    }
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Add(a)) => {
                    let Some(left) = self.prove_riemann_integrable_expression(
                        &a.left,
                        parameter,
                        point,
                        lower,
                        upper,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some(right) = self.prove_riemann_integrable_expression(
                        &a.right,
                        parameter,
                        point,
                        lower,
                        upper,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    C::Add {
                        left: Box::new(left),
                        right: Box::new(right),
                    }
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(a)) => {
                    let Some(left) = self.prove_riemann_integrable_expression(
                        &a.left,
                        parameter,
                        point,
                        lower,
                        upper,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some(right) = self.prove_riemann_integrable_expression(
                        &a.right,
                        parameter,
                        point,
                        lower,
                        upper,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    C::Sub {
                        left: Box::new(left),
                        right: Box::new(right),
                    }
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(a)) => {
                    let Some(left) = self.prove_riemann_integrable_expression(
                        &a.left,
                        parameter,
                        point,
                        lower,
                        upper,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some(right) = self.prove_riemann_integrable_expression(
                        &a.right,
                        parameter,
                        point,
                        lower,
                        upper,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    C::Mul {
                        left: Box::new(left),
                        right: Box::new(right),
                    }
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(a))
                    if !depends(&a.exponent, parameter) =>
                {
                    let fact: Fact =
                        member(self, *a.exponent.clone(), Obj::StandardSet(StandardSet::N)).into();
                    let exponent_natural = self.verify_fact(&fact, state)?;
                    if exponent_natural.is_failed() {
                        return Ok(None);
                    }
                    let Some(base) = self.prove_riemann_integrable_expression(
                        &a.base,
                        parameter,
                        point,
                        lower,
                        upper,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    C::NaturalPower {
                        base: Box::new(base),
                        exponent_natural: Box::new(exponent_natural),
                    }
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Div(a)) => {
                    let Some(numerator) = self.prove_riemann_integrable_expression(
                        &a.left,
                        parameter,
                        point,
                        lower,
                        upper,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some(denominator_continuity) = self.prove_continuous_expression(
                        &a.right,
                        parameter,
                        point,
                        RealApproachSide::Both,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    let fact: Fact = NotEqualFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        left: denominator_continuity.value.clone(),
                        right: num("0"),
                        line_file: None,
                    }
                    .into();
                    let denominator_nonzero = self.verify_fact(&fact, state)?;
                    if denominator_nonzero.is_failed() {
                        return Ok(None);
                    }
                    C::Quotient {
                        numerator: Box::new(numerator),
                        denominator_continuity,
                        denominator_nonzero: Box::new(denominator_nonzero),
                    }
                }
                Obj::FnObj(call)
                    if call.body.len() == 1
                        && call.body[0].len() == 1
                        && is_parameter(&call.body[0][0], parameter) =>
                {
                    let function = function_head(&call.head);
                    if depends(&function, parameter) {
                        return Ok(None);
                    }
                    let fact: Fact = self
                        .riemann_integrable(function.clone(), lower.clone(), upper.clone())
                        .into();
                    let integrability = self.verify_fact(&fact, state)?;
                    if integrability.is_failed() {
                        let Some(proof) = self.prove_continuous_expression(
                            expression,
                            parameter,
                            point,
                            RealApproachSide::Both,
                            state,
                            depth + 1,
                            budget,
                        )?
                        else {
                            return Ok(None);
                        };
                        C::Continuous(proof)
                    } else {
                        C::Application {
                            function,
                            integrability: Box::new(integrability),
                        }
                    }
                }
                _ => {
                    let Some(proof) = self.prove_continuous_expression(
                        expression,
                        parameter,
                        point,
                        RealApproachSide::Both,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    C::Continuous(proof)
                }
            }
        };
        Ok(Some(RiemannIntegrableExpressionProof {
            expression: expression.clone(),
            value,
            value_real: Box::new(value_real),
            constructor,
        }))
    }
}
