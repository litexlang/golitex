//! Oriented Riemann integration of finite linear expressions.
//! Every constructor records its premises; only scalar multiplication is linear.
use super::function_domain::{function_domains_alpha_equal, CheckedFunctionBodyProof};
use super::function_limit::RealFunctionLimitDomainProof;
use super::riemann_integral::helper::{eq, member, num, real};
use super::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use super::verify_atomic_fact::verify_equality::result::{
    equal_fact_result_from_success, VerifyEqualityFailed,
};
use crate::prelude::*;
use crate::rational_expression::helper::{add_objs, div_objs, mul_objs, sub_objs};
use std::collections::HashSet;

pub struct StructuralRiemannIntegralProof {
    pub function: Obj,
    pub lower: Obj,
    pub upper: Obj,
    pub domain: Box<RealFunctionLimitDomainProof>,
    pub interval_requirements: Vec<VerifyFactResult>,
    pub body: AnonymousFn,
    pub body_equal: KnownEqualityPathProof,
    pub body_well_defined: CheckedFunctionBodyProof,
    pub expression: RiemannExpressionProof,
    pub conclusion: RiemannConclusionProof,
}

pub enum RiemannConclusionProof {
    Candidate(Box<VerifyFactResult>),
    Integrable,
}

pub struct RiemannExpressionProof {
    pub expression: Obj,
    pub integral: Obj,
    pub constructor: RiemannConstructorProof,
    pub integral_real: Box<VerifyFactResult>,
}

pub enum RiemannConstructorProof {
    Constant {
        value_real: Box<VerifyFactResult>,
    },
    Variable,
    NaturalPower {
        exponent_natural: Box<VerifyFactResult>,
    },
    Neg {
        argument: Box<RiemannExpressionProof>,
    },
    Add {
        left: Box<RiemannExpressionProof>,
        right: Box<RiemannExpressionProof>,
    },
    Sub {
        left: Box<RiemannExpressionProof>,
        right: Box<RiemannExpressionProof>,
    },
    Scale {
        scalar: Obj,
        scalar_real: Box<VerifyFactResult>,
        argument: Box<RiemannExpressionProof>,
    },
    Divide {
        argument: Box<RiemannExpressionProof>,
        denominator_real: Box<VerifyFactResult>,
        denominator_nonzero: Box<VerifyFactResult>,
    },
    Application {
        function: Obj,
        leaf: RiemannLeafProof,
    },
}

pub enum RiemannLeafProof {
    Candidate(AtomicExceptEqualityFactKnownProof),
    Selected {
        integrability: Box<VerifyFactResult>,
        value_well_defined: Box<ObjWellDefinedProof>,
    },
}

pub(super) fn depends(expression: &Obj, parameter: IdentifierId) -> bool {
    let mut free = HashSet::new();
    crate::instantiate::collect_free_plain_ids(expression, &HashSet::new(), &mut free);
    free.contains(&parameter)
}

pub(super) fn is_parameter(expression: &Obj, parameter: IdentifierId) -> bool {
    matches!(expression, Obj::Identifier(IdentifierObj::Plain { id, .. }) if *id == parameter)
}

pub(super) fn function_head(head: &FnObjHead) -> Obj {
    match head {
        FnObjHead::Identifier(value) => Obj::Identifier(value.clone()),
        FnObjHead::AnonymousFnLiteral(value) => {
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(*value.clone()))
        }
        FnObjHead::Object(value) => *value.clone(),
        FnObjHead::FieldAccess(value) => {
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(value.clone()))
        }
        FnObjHead::InstantiatedTemplateObj(value) => Obj::InstantiatedTemplateObj(value.clone()),
    }
}

fn power_integral(lower: &Obj, upper: &Obj, exponent: Obj) -> Obj {
    let next = add_objs(exponent, num("1"));
    let upper_power = Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
        base: Box::new(upper.clone()),
        exponent: Box::new(next.clone()),
    }));
    let lower_power = Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
        base: Box::new(lower.clone()),
        exponent: Box::new(next.clone()),
    }));
    div_objs(sub_objs(upper_power, lower_power), next)
}

impl Runtime {
    pub(crate) fn search_structural_riemann_integral_strategy(
        &mut self,
        goal: &AtomicFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<StructuralRiemannIntegralProof>> {
        let (function, lower, upper, value) = match goal {
            AtomicFact::HasRiemannIntegralFact(f) => {
                (&f.function, &f.lower, &f.upper, Some(&f.value))
            }
            AtomicFact::FunctionRiemannIntegrableFact(f) => (&f.function, &f.lower, &f.upper, None),
            _ => return Ok(None),
        };
        let Some(domain) = self.checked_real_function_limit_domain(function, state)? else {
            return Ok(None);
        };
        let mut interval_requirements = Vec::new();
        for fact in
            self.riemann_domain_requirements(lower.clone(), upper.clone(), domain.domain.clone())
        {
            let proof = self.verify_fact(&fact, state)?;
            if proof.is_failed() {
                return Ok(None);
            }
            interval_requirements.push(proof);
        }
        let mut budget = 512;
        for (literal, path) in
            self.exact_property_object_values_of_shapes(function, &[EqualToObjShape::AnonymousFn])
        {
            let Obj::FunctionSpace(FunctionSpace::AnonymousFn(body)) = &literal else {
                continue;
            };
            if !function_domains_alpha_equal(&domain.source.signature, &body.body) {
                continue;
            }
            let params: Vec<_> = body
                .body
                .set_bound_parameters
                .groups
                .iter()
                .flat_map(|g| &g.params)
                .collect();
            if params.len() != 1 {
                continue;
            }
            let Some(body_well_defined) =
                self.checked_function_body_well_definedness(function, &literal, state)?
            else {
                continue;
            };
            let Some(expression) = self.prove_riemann_expression(
                &body.equal_to,
                params[0].id,
                lower,
                upper,
                state,
                0,
                &mut budget,
            )?
            else {
                continue;
            };
            let conclusion = match value {
                Some(value) => {
                    let comparison: Fact =
                        eq(self, expression.integral.clone(), value.clone()).into();
                    let proof = self.verify_fact(&comparison, state)?;
                    let proof = match proof {
                        VerifyFactResult::Equality(result) => match *result {
                            VerifyEqualityResult::Failed(
                                VerifyEqualityFailed::FailToSearchProof {
                                    fact,
                                    well_defined_proof,
                                },
                            ) => {
                                // Normalize the constructed formula with the same checked
                                // denominator premises used by the derivative strategy.
                                let Some(normalization) = self
                                    .search_equal_fact_by_rational_with_nonzero_premises(
                                        &fact, state,
                                    )?
                                else {
                                    continue;
                                };
                                equal_fact_result_from_success(&fact, well_defined_proof,
                                    EqualFactSearchedProof::ByBuiltinStrategy(EqualitySearchProofByBuiltinStrategy::RationalWithNonzeroPremises(normalization)))
                            }
                            result => VerifyFactResult::Equality(Box::new(result)),
                        },
                        proof => proof,
                    };
                    if proof.is_failed() {
                        continue;
                    }
                    RiemannConclusionProof::Candidate(Box::new(proof))
                }
                None => RiemannConclusionProof::Integrable,
            };
            return Ok(Some(StructuralRiemannIntegralProof {
                function: function.clone(),
                lower: lower.clone(),
                upper: upper.clone(),
                domain: Box::new(domain),
                interval_requirements,
                body: body.clone(),
                body_equal: KnownEqualityPathProof::new(path),
                body_well_defined,
                expression,
                conclusion,
            }));
        }
        Ok(None)
    }

    fn prove_riemann_expression(
        &mut self,
        expression: &Obj,
        parameter: IdentifierId,
        lower: &Obj,
        upper: &Obj,
        state: VerifyState,
        depth: usize,
        budget: &mut usize,
    ) -> RuntimeResult<Option<RiemannExpressionProof>> {
        if depth >= 64 || *budget == 0 {
            return Ok(None);
        }
        *budget -= 1;
        use RiemannConstructorProof as C;
        let (integral, constructor) = if !depends(expression, parameter) {
            let fact: Fact = member(self, expression.clone(), real()).into();
            let value_real = self.verify_fact(&fact, state)?;
            if value_real.is_failed() {
                return Ok(None);
            }
            (
                mul_objs(expression.clone(), sub_objs(upper.clone(), lower.clone())),
                C::Constant {
                    value_real: Box::new(value_real),
                },
            )
        } else if is_parameter(expression, parameter) {
            (power_integral(lower, upper, num("1")), C::Variable)
        } else {
            match expression {
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(a))
                    if is_parameter(&a.base, parameter) && !depends(&a.exponent, parameter) =>
                {
                    let fact: Fact =
                        member(self, *a.exponent.clone(), Obj::StandardSet(StandardSet::N)).into();
                    let exponent_natural = self.verify_fact(&fact, state)?;
                    if exponent_natural.is_failed() {
                        return Ok(None);
                    }
                    (
                        power_integral(lower, upper, *a.exponent.clone()),
                        C::NaturalPower {
                            exponent_natural: Box::new(exponent_natural),
                        },
                    )
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Neg(a)) => {
                    let Some(argument) = self.prove_riemann_expression(
                        &a.arg,
                        parameter,
                        lower,
                        upper,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    (
                        sub_objs(num("0"), argument.integral.clone()),
                        C::Neg {
                            argument: Box::new(argument),
                        },
                    )
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Add(a)) => {
                    let Some(left) = self.prove_riemann_expression(
                        &a.left,
                        parameter,
                        lower,
                        upper,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some(right) = self.prove_riemann_expression(
                        &a.right,
                        parameter,
                        lower,
                        upper,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    (
                        add_objs(left.integral.clone(), right.integral.clone()),
                        C::Add {
                            left: Box::new(left),
                            right: Box::new(right),
                        },
                    )
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(a)) => {
                    let Some(left) = self.prove_riemann_expression(
                        &a.left,
                        parameter,
                        lower,
                        upper,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some(right) = self.prove_riemann_expression(
                        &a.right,
                        parameter,
                        lower,
                        upper,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    (
                        sub_objs(left.integral.clone(), right.integral.clone()),
                        C::Sub {
                            left: Box::new(left),
                            right: Box::new(right),
                        },
                    )
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(a)) => {
                    let (scalar, argument) = if !depends(&a.left, parameter) {
                        (&a.left, &a.right)
                    } else if !depends(&a.right, parameter) {
                        (&a.right, &a.left)
                    } else {
                        return Ok(None);
                    };
                    let fact: Fact = member(self, *scalar.clone(), real()).into();
                    let scalar_real = self.verify_fact(&fact, state)?;
                    if scalar_real.is_failed() {
                        return Ok(None);
                    }
                    let Some(argument) = self.prove_riemann_expression(
                        argument,
                        parameter,
                        lower,
                        upper,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    (
                        mul_objs(*scalar.clone(), argument.integral.clone()),
                        C::Scale {
                            scalar: *scalar.clone(),
                            scalar_real: Box::new(scalar_real),
                            argument: Box::new(argument),
                        },
                    )
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Div(a))
                    if !depends(&a.right, parameter) =>
                {
                    let fact: Fact = member(self, *a.right.clone(), real()).into();
                    let denominator_real = self.verify_fact(&fact, state)?;
                    if denominator_real.is_failed() {
                        return Ok(None);
                    }
                    let fact: Fact = NotEqualFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        left: *a.right.clone(),
                        right: num("0"),
                        line_file: None,
                    }
                    .into();
                    let denominator_nonzero = self.verify_fact(&fact, state)?;
                    if denominator_nonzero.is_failed() {
                        return Ok(None);
                    }
                    let Some(argument) = self.prove_riemann_expression(
                        &a.left,
                        parameter,
                        lower,
                        upper,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    (
                        div_objs(argument.integral.clone(), *a.right.clone()),
                        C::Divide {
                            argument: Box::new(argument),
                            denominator_real: Box::new(denominator_real),
                            denominator_nonzero: Box::new(denominator_nonzero),
                        },
                    )
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
                    let Some((integral, leaf)) =
                        self.prove_riemann_leaf(&function, lower, upper, state)?
                    else {
                        return Ok(None);
                    };
                    (integral, C::Application { function, leaf })
                }
                _ => return Ok(None),
            }
        };
        let fact: Fact = member(self, integral.clone(), real()).into();
        let integral_real = self.verify_fact(&fact, state)?;
        if integral_real.is_failed() {
            return Ok(None);
        }
        Ok(Some(RiemannExpressionProof {
            expression: expression.clone(),
            integral,
            constructor,
            integral_real: Box::new(integral_real),
        }))
    }

    fn prove_riemann_leaf(
        &mut self,
        function: &Obj,
        lower: &Obj,
        upper: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<Option<(Obj, RiemannLeafProof)>> {
        for known in self.known_riemann_integral_candidates() {
            let query = self.riemann_integral_candidate(
                function.clone(),
                lower.clone(),
                upper.clone(),
                known.value.clone(),
            );
            if let Some(proof) = self.lookup_known_atomic_premise(query) {
                return Ok(Some((known.value, RiemannLeafProof::Candidate(proof))));
            }
        }
        let fact: Fact = self
            .riemann_integrable(function.clone(), lower.clone(), upper.clone())
            .into();
        let integrability = self.verify_fact(&fact, state)?;
        if integrability.is_failed() {
            return Ok(None);
        }
        let value: Obj =
            RiemannIntegral::new(function.clone(), lower.clone(), upper.clone()).into();
        let VerifyObjWellDefinedResult::Success(value_well_defined) =
            self.verify_obj_well_definedness(&value, state)?
        else {
            return Ok(None);
        };
        Ok(Some((
            value,
            RiemannLeafProof::Selected {
                integrability: Box::new(integrability),
                value_well_defined: Box::new(value_well_defined),
            },
        )))
    }
}
