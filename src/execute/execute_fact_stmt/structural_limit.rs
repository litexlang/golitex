//! Bounded arithmetic limit checking over an already checked function body.
//! Example: a -> A and b -> B prove (k |-> a(k)+b(k)) -> A+B.
//! Shared fact verification uses this evidence for limit values and existence.
#[cfg(test)]
#[path = "../../../tests/unit/execute/pointwise_analysis/structural_limit.rs"]
mod structural_limit_tests;
use super::function_domain::{function_domains_alpha_equal, CheckedFunctionBodyProof};
use super::function_limit::RealFunctionLimitDomainProof;
use super::verify_atomic_fact::verify_atomic_except_equality::result::atomic_except_equality_fact_result_from_success;
use super::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use super::verify_atomic_fact::well_defined_result::FunctionLimitApproachRealProof;
use crate::prelude::*;
use crate::rational_expression::helper::{add_objs, div_objs, mul_objs, sub_objs};
use std::collections::HashSet;

pub struct StructuralLimitProof {
    pub function: Obj,
    pub approach: StructuralLimitApproach,
    pub domain: Box<RealFunctionLimitDomainProof>,
    pub body: AnonymousFn,
    pub body_equal: KnownEqualityPathProof,
    pub body_well_defined: CheckedFunctionBodyProof,
    pub geometry: StructuralLimitGeometryProof,
    pub expression: StructuralLimitExpressionProof,
    pub result_equal: Box<VerifyFactResult>,
}

pub struct LimitValueStrategyProof {
    pub candidate: Box<VerifyFactResult>,
}

#[derive(Clone)]
pub enum StructuralLimitApproach {
    Sequence,
    Function(LimitApproach),
}

pub enum StructuralLimitGeometryProof {
    RealInterval {
        requirement_facts: Vec<Fact>,
        proof_of_requirement_facts: Vec<VerifyFactResult>,
    },
    PositiveNaturalSequence,
    RealLine {
        domain_equal: Box<EqualFactSearchedProof>,
        approach_real: FunctionLimitApproachRealProof,
    },
    EstablishedCandidate {
        domain: Box<RealFunctionLimitDomainProof>,
        candidate: AtomicExceptEqualityFactKnownProof,
    },
    Known {
        requirement: Fact,
        proof: Box<VerifyFactResult>,
    },
}

pub struct StructuralLimitExpressionProof {
    pub expression: Obj,
    pub limit: Obj,
    pub constructor: StructuralLimitConstructorProof,
    pub limit_real: Box<VerifyFactResult>,
}

pub enum StructuralLimitConstructorProof {
    Elementary {
        kind: super::pointwise_elementary::ElementaryRealFunction,
        argument: Box<StructuralLimitExpressionProof>,
        domain: Box<VerifyFactResult>,
    },
    ReciprocalAffinePower {
        numerator: Box<StructuralLimitExpressionProof>,
        slope: Obj,
        offset: Obj,
        exponent: Obj,
        requirements: Vec<VerifyFactResult>,
    },
    RiemannIntegral {
        introduced_parameter: crate::execute::IntroduceTypedParametersResult,
        integral: Box<super::structural_riemann_integral::StructuralRiemannIntegralProof>,
        formula_limit: Box<StructuralLimitExpressionProof>,
        local_env: Box<ExecEnv>,
    },
    Constant,
    ZeroProduct {
        zero_factor: Box<VerifyFactResult>,
    },
    FiniteIdentity,
    Candidate {
        function_domain: Box<RealFunctionLimitDomainProof>,
        candidate: AtomicExceptEqualityFactKnownProof,
    },
    SequenceShift {
        function_domain: Box<RealFunctionLimitDomainProof>,
        offset: Obj,
        offset_natural: Box<VerifyFactResult>,
        candidate: AtomicExceptEqualityFactKnownProof,
    },
    Neg {
        argument: Box<StructuralLimitExpressionProof>,
    },
    Abs {
        argument: Box<StructuralLimitExpressionProof>,
    },
    Add {
        left: Box<StructuralLimitExpressionProof>,
        right: Box<StructuralLimitExpressionProof>,
    },
    Sub {
        left: Box<StructuralLimitExpressionProof>,
        right: Box<StructuralLimitExpressionProof>,
    },
    Mul {
        left: Box<StructuralLimitExpressionProof>,
        right: Box<StructuralLimitExpressionProof>,
    },
    Div {
        left: Box<StructuralLimitExpressionProof>,
        right: Box<StructuralLimitExpressionProof>,
        limit_nonzero: Box<VerifyFactResult>,
    },
    NaturalPower {
        exponent: Obj,
        exponent_natural: Box<VerifyFactResult>,
        base: Box<StructuralLimitExpressionProof>,
    },
}

impl Runtime {
    pub(crate) fn search_structural_limit_strategy(
        &mut self,
        goal: &AtomicFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<StructuralLimitProof>> {
        let (function, target, approach) = match goal {
            AtomicFact::HasSequenceLimitFact(f) => {
                (&f.sequence, &f.value, StructuralLimitApproach::Sequence)
            }
            AtomicFact::HasFunctionLimitFact(f) => (
                &f.function,
                &f.value,
                StructuralLimitApproach::Function(f.approach.clone()),
            ),
            _ => return Ok(None),
        };
        self.prove_structural_limit(function, approach, Some(target), state)
    }

    // A structurally computed real limit witnesses convergence. The exact
    // single-binder shape excludes extra conditions, uniqueness and negation.
    pub(crate) fn search_structural_limit_existence_strategy(
        &mut self,
        goal: &ExistShapedFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<StructuralLimitProof>> {
        let ExistShapedFact::Exist(existence) = goal else {
            return Ok(None);
        };
        let [group] = existence.typed_parameters.groups.as_slice() else {
            return Ok(None);
        };
        let [parameter] = group.params.as_slice() else {
            return Ok(None);
        };
        if !matches!(
            &group.param_type,
            ParamType::Obj(Obj::StandardSet(StandardSet::R))
        ) {
            return Ok(None);
        }
        let [QuantifierFreeFact::AtomicFact(candidate)] = existence.facts.as_slice() else {
            return Ok(None);
        };
        let (function, value, approach) = match candidate {
            AtomicFact::HasSequenceLimitFact(f) => {
                (&f.sequence, &f.value, StructuralLimitApproach::Sequence)
            }
            AtomicFact::HasFunctionLimitFact(f) => (
                &f.function,
                &f.value,
                StructuralLimitApproach::Function(f.approach.clone()),
            ),
            _ => return Ok(None),
        };
        if !is_limit_parameter(value, parameter.id)
            || depends_on_limit_parameter(function, parameter.id)
        {
            return Ok(None);
        }
        if let StructuralLimitApproach::Function(approach) = &approach {
            if approach
                .point()
                .is_some_and(|point| depends_on_limit_parameter(point, parameter.id))
            {
                return Ok(None);
            }
        }
        self.prove_structural_limit(function, approach, None, state)
    }

    // Like derivative/integral value strategies, only an equality endpoint
    // selects this route. Its candidate retains the shared structural proof.
    pub(crate) fn search_limit_value_strategy(
        &mut self,
        goal: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<LimitValueStrategyProof>> {
        for (selected, value) in [(&goal.left, &goal.right), (&goal.right, &goal.left)] {
            let candidate: AtomicFact = match selected {
                Obj::LimitOperator(LimitOperator::Function(limit)) => self
                    .function_limit_candidate(
                        *limit.function.clone(),
                        limit.approach.clone(),
                        value.clone(),
                    )
                    .into(),
                Obj::LimitOperator(LimitOperator::Sequence(limit)) => self
                    .sequence_limit_candidate(*limit.sequence.clone(), value.clone())
                    .into(),
                _ => continue,
            };
            let well_defined = match self.verify_atomic_fact_well_definedness(&candidate, state)? {
                VerifyAtomicFactWellDefinedResult::Success(proof) => proof,
                VerifyAtomicFactWellDefinedResult::Failed(_) => continue,
            };
            let Some(proof) = self.search_structural_limit_strategy(&candidate, state)? else {
                continue;
            };
            let candidate = atomic_except_equality_fact_result_from_success(
                &candidate,
                well_defined,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
                    AtomicExceptEqualityFactSearchProofByBuiltinStrategy::StructuralLimit(proof),
                ),
            );
            return Ok(Some(LimitValueStrategyProof {
                candidate: Box::new(candidate),
            }));
        }
        Ok(None)
    }

    pub(crate) fn prove_structural_limit(
        &mut self,
        function: &Obj,
        approach: StructuralLimitApproach,
        target: Option<&Obj>,
        state: VerifyState,
    ) -> RuntimeResult<Option<StructuralLimitProof>> {
        let Some(domain) = self.checked_real_function_limit_domain(function, state)? else {
            return Ok(None);
        };
        if matches!(approach, StructuralLimitApproach::Sequence)
            && (domain.domain != Obj::StandardSet(StandardSet::NPos)
                || !domain.source.signature.dom_facts.is_empty())
        {
            return Ok(None);
        }
        let mut remaining = 512;
        for (literal, path) in self
            .exact_property_object_values_of_shapes(function, &[EqualToObjShape::AnonymousFn])
            .into_iter()
            .take(16)
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
                .flat_map(|g| &g.params)
                .collect();
            if parameters.len() != 1 {
                continue;
            }
            let Some(body_well_defined) =
                self.checked_function_body_well_definedness(function, &literal, state)?
            else {
                continue;
            };
            let Some(geometry) = self.prove_structural_limit_geometry(&domain, &approach, state)?
            else {
                continue;
            };
            let Some(expression) = self.prove_structural_limit_expression(
                &body.equal_to,
                parameters[0],
                &domain,
                &approach,
                state,
                0,
                &mut remaining,
            )?
            else {
                continue;
            };
            let equal: Fact = EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: expression.limit.clone(),
                right: target.unwrap_or(&expression.limit).clone(),
                line_file: None,
            }
            .into();
            let result_equal = self.verify_fact(&equal, state)?;
            if result_equal.is_failed() {
                continue;
            }
            return Ok(Some(StructuralLimitProof {
                function: function.clone(),
                approach,
                domain: Box::new(domain),
                body: body.clone(),
                body_equal: KnownEqualityPathProof::new(path),
                body_well_defined,
                geometry,
                expression,
                result_equal: Box::new(result_equal),
            }));
        }
        Ok(None)
    }

    fn prove_structural_limit_geometry(
        &mut self,
        domain: &RealFunctionLimitDomainProof,
        approach: &StructuralLimitApproach,
        state: VerifyState,
    ) -> RuntimeResult<Option<StructuralLimitGeometryProof>> {
        let StructuralLimitApproach::Function(approach) = approach else {
            return Ok(Some(StructuralLimitGeometryProof::PositiveNaturalSequence));
        };
        if let Some(requirements) =
            self.interval_accumulation_requirements(&domain.domain, approach)
        {
            let mut proofs = Vec::new();
            for requirement in &requirements {
                let proof = self.verify_fact(requirement, state)?;
                if proof.is_failed() {
                    break;
                }
                proofs.push(proof);
            }
            if proofs.len() == requirements.len() {
                return Ok(Some(StructuralLimitGeometryProof::RealInterval {
                    requirement_facts: requirements,
                    proof_of_requirement_facts: proofs,
                }));
            }
        }
        // The existing real-line accumulation BT has no function-dependent
        // premise. Retain its domain equality and exact approach evidence here.
        if let Some(domain_equal) = self
            .lookup_exact_property_obj_equality(&domain.domain, &Obj::StandardSet(StandardSet::R))
        {
            let approach_real = match approach {
                LimitApproach::AtPositiveInfinity => {
                    FunctionLimitApproachRealProof::AtPositiveInfinity
                }
                LimitApproach::AtNegativeInfinity => {
                    FunctionLimitApproachRealProof::AtNegativeInfinity
                }
                _ => {
                    let required = self.function_limit_real_member(
                        approach.point().expect("finite approach").clone(),
                    );
                    let proof = self.verify_fact(&required, state)?;
                    if proof.is_failed() {
                        return Ok(None);
                    }
                    FunctionLimitApproachRealProof::Finite(Box::new(proof))
                }
            };
            return Ok(Some(StructuralLimitGeometryProof::RealLine {
                domain_equal: Box::new(domain_equal),
                approach_real,
            }));
        }
        // A checked candidate already includes accumulation on its actual
        // domain. Never infer accumulation on a larger or different domain.
        for candidate in self.known_function_limit_candidates().into_iter().take(128) {
            if &candidate.approach != approach {
                continue;
            }
            let Some(source) =
                self.checked_real_function_limit_domain(&candidate.function, state)?
            else {
                continue;
            };
            if !same_limit_input_domain(&source, domain) {
                continue;
            }
            let query = self.function_limit_candidate(
                candidate.function,
                approach.clone(),
                candidate.value,
            );
            if let Some(candidate) = self.lookup_known_atomic_premise(query.into()) {
                return Ok(Some(StructuralLimitGeometryProof::EstablishedCandidate {
                    domain: Box::new(source),
                    candidate,
                }));
            }
        }
        let requirement = self.function_limit_accumulation(domain.domain.clone(), approach.clone());
        let proof = self.verify_fact(&requirement, state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(StructuralLimitGeometryProof::Known {
            requirement,
            proof: Box::new(proof),
        }))
    }

    fn prove_structural_limit_expression(
        &mut self,
        expression: &Obj,
        parameter: &BoundName,
        domain: &RealFunctionLimitDomainProof,
        approach: &StructuralLimitApproach,
        state: VerifyState,
        depth: usize,
        remaining: &mut usize,
    ) -> RuntimeResult<Option<StructuralLimitExpressionProof>> {
        if depth >= 64 || *remaining == 0 {
            return Ok(None);
        }
        *remaining -= 1;
        use StructuralLimitConstructorProof as C;
        let (limit, constructor) = if !depends_on_limit_parameter(expression, parameter.id) {
            (expression.clone(), C::Constant)
        } else if is_limit_parameter(expression, parameter.id) {
            let StructuralLimitApproach::Function(approach) = approach else {
                return Ok(None);
            };
            let Some(point) = approach.point() else {
                return Ok(None);
            };
            (point.clone(), C::FiniteIdentity)
        } else if let Some(zero_factor) =
            self.structural_limit_zero_factor(expression, parameter.id, state)?
        {
            (
                limit_number("0"),
                C::ZeroProduct {
                    zero_factor: Box::new(zero_factor),
                },
            )
        } else if let Some((kind, input)) =
            super::pointwise_elementary::ElementaryRealFunction::from_expression(expression)
        {
            let Some(argument) = self.prove_structural_limit_expression(
                input,
                parameter,
                domain,
                approach,
                state,
                depth + 1,
                remaining,
            )?
            else {
                return Ok(None);
            };
            let requirement = self.elementary_real_condition(kind, argument.limit.clone(), false);
            let condition = self.verify_fact(&requirement, state)?;
            if condition.is_failed() {
                return Ok(None);
            }
            (
                kind.apply(argument.limit.clone()),
                C::Elementary {
                    kind,
                    argument: Box::new(argument),
                    domain: Box::new(condition),
                },
            )
        } else {
            match expression {
                Obj::ArithmeticOperator(ArithmeticOperator::Div(quotient))
                    if matches!(
                        approach,
                        StructuralLimitApproach::Function(
                            LimitApproach::AtPositiveInfinity | LimitApproach::AtNegativeInfinity
                        )
                    ) && depends_on_limit_parameter(&quotient.right, parameter.id)
                        && affine_power(&quotient.right, parameter.id).is_some() =>
                {
                    let (slope, offset, exponent) =
                        affine_power(&quotient.right, parameter.id).expect("matched affine power");
                    let Some(numerator) = self.prove_structural_limit_expression(
                        &quotient.left,
                        parameter,
                        domain,
                        approach,
                        state,
                        depth + 1,
                        remaining,
                    )?
                    else {
                        return Ok(None);
                    };
                    let facts = vec![
                        limit_member(self, slope.clone(), StandardSet::R),
                        limit_member(self, offset.clone(), StandardSet::R),
                        limit_member(self, exponent.clone(), StandardSet::NPos),
                        Fact::AtomicFact(
                            NotEqualFact {
                                fact_id: self.global_ids.allocate_fact_id(),
                                left: slope.clone(),
                                right: limit_number("0"),
                                line_file: None,
                            }
                            .into(),
                        ),
                    ];
                    let mut requirements = Vec::new();
                    for fact in facts {
                        let proof = self.verify_fact(&fact, state)?;
                        if proof.is_failed() {
                            return Ok(None);
                        }
                        requirements.push(proof);
                    }
                    (
                        limit_number("0"),
                        C::ReciprocalAffinePower {
                            numerator: Box::new(numerator),
                            slope,
                            offset,
                            exponent,
                            requirements,
                        },
                    )
                }
                Obj::IntegralOperator(IntegralOperator::Riemann(integral)) => {
                    let (result, local_env) = self.run_in_local_env_and_take_env(|rt| {
                        let parameters = super::function_limit::function_limit_typed(
                            parameter.clone(),
                            domain.domain.clone(),
                        );
                        let Ok(introduced_parameter) =
                            rt.introduce_typed_parameters(&parameters, state)?
                        else {
                            return Ok(None);
                        };
                        let goal = rt.riemann_integrable(
                            *integral.function.clone(),
                            *integral.lower.clone(),
                            *integral.upper.clone(),
                        );
                        let Some(integral_proof) =
                            rt.search_structural_riemann_integral_strategy(&goal, state)?
                        else {
                            return Ok(None);
                        };
                        let Some(formula_limit) = rt.prove_structural_limit_expression(
                            &integral_proof.expression.integral,
                            parameter,
                            domain,
                            approach,
                            state,
                            depth + 1,
                            remaining,
                        )?
                        else {
                            return Ok(None);
                        };
                        Ok(Some((introduced_parameter, integral_proof, formula_limit)))
                    })?;
                    let Some((introduced_parameter, integral_proof, formula_limit)) = result else {
                        return Ok(None);
                    };
                    (
                        formula_limit.limit.clone(),
                        C::RiemannIntegral {
                            introduced_parameter,
                            integral: Box::new(integral_proof),
                            formula_limit: Box::new(formula_limit),
                            local_env,
                        },
                    )
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Neg(a)) => {
                    let Some(argument) = self.prove_structural_limit_expression(
                        &a.arg,
                        parameter,
                        domain,
                        approach,
                        state,
                        depth + 1,
                        remaining,
                    )?
                    else {
                        return Ok(None);
                    };
                    let limit = Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg {
                        arg: Box::new(argument.limit.clone()),
                    }));
                    (
                        limit,
                        C::Neg {
                            argument: Box::new(argument),
                        },
                    )
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Abs(a)) => {
                    let Some(argument) = self.prove_structural_limit_expression(
                        &a.arg,
                        parameter,
                        domain,
                        approach,
                        state,
                        depth + 1,
                        remaining,
                    )?
                    else {
                        return Ok(None);
                    };
                    let limit = Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs {
                        arg: Box::new(argument.limit.clone()),
                    }));
                    (
                        limit,
                        C::Abs {
                            argument: Box::new(argument),
                        },
                    )
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Add(_))
                | Obj::ArithmeticOperator(ArithmeticOperator::Sub(_))
                | Obj::ArithmeticOperator(ArithmeticOperator::Mul(_))
                | Obj::ArithmeticOperator(ArithmeticOperator::Div(_)) => {
                    let (left, right) = match expression {
                        Obj::ArithmeticOperator(ArithmeticOperator::Add(a)) => (&a.left, &a.right),
                        Obj::ArithmeticOperator(ArithmeticOperator::Sub(a)) => (&a.left, &a.right),
                        Obj::ArithmeticOperator(ArithmeticOperator::Mul(a)) => (&a.left, &a.right),
                        Obj::ArithmeticOperator(ArithmeticOperator::Div(a)) => (&a.left, &a.right),
                        _ => unreachable!("matched binary arithmetic"),
                    };
                    let Some(left) = self.prove_structural_limit_expression(
                        left,
                        parameter,
                        domain,
                        approach,
                        state,
                        depth + 1,
                        remaining,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some(right) = self.prove_structural_limit_expression(
                        right,
                        parameter,
                        domain,
                        approach,
                        state,
                        depth + 1,
                        remaining,
                    )?
                    else {
                        return Ok(None);
                    };
                    let (a, b) = (left.limit.clone(), right.limit.clone());
                    match expression {
                        Obj::ArithmeticOperator(ArithmeticOperator::Add(_)) => (
                            add_objs(a, b),
                            C::Add {
                                left: Box::new(left),
                                right: Box::new(right),
                            },
                        ),
                        Obj::ArithmeticOperator(ArithmeticOperator::Sub(_)) => (
                            sub_objs(a, b),
                            C::Sub {
                                left: Box::new(left),
                                right: Box::new(right),
                            },
                        ),
                        Obj::ArithmeticOperator(ArithmeticOperator::Mul(_)) => (
                            mul_objs(a, b),
                            C::Mul {
                                left: Box::new(left),
                                right: Box::new(right),
                            },
                        ),
                        Obj::ArithmeticOperator(ArithmeticOperator::Div(_)) => {
                            let required: Fact = NotEqualFact {
                                fact_id: self.global_ids.allocate_fact_id(),
                                left: b.clone(),
                                right: limit_number("0"),
                                line_file: None,
                            }
                            .into();
                            let limit_nonzero = self.verify_fact(&required, state)?;
                            if limit_nonzero.is_failed() {
                                return Ok(None);
                            }
                            (
                                div_objs(a, b),
                                C::Div {
                                    left: Box::new(left),
                                    right: Box::new(right),
                                    limit_nonzero: Box::new(limit_nonzero),
                                },
                            )
                        }
                        _ => unreachable!("matched binary arithmetic"),
                    }
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(a)) => {
                    if depends_on_limit_parameter(&a.exponent, parameter.id) {
                        return Ok(None);
                    }
                    let required = limit_member(self, *a.exponent.clone(), StandardSet::N);
                    let exponent_natural = self.verify_fact(&required, state)?;
                    if exponent_natural.is_failed() {
                        return Ok(None);
                    }
                    let Some(base) = self.prove_structural_limit_expression(
                        &a.base,
                        parameter,
                        domain,
                        approach,
                        state,
                        depth + 1,
                        remaining,
                    )?
                    else {
                        return Ok(None);
                    };
                    let limit = Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
                        base: Box::new(base.limit.clone()),
                        exponent: a.exponent.clone(),
                    }));
                    (
                        limit,
                        C::NaturalPower {
                            exponent: *a.exponent.clone(),
                            exponent_natural: Box::new(exponent_natural),
                            base: Box::new(base),
                        },
                    )
                }
                Obj::FnObj(call) if call.body.len() == 1 && call.body[0].len() == 1 => {
                    let function = limit_function_head(&call.head);
                    if depends_on_limit_parameter(&function, parameter.id) {
                        return Ok(None);
                    }
                    let Some(function_domain) =
                        self.checked_real_function_limit_domain(&function, state)?
                    else {
                        return Ok(None);
                    };
                    if !same_limit_input_domain(&function_domain, domain) {
                        return Ok(None);
                    }
                    let input = &call.body[0][0];
                    let offset = if is_limit_parameter(input, parameter.id) {
                        None
                    } else if matches!(approach, StructuralLimitApproach::Sequence) {
                        let Obj::ArithmeticOperator(ArithmeticOperator::Add(add)) = input.as_ref()
                        else {
                            return Ok(None);
                        };
                        let offset = if is_limit_parameter(&add.left, parameter.id) {
                            &add.right
                        } else if is_limit_parameter(&add.right, parameter.id) {
                            &add.left
                        } else {
                            return Ok(None);
                        };
                        if depends_on_limit_parameter(offset, parameter.id) {
                            return Ok(None);
                        }
                        let required = limit_member(self, *offset.clone(), StandardSet::N);
                        let proof = self.verify_fact(&required, state)?;
                        if proof.is_failed() {
                            return Ok(None);
                        }
                        Some((*offset.clone(), proof))
                    } else {
                        return Ok(None);
                    };
                    let found = match approach {
                        StructuralLimitApproach::Sequence => {
                            let mut found = None;
                            for known in
                                self.known_sequence_limit_candidates().into_iter().take(128)
                            {
                                let query = self.sequence_limit_candidate(
                                    function.clone(),
                                    known.value.clone(),
                                );
                                if let Some(proof) = self.lookup_known_atomic_premise(query.into())
                                {
                                    found = Some((known.value, proof));
                                    break;
                                }
                            }
                            found
                        }
                        StructuralLimitApproach::Function(approach) => {
                            let mut found = None;
                            for known in
                                self.known_function_limit_candidates().into_iter().take(128)
                            {
                                if &known.approach != approach {
                                    continue;
                                }
                                let query = self.function_limit_candidate(
                                    function.clone(),
                                    approach.clone(),
                                    known.value.clone(),
                                );
                                if let Some(proof) = self.lookup_known_atomic_premise(query.into())
                                {
                                    found = Some((known.value, proof));
                                    break;
                                }
                            }
                            found
                        }
                    };
                    let Some((limit, candidate)) = found else {
                        return Ok(None);
                    };
                    let constructor = match offset {
                        Some((offset, offset_natural)) => C::SequenceShift {
                            function_domain: Box::new(function_domain),
                            offset,
                            offset_natural: Box::new(offset_natural),
                            candidate,
                        },
                        None => C::Candidate {
                            function_domain: Box::new(function_domain),
                            candidate,
                        },
                    };
                    (limit, constructor)
                }
                _ => return Ok(None),
            }
        };
        let required = limit_member(self, limit.clone(), StandardSet::R);
        let limit_real = self.verify_fact(&required, state)?;
        if limit_real.is_failed() {
            return Ok(None);
        }
        Ok(Some(StructuralLimitExpressionProof {
            expression: expression.clone(),
            limit,
            constructor,
            limit_real: Box::new(limit_real),
        }))
    }
}

impl Runtime {
    // The enclosing checked function body supplies WD for both factors.
    // A factor independent of the limit parameter and equal to zero makes
    // the whole product zero, even when the other factor has no finite limit.
    fn structural_limit_zero_factor(
        &mut self,
        expression: &Obj,
        parameter: IdentifierId,
        state: VerifyState,
    ) -> RuntimeResult<Option<VerifyFactResult>> {
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = expression else {
            return Ok(None);
        };
        for factor in [&product.left, &product.right] {
            if depends_on_limit_parameter(factor, parameter) {
                continue;
            }
            let equality: Fact = EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: *factor.clone(),
                right: limit_number("0"),
                line_file: None,
            }
            .into();
            let proof = self.verify_fact(&equality, state)?;
            if !proof.is_failed() {
                return Ok(Some(proof));
            }
        }
        Ok(None)
    }

    fn interval_accumulation_requirements(
        &mut self,
        domain: &Obj,
        approach: &LimitApproach,
    ) -> Option<Vec<Fact>> {
        use super::riemann_integral::helper::{le, lt, member, real};
        let Obj::SetFormer(set) = domain else {
            return None;
        };
        let (lower, upper) = match set {
            SetFormer::IntervalObj(interval) => {
                let bounds = match interval {
                    IntervalObj::LeftClosedRightClosed(x)
                    | IntervalObj::LeftClosedRightOpen(x)
                    | IntervalObj::LeftOpenRightClosed(x)
                    | IntervalObj::LeftOpenRightOpen(x) => x,
                };
                (Some(*bounds.start.clone()), Some(*bounds.end.clone()))
            }
            SetFormer::OneSideInfinityIntervalObj(
                OneSideInfinityIntervalObj::LowerClosed(x)
                | OneSideInfinityIntervalObj::LowerOpen(x),
            ) => (Some(*x.start.clone()), None),
            SetFormer::OneSideInfinityIntervalObj(
                OneSideInfinityIntervalObj::UpperClosed(x)
                | OneSideInfinityIntervalObj::UpperOpen(x),
            ) => (None, Some(*x.start.clone())),
            _ => return None,
        };
        let mut requirements = Vec::new();
        match approach {
            LimitApproach::AtPositiveInfinity if upper.is_none() => {}
            LimitApproach::AtNegativeInfinity if lower.is_none() => {}
            LimitApproach::AtPositiveInfinity | LimitApproach::AtNegativeInfinity => return None,
            _ => {
                let point = approach.point()?.clone();
                requirements.push(member(self, point.clone(), real()).into());
                if let Some(lower) = lower.clone() {
                    requirements.push(if matches!(approach, LimitApproach::FromRight(_)) {
                        le(self, lower, point.clone()).into()
                    } else {
                        lt(self, lower, point.clone()).into()
                    });
                }
                if let Some(upper) = upper.clone() {
                    requirements.push(if matches!(approach, LimitApproach::FromLeft(_)) {
                        le(self, point, upper).into()
                    } else {
                        lt(self, point, upper).into()
                    });
                }
            }
        }
        for endpoint in lower.into_iter().chain(upper) {
            requirements.push(member(self, endpoint, real()).into());
        }
        Some(requirements)
    }
}

fn same_limit_input_domain(
    left: &RealFunctionLimitDomainProof,
    right: &RealFunctionLimitDomainProof,
) -> bool {
    function_domains_alpha_equal(&left.source.signature, &right.source.signature)
}

fn depends_on_limit_parameter(expression: &Obj, parameter: IdentifierId) -> bool {
    let mut free = HashSet::new();
    crate::instantiate::collect_free_plain_ids(expression, &HashSet::new(), &mut free);
    free.contains(&parameter)
}

fn is_limit_parameter(expression: &Obj, parameter: IdentifierId) -> bool {
    matches!(expression, Obj::Identifier(IdentifierObj::Plain { id, .. }) if *id == parameter)
}

fn limit_function_head(head: &FnObjHead) -> Obj {
    match head {
        FnObjHead::Identifier(a) => Obj::Identifier(a.clone()),
        FnObjHead::AnonymousFnLiteral(a) => {
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(*a.clone()))
        }
        FnObjHead::Object(a) => *a.clone(),
        FnObjHead::FieldAccess(a) => {
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(a.clone()))
        }
        FnObjHead::InstantiatedTemplateObj(a) => Obj::InstantiatedTemplateObj(a.clone()),
    }
}

fn limit_number(value: &str) -> Obj {
    Obj::Literal(Literal::Number(Number::new(value.into())))
}

fn limit_member(rt: &mut Runtime, element: Obj, set: StandardSet) -> Fact {
    InFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        element,
        set: Obj::StandardSet(set),
        line_file: None,
    }
    .into()
}

fn affine_power(expression: &Obj, parameter: IdentifierId) -> Option<(Obj, Obj, Obj)> {
    let (base, exponent) = match expression {
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(power))
            if !depends_on_limit_parameter(&power.exponent, parameter) =>
        {
            (power.base.as_ref(), *power.exponent.clone())
        }
        value => (value, limit_number("1")),
    };
    let (slope, offset) = affine_coefficients(base, parameter, 0)?;
    Some((slope, offset, exponent))
}

fn affine_coefficients(
    expression: &Obj,
    parameter: IdentifierId,
    depth: usize,
) -> Option<(Obj, Obj)> {
    if depth > 32 {
        return None;
    }
    if !depends_on_limit_parameter(expression, parameter) {
        return Some((limit_number("0"), expression.clone()));
    }
    if is_limit_parameter(expression, parameter) {
        return Some((limit_number("1"), limit_number("0")));
    }
    let result = match expression {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(value)) => {
            let (a, b) = affine_coefficients(&value.left, parameter, depth + 1)?;
            let (c, d) = affine_coefficients(&value.right, parameter, depth + 1)?;
            (add_objs(a, c), add_objs(b, d))
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(value)) => {
            let (a, b) = affine_coefficients(&value.left, parameter, depth + 1)?;
            let (c, d) = affine_coefficients(&value.right, parameter, depth + 1)?;
            (sub_objs(a, c), sub_objs(b, d))
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(value)) => {
            let (scalar, base) = if !depends_on_limit_parameter(&value.left, parameter) {
                (&value.left, &value.right)
            } else if !depends_on_limit_parameter(&value.right, parameter) {
                (&value.right, &value.left)
            } else {
                return None;
            };
            let (a, b) = affine_coefficients(base, parameter, depth + 1)?;
            (mul_objs(*scalar.clone(), a), mul_objs(*scalar.clone(), b))
        }
        _ => return None,
    };
    Some(result)
}
