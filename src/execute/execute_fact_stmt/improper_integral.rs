//! Improper Riemann integrals retain local integrability and independent limits.
use super::riemann_integral::helper::*;
use crate::prelude::*;

#[cfg(test)]
#[path = "../../../tests/unit/execute/riemann_integral/improper.rs"]
mod tests;

pub struct ImproperIntegralWellDefinedProof {
    pub children: Vec<ObjWellDefinedProof>,
    pub integrability: Box<VerifyFactResult>,
}

pub struct ImproperIntegralWellDefinedFailure {
    pub obj: Obj,
    pub requirement: Fact,
    pub result: Box<VerifyFactResult>,
}

pub struct ImproperIntegralDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
    pub stores: Vec<StoreFactAndInferResult>,
    pub local_env: Box<ExecEnv>,
}

pub struct ImproperIntegralStructuralProof {
    pub domain_requirements: Vec<VerifyFactResult>,
    pub domain_stores: Vec<StoreFactAndInferResult>,
    pub local_integrability: Box<VerifyFactResult>,
    pub local_integrability_store: StoreFactAndInferResult,
    pub limits: Vec<ImproperTruncationLimitProof>,
    pub value: Obj,
    pub comparison: Box<VerifyFactResult>,
    pub local_env: Box<ExecEnv>,
}

pub struct ImproperTruncationLimitProof {
    pub introduced_parameter: crate::execute::IntroduceTypedParametersResult,
    pub integrand_wd: ObjWellDefinedProof,
    pub integral: super::structural_riemann_integral::StructuralRiemannIntegralProof,
    pub formula_wd: ObjWellDefinedProof,
    pub limit: super::structural_limit::StructuralLimitProof,
    pub local_env: Box<ExecEnv>,
}

pub struct ImproperIntegralValueProof {
    pub requirement: Fact,
    pub proof: Box<VerifyFactResult>,
}

pub(crate) fn predicate_integral(fact: &AtomicFact) -> Option<(ImproperIntegral, Option<Obj>)> {
    let (predicate, body) = match fact {
        AtomicFact::NormalAtomicFact(fact) => (&fact.predicate, &fact.body),
        AtomicFact::NotNormalAtomicFact(fact) => (&fact.predicate, &fact.body),
        _ => return None,
    };
    let AtomicName::Plain { name } = predicate else {
        return None;
    };
    let (function, args) = body.split_first()?;
    let (bounds, candidate) = ImproperIntegralBounds::from_predicate(name, args)?;
    Some((
        ImproperIntegral::new(function.clone(), bounds),
        candidate.then(|| args.last().unwrap().clone()),
    ))
}

pub(crate) fn predicate_arity(name: &str) -> Option<usize> {
    match name {
        "has_integral_open_closed" | "has_integral_closed_open" | "has_integral_open" => Some(4),
        "has_integral_pos_inf" | "has_integral_neg_inf" => Some(3),
        "is_integrable_open_closed" | "is_integrable_closed_open" | "is_integrable_open" => Some(3),
        "is_integrable_pos_inf" | "is_integrable_neg_inf" => Some(2),
        _ => None,
    }
}

impl Runtime {
    pub(crate) fn improper_predicate(
        &mut self,
        integral: &ImproperIntegral,
        value: Option<Obj>,
    ) -> AtomicFact {
        let mut args = vec![*integral.function.clone()];
        args.extend(integral.bounds.endpoint_refs().into_iter().cloned());
        let name = integral.bounds.predicate_name(value.is_some());
        args.extend(value);
        certificate(self, name, args)
    }

    pub(crate) fn improper_signature_requirements(
        &mut self,
        integral: &ImproperIntegral,
        value: Option<Obj>,
        state: VerifyState,
    ) -> RuntimeResult<Option<Vec<Fact>>> {
        let Some(domain) = self.checked_real_function_limit_domain(&integral.function, state)?
        else {
            return Ok(None);
        };
        let mut requirements = Vec::new();
        for endpoint in integral.bounds.endpoint_refs() {
            requirements.push(member(self, endpoint.clone(), real()).into());
        }
        if let [start, end] = integral.bounds.endpoint_refs().as_slice() {
            requirements.push(
                NotEqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: (*start).clone(),
                    right: (*end).clone(),
                    line_file: None,
                }
                .into(),
            );
        }
        requirements.push(subset(self, integral_region(&integral.bounds), domain.domain).into());
        if let Some(value) = value {
            requirements.push(member(self, value, real()).into());
        }
        Ok(Some(requirements))
    }

    pub(crate) fn improper_definition_requirements(
        &mut self,
        integral: &ImproperIntegral,
        value: Option<Obj>,
    ) -> Vec<Fact> {
        let local = self.improper_local_integrability(integral);
        let selected = self.improper_limit_value(integral);
        let conclusion = match value {
            Some(value) => eq(self, selected, value).into(),
            None => member(self, selected, real()).into(),
        };
        vec![local, conclusion]
    }

    pub(crate) fn improper_local_integrability(&mut self, integral: &ImproperIntegral) -> Fact {
        let first = self.fresh_internal_param();
        let second = self.fresh_internal_param();
        let candidate =
            self.riemann_integrable(*integral.function.clone(), id(&first), id(&second));
        Fact::ForallFact(ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: TypedParameterList {
                groups: vec![TypedParameterGroup {
                    params: vec![first, second],
                    param_type: ParamType::Obj(integral_region(&integral.bounds)),
                }],
            },
            dom_facts: vec![],
            then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(candidate)],
            line_file: None,
        })
    }

    pub(crate) fn improper_limit_value(&mut self, integral: &ImproperIntegral) -> Obj {
        use ImproperIntegralBounds::*;
        if let Open { start, end } = &integral.bounds {
            let middle = crate::rational_expression::helper::div_objs(
                add(*start.clone(), *end.clone()),
                num("2"),
            );
            let first = ImproperIntegral::new(
                *integral.function.clone(),
                OpenClosed {
                    start: start.clone(),
                    end: Box::new(middle.clone()),
                },
            );
            let second = ImproperIntegral::new(
                *integral.function.clone(),
                ClosedOpen {
                    start: Box::new(middle),
                    end: end.clone(),
                },
            );
            return add(
                self.improper_limit_value(&first),
                self.improper_limit_value(&second),
            );
        }
        let parameter = self.fresh_internal_param();
        let t = id(&parameter);
        let (lower, upper, domain, approach) = match &integral.bounds {
            OpenClosed { start, end } | ClosedOpen { start, end }
                if EvalRational::from_obj(start)
                    .zip(EvalRational::from_obj(end))
                    .and_then(|(a, b)| a.compare(&b))
                    .is_some() =>
            {
                let forward = EvalRational::from_obj(start)
                    .zip(EvalRational::from_obj(end))
                    .and_then(|(a, b)| a.compare(&b))
                    == Some(crate::rational_expression::NumberCompareResult::Less);
                let domain = open_interval(
                    min(*start.clone(), *end.clone()),
                    max(*start.clone(), *end.clone()),
                );
                if matches!(integral.bounds, OpenClosed { .. }) {
                    let approach = if forward {
                        LimitApproach::FromRight(start.clone())
                    } else {
                        LimitApproach::FromLeft(start.clone())
                    };
                    (t, *end.clone(), domain, approach)
                } else {
                    let approach = if forward {
                        LimitApproach::FromLeft(end.clone())
                    } else {
                        LimitApproach::FromRight(end.clone())
                    };
                    (*start.clone(), t, domain, approach)
                }
            }
            OpenClosed { start, end } => (
                linear_endpoint(*start.clone(), t, *end.clone()),
                *end.clone(),
                open_interval(num("0"), num("1")),
                LimitApproach::FromRight(Box::new(num("0"))),
            ),
            ClosedOpen { start, end } => (
                *start.clone(),
                linear_endpoint(*end.clone(), t, *start.clone()),
                open_interval(num("0"), num("1")),
                LimitApproach::FromRight(Box::new(num("0"))),
            ),
            PositiveInfinity { start } => (
                *start.clone(),
                t,
                positive_ray(*start.clone(), false),
                LimitApproach::AtPositiveInfinity,
            ),
            NegativeInfinity { end } => (
                t,
                *end.clone(),
                Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(
                    OneSideInfinityIntervalObj::UpperOpen(OneSideInfinityIntervalObjStruct {
                        start: end.clone(),
                    }),
                )),
                LimitApproach::AtNegativeInfinity,
            ),
            Open { .. } => unreachable!(),
        };
        let body: Obj = RiemannIntegral::new(*integral.function.clone(), lower, upper).into();
        FunctionLimit::with_approach(literal(parameter, domain, body), approach).into()
    }

    pub(crate) fn verify_improper_integral_well_definedness(
        &mut self,
        integral: &ImproperIntegral,
        state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let obj: Obj = integral.clone().into();
        let mut children = Vec::new();
        for child in integral.operand_refs() {
            match self.verify_obj_well_definedness(child, state)? {
                VerifyObjWellDefinedResult::Success(proof) => children.push(proof),
                VerifyObjWellDefinedResult::Failed { reason, .. } => {
                    return Ok(VerifyObjWellDefinedResult::Failed { obj, reason })
                }
            }
        }
        let requirement: Fact = self.improper_predicate(integral, None).into();
        let result = self.verify_fact(&requirement, state)?;
        if result.is_failed() {
            return Ok(VerifyObjWellDefinedResult::Failed {
                obj: obj.clone(),
                reason: super::well_defined_results::verify_obj::FailToVerifyObjWellDefinedResult::IntegralOperator(
                    super::riemann_integral::IntegralOperatorWellDefinedFailure::Improper(ImproperIntegralWellDefinedFailure {
                        obj, requirement, result: Box::new(result),
                    }),
                ),
            });
        }
        Ok(VerifyObjWellDefinedResult::Success(
            ObjWellDefinedProof::by_def(self.result_detail(), &obj, None, || {
                ObjWellDefinedProofByDef::IntegralOperator(
                    super::riemann_integral::IntegralOperatorWellDefinedProof::Improper(
                        ImproperIntegralWellDefinedProof {
                            children,
                            integrability: Box::new(result),
                        },
                    ),
                )
            }),
        ))
    }

    pub(crate) fn prove_improper_definition(
        &mut self,
        integral: &ImproperIntegral,
        value: Option<Obj>,
        state: VerifyState,
    ) -> RuntimeResult<Result<ImproperIntegralDefinitionProof, DefinitionProofFailed>> {
        let requirements = self.improper_definition_requirements(integral, value);
        let (proofs, local_env) = self.run_in_local_env_and_take_env(|rt| {
            let mut proofs = Vec::new();
            let mut stores = Vec::new();
            for (index, requirement) in requirements.iter().enumerate() {
                let proof = rt.verify_fact(requirement, state)?;
                if proof.is_failed() {
                    return Ok(Err(DefinitionProofFailed::Requirement {
                        requirement_facts: requirements.clone(),
                        proof_of_requirement_facts: proofs,
                        index,
                        fact: requirement.clone(),
                        result: Box::new(proof),
                    }));
                }
                stores.push(rt.store_fact_and_infer(requirement, state)?);
                proofs.push(proof);
            }
            Ok(Ok((proofs, stores)))
        })?;
        Ok(
            proofs.map(|(proofs, stores)| ImproperIntegralDefinitionProof {
                requirement_facts: requirements,
                proof_of_requirement_facts: proofs,
                stores,
                local_env,
            }),
        )
    }

    pub(crate) fn search_improper_integral_structure(
        &mut self,
        fact: &AtomicFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<ImproperIntegralStructuralProof>> {
        if !matches!(fact, AtomicFact::NormalAtomicFact(_)) {
            return Ok(None);
        }
        let Some((integral, candidate)) = predicate_integral(fact) else {
            return Ok(None);
        };
        let Some(requirements) = self.improper_signature_requirements(&integral, None, state)?
        else {
            return Ok(None);
        };
        let local = self.improper_local_integrability(&integral);
        let (result, local_env) = self.run_in_local_env_and_take_env(|rt| {
            let mut domain_requirements = Vec::new();
            let mut domain_stores = Vec::new();
            for requirement in requirements {
                let proof = rt.verify_fact(&requirement, state)?;
                if proof.is_failed() {
                    return Ok(None);
                }
                domain_stores.push(rt.store_fact_and_infer(&requirement, state)?);
                domain_requirements.push(proof);
            }
            let Some(local_integrability) =
                rt.verify_improper_local_integrability(&local, state)?
            else {
                return Ok(None);
            };
            let local_integrability_store = rt.store_fact_and_infer(&local, state)?;
            let expression = rt.improper_limit_value(&integral);
            let mut limits = Vec::new();
            let Some(value) = rt.compute_improper_limit(&expression, state, &mut limits)? else {
                return Ok(None);
            };
            let target = candidate.unwrap_or_else(|| value.clone());
            let equality = eq(rt, value.clone(), target);
            let AtomicFact::EqualFact(equality) = equality else {
                unreachable!()
            };
            let Some(comparison) = rt.verify_integral_formula_equality(&equality, state)? else {
                return Ok(None);
            };
            Ok(Some((
                domain_requirements,
                domain_stores,
                local_integrability,
                local_integrability_store,
                limits,
                value,
                comparison,
            )))
        })?;
        Ok(result.map(
            |(
                domain_requirements,
                domain_stores,
                local_integrability,
                local_integrability_store,
                limits,
                value,
                comparison,
            )| {
                ImproperIntegralStructuralProof {
                    domain_requirements,
                    domain_stores,
                    local_integrability: Box::new(local_integrability),
                    local_integrability_store,
                    limits,
                    value,
                    comparison: Box::new(comparison),
                    local_env,
                }
            },
        ))
    }

    fn verify_improper_local_integrability(
        &mut self,
        fact: &Fact,
        state: VerifyState,
    ) -> RuntimeResult<Option<VerifyFactResult>> {
        let checked = self.verify_fact(fact, state)?;
        if !checked.is_failed() {
            return Ok(Some(checked));
        }
        let Fact::ForallFact(forall) = fact else {
            return Ok(None);
        };
        let (result, local_env) = self.run_in_local_env_and_take_env(|rt| {
            let Ok(introduced) = rt.introduce_typed_parameters(&forall.typed_parameters, state)?
            else {
                return Ok(None);
            };
            let [ExistOrAndChainAtomicFact::AtomicFact(goal)] = forall.then_facts.as_slice()
            else {
                return Ok(None);
            };
            let VerifyAtomicFactWellDefinedResult::Success(wd) =
                rt.verify_atomic_fact_well_definedness(goal, state)?
            else {
                return Ok(None);
            };
            use super::verify_atomic_fact::verify_atomic_except_equality::result::atomic_except_equality_fact_result_from_success;
            let proof = if let Some(proof) = rt.search_riemann_integrability_strategy(goal, state)? {
                AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RiemannIntegrability(proof)
            } else if let Some(proof) = rt.search_structural_riemann_integral_strategy(goal, state)? {
                AtomicExceptEqualityFactSearchProofByBuiltinStrategy::StructuralRiemannIntegral(proof)
            } else {
                return Ok(None);
            };
            let proof = atomic_except_equality_fact_result_from_success(
                goal, wd, AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(proof),
            );
            let store = rt.store_fact_and_infer(&goal.clone().into(), state)?;
            Ok(Some((introduced, proof, store)))
        })?;
        Ok(result.map(|(introduced, proof, store)| {
            VerifyFactResult::ForallFact(Box::new(VerifyForallFactResult::Success(
                VerifyForallFactProof::ByLocalIntroduction(VerifyForallFactSuccess {
                    fact: forall.clone(),
                    introduced_params: introduced,
                    assumed_dom_facts: vec![],
                    proved_then_facts: vec![
                        super::verify_forall_fact::ProveAndStoreThenFactResult {
                            verify_result: proof,
                            store_and_infer: store,
                        },
                    ],
                    local_env,
                }),
            )))
        }))
    }

    fn compute_improper_limit(
        &mut self,
        expression: &Obj,
        state: VerifyState,
        limits: &mut Vec<ImproperTruncationLimitProof>,
    ) -> RuntimeResult<Option<Obj>> {
        match expression {
            Obj::LimitOperator(LimitOperator::Function(limit)) => {
                let Obj::FunctionSpace(FunctionSpace::AnonymousFn(body)) = limit.function.as_ref()
                else {
                    return Ok(None);
                };
                let [group] = body.body.set_bound_parameters.groups.as_slice() else {
                    return Ok(None);
                };
                let [parameter] = group.params.as_slice() else {
                    return Ok(None);
                };
                let Obj::IntegralOperator(IntegralOperator::Riemann(integral)) =
                    body.equal_to.as_ref()
                else {
                    return Ok(None);
                };
                let VerifyObjWellDefinedResult::Success(integrand_wd) =
                    self.verify_obj_well_definedness(&integral.function, state)?
                else {
                    return Ok(None);
                };
                let (computed, local_env) = self.run_in_local_env_and_take_env(|rt| {
                    let parameters = super::function_limit::function_limit_typed(
                        parameter.clone(),
                        *group.param_type.clone(),
                    );
                    let Ok(introduced) = rt.introduce_typed_parameters(&parameters, state)? else {
                        return Ok(None);
                    };
                    let goal = rt.riemann_integrable(
                        *integral.function.clone(),
                        *integral.lower.clone(),
                        *integral.upper.clone(),
                    );
                    let Some(proof) =
                        rt.search_structural_riemann_integral_strategy(&goal, state)?
                    else {
                        return Ok(None);
                    };
                    let formula = proof.expression.integral.clone();
                    Ok(Some((introduced, proof, formula)))
                })?;
                let Some((introduced_parameter, integral, formula)) = computed else {
                    return Ok(None);
                };
                let formula_function =
                    literal(parameter.clone(), *group.param_type.clone(), formula);
                let VerifyObjWellDefinedResult::Success(formula_wd) =
                    self.verify_obj_well_definedness(&formula_function, state)?
                else {
                    return Ok(None);
                };
                let approach = super::structural_limit::StructuralLimitApproach::Function(
                    limit.approach.clone(),
                );
                let Some(limit) =
                    self.prove_structural_limit(&formula_function, approach, None, state)?
                else {
                    return Ok(None);
                };
                let value = limit.expression.limit.clone();
                limits.push(ImproperTruncationLimitProof {
                    introduced_parameter,
                    integrand_wd,
                    integral,
                    formula_wd,
                    limit,
                    local_env,
                });
                Ok(Some(value))
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) => {
                let Some(left) = self.compute_improper_limit(&sum.left, state, limits)? else {
                    return Ok(None);
                };
                let Some(right) = self.compute_improper_limit(&sum.right, state, limits)? else {
                    return Ok(None);
                };
                Ok(Some(add(left, right)))
            }
            _ => Ok(None),
        }
    }

    pub(crate) fn search_improper_integral_equality(
        &mut self,
        goal: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<ImproperIntegralValueProof>> {
        for (selected, value) in [(&goal.left, &goal.right), (&goal.right, &goal.left)] {
            let Obj::IntegralOperator(IntegralOperator::Improper(integral)) = selected else {
                continue;
            };
            let requirement: Fact = self
                .improper_predicate(integral, Some(value.clone()))
                .into();
            let mut proof = self.verify_fact(&requirement, state)?;
            if proof.is_failed() {
                let Fact::AtomicFact(candidate) = &requirement else {
                    unreachable!()
                };
                if let VerifyAtomicFactWellDefinedResult::Success(wd) =
                    self.verify_atomic_fact_well_definedness(candidate, state)?
                {
                    if let Some(structure) =
                        self.search_improper_integral_structure(candidate, state)?
                    {
                        proof = super::verify_atomic_fact::verify_atomic_except_equality::result::atomic_except_equality_fact_result_from_success(
                            candidate,
                            wd,
                            AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
                                AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ImproperIntegral(structure),
                            ),
                        );
                    }
                }
            }
            if !proof.is_failed() {
                return Ok(Some(ImproperIntegralValueProof {
                    requirement,
                    proof: Box::new(proof),
                }));
            }
        }
        Ok(None)
    }
}

pub(crate) fn integral_region(bounds: &ImproperIntegralBounds) -> Obj {
    use ImproperIntegralBounds::*;
    let (start, end, excluded) = match bounds {
        OpenClosed { start, end } => (start, end, vec![*start.clone()]),
        ClosedOpen { start, end } => (start, end, vec![*end.clone()]),
        Open { start, end } => (start, end, vec![*start.clone(), *end.clone()]),
        PositiveInfinity { start } => return positive_ray(*start.clone(), true),
        NegativeInfinity { end } => {
            return Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(
                OneSideInfinityIntervalObj::UpperClosed(OneSideInfinityIntervalObjStruct {
                    start: end.clone(),
                }),
            ))
        }
    };
    if let Some(order) = EvalRational::from_obj(start)
        .zip(EvalRational::from_obj(end))
        .and_then(|(a, b)| a.compare(&b))
    {
        let forward = order != crate::rational_expression::NumberCompareResult::Greater;
        let left_endpoint = if forward {
            start.as_ref()
        } else {
            end.as_ref()
        };
        let right_endpoint = if forward {
            end.as_ref()
        } else {
            start.as_ref()
        };
        let left_open = excluded.iter().any(|x| x == left_endpoint);
        let right_open = excluded.iter().any(|x| x == right_endpoint);
        let body = IntervalObjStruct {
            start: Box::new(min(*start.clone(), *end.clone())),
            end: Box::new(max(*start.clone(), *end.clone())),
        };
        return Obj::SetFormer(SetFormer::IntervalObj(match (left_open, right_open) {
            (true, true) => IntervalObj::LeftOpenRightOpen(body),
            (true, false) => IntervalObj::LeftOpenRightClosed(body),
            (false, true) => IntervalObj::LeftClosedRightOpen(body),
            (false, false) => IntervalObj::LeftClosedRightClosed(body),
        }));
    }
    Obj::SetOperator(SetOperator::SetMinus(SetMinus {
        left: Box::new(sorted_interval(*start.clone(), *end.clone())),
        right: Box::new(Obj::SetFormer(SetFormer::ListSet(ListSet {
            list: excluded.into_iter().map(Box::new).collect(),
        }))),
    }))
}

fn positive_ray(start: Obj, closed: bool) -> Obj {
    let bound = OneSideInfinityIntervalObjStruct {
        start: Box::new(start),
    };
    Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(if closed {
        OneSideInfinityIntervalObj::LowerClosed(bound)
    } else {
        OneSideInfinityIntervalObj::LowerOpen(bound)
    }))
}

fn linear_endpoint(start: Obj, parameter: Obj, end: Obj) -> Obj {
    // Preserve the affine segment expression used by shared membership proofs.
    // In particular, a zero start still needs its anchor in the expression.
    add(start.clone(), mul(parameter, sub(end, start)))
}
