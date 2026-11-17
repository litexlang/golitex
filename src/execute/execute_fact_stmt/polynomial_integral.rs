//! Bounded univariate normalization using the shared algebraic monomial collector.
use super::riemann_integral::helper::num;
use super::structural_riemann_integral::{depends, is_parameter};
use crate::prelude::*;
use crate::rational_expression::helper::{add_objs, div_objs, mul_objs, sub_objs};
use crate::rational_expression::{collect_monomials_in_obj, AlgebraicNormalizationMode};

impl Runtime {
    pub(super) fn verify_polynomial_identity(
        &mut self,
        fact: &ForallFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<VerifyFactResult>> {
        if !fact.dom_facts.is_empty() {
            return Ok(None);
        }
        let checked = self.verify_forall_fact(fact, state)?;
        if !checked.is_failed() {
            return Ok(Some(checked));
        }
        // The enclosing integration strategy may discharge rational identities
        // with checked nonzero premises in the same original binder scope.
        let (proved, local_env) = self.run_in_local_env_and_take_env(|rt| {
            let Ok(introduced) = rt.introduce_typed_parameters(&fact.typed_parameters, state)?
            else {
                return Ok(None);
            };
            let mut steps = Vec::new();
            for conclusion in &fact.then_facts {
                let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = conclusion.clone().into()
                else {
                    return Ok(None);
                };
                let Some(checked) = rt.verify_integral_formula_equality(&equality, state)? else {
                    return Ok(None);
                };
                let stored = rt.store_fact_and_infer(&equality.clone().into(), state)?;
                steps.push(super::verify_forall_fact::ProveAndStoreThenFactResult {
                    verify_result: checked,
                    store_and_infer: stored,
                });
            }
            Ok(Some((introduced, steps)))
        })?;
        Ok(proved.map(|(introduced, steps)| {
            VerifyFactResult::ForallFact(Box::new(VerifyForallFactResult::Success(
                VerifyForallFactProof::ByLocalIntroduction(VerifyForallFactSuccess {
                    fact: fact.clone(),
                    introduced_params: introduced,
                    assumed_dom_facts: Vec::new(),
                    proved_then_facts: steps,
                    local_env,
                }),
            )))
        }))
    }

    pub(super) fn verify_integral_formula_equality(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<VerifyFactResult>> {
        use super::verify_atomic_fact::verify_equality::result::{
            equal_fact_result_from_success, VerifyEqualityFailed,
        };
        let checked = self.verify_fact(&fact.clone().into(), state)?;
        if !checked.is_failed() {
            return Ok(Some(checked));
        }
        let VerifyFactResult::Equality(result) = checked else {
            return Ok(None);
        };
        let VerifyEqualityResult::Failed(VerifyEqualityFailed::FailToSearchProof {
            fact,
            well_defined_proof,
        }) = *result
        else {
            return Ok(None);
        };
        if let Some(calculation) = self.search_equal_fact_by_calculation(&fact, state)? {
            return Ok(Some(equal_fact_result_from_success(
                &fact,
                well_defined_proof,
                EqualFactSearchedProof::ByBuiltinRule(
                    EqualitySearchProofByBuiltinRule::Calculation(calculation),
                ),
            )));
        }
        let Some(normalization) =
            self.search_equal_fact_by_rational_with_nonzero_premises(&fact, state)?
        else {
            return Ok(None);
        };
        Ok(Some(equal_fact_result_from_success(
            &fact,
            well_defined_proof,
            EqualFactSearchedProof::ByBuiltinStrategy(
                EqualitySearchProofByBuiltinStrategy::RationalWithNonzeroPremises(normalization),
            ),
        )))
    }

    pub(crate) fn has_explicit_polynomial_integrand(&self, function: &Obj) -> bool {
        self.exact_property_object_values_of_shapes(function, &[EqualToObjShape::AnonymousFn])
            .into_iter()
            .any(|(literal, _)| {
                let Obj::FunctionSpace(FunctionSpace::AnonymousFn(body)) = literal else {
                    return false;
                };
                let [group] = body.body.set_bound_parameters.groups.as_slice() else {
                    return false;
                };
                let [parameter] = group.params.as_slice() else {
                    return false;
                };
                polynomial_shape(&body.equal_to, parameter.id, &mut 512, 0)
            })
    }
}

fn polynomial_shape(
    expression: &Obj,
    parameter: IdentifierId,
    budget: &mut usize,
    depth: usize,
) -> bool {
    if depth >= 64 || *budget == 0 {
        return false;
    }
    *budget -= 1;
    if !depends(expression, parameter) || is_parameter(expression, parameter) {
        return true;
    }
    match expression {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(p)) => {
            polynomial_shape(&p.left, parameter, budget, depth + 1)
                && polynomial_shape(&p.right, parameter, budget, depth + 1)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) => {
            polynomial_shape(&p.left, parameter, budget, depth + 1)
                && polynomial_shape(&p.right, parameter, budget, depth + 1)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) => {
            polynomial_shape(&p.left, parameter, budget, depth + 1)
                && polynomial_shape(&p.right, parameter, budget, depth + 1)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Div(p)) => {
            !depends(&p.right, parameter) && polynomial_shape(&p.left, parameter, budget, depth + 1)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(p)) => {
            polynomial_shape(&p.arg, parameter, budget, depth + 1)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(p)) => {
            !depends(&p.exponent, parameter)
                && polynomial_shape(&p.base, parameter, budget, depth + 1)
        }
        _ => false,
    }
}

pub(super) fn normalized_polynomial(
    expression: &Obj,
    parameter: IdentifierId,
    budget: &mut usize,
) -> Option<Obj> {
    let expanded_bound = expansion_bound(expression, parameter, budget, 0)?;
    if expanded_bound > 512 {
        return None;
    }
    normalized_polynomial_checked(expression, parameter)
}

fn normalized_polynomial_checked(expression: &Obj, parameter: IdentifierId) -> Option<Obj> {
    if let Obj::ArithmeticOperator(ArithmeticOperator::Div(quotient)) = expression {
        if !depends(&quotient.right, parameter) {
            return Some(div_objs(
                normalized_polynomial_checked(&quotient.left, parameter)?,
                *quotient.right.clone(),
            ));
        }
    }
    let expansion_source = coefficient_divisions(expression, parameter);
    let monomials =
        collect_monomials_in_obj(&expansion_source, AlgebraicNormalizationMode::Ordinary);
    let mut terms = Vec::new();
    for monomial in monomials {
        let mut coefficient = num(&monomial.non_zero_scalar);
        let mut degree = 0;
        for (factor, _) in monomial.ordered_operands.unwrap_or_default() {
            if is_parameter(&factor, parameter) {
                degree += 1;
            } else if !depends(&factor, parameter) {
                coefficient = if coefficient == num("1") {
                    factor
                } else {
                    mul_objs(coefficient, factor)
                };
            } else {
                return None;
            }
        }
        if degree > 32 {
            return None;
        }
        let term = if degree == 0 {
            coefficient
        } else {
            let variable = find_parameter(expression, parameter)?;
            let power = if degree == 1 {
                variable
            } else {
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
                    base: Box::new(variable),
                    exponent: Box::new(num(&degree.to_string())),
                }))
            };
            if coefficient == num("1") {
                power
            } else {
                mul_objs(coefficient, power)
            }
        };
        terms.push(term);
    }
    Some(
        terms
            .into_iter()
            .reduce(add_objs)
            .unwrap_or_else(|| num("0")),
    )
}

fn consume_expression_budget(expression: &Obj, budget: &mut usize, depth: usize) -> Option<()> {
    if depth >= 64 || *budget == 0 {
        return None;
    }
    *budget -= 1;
    match expression {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(p)) => {
            consume_expression_budget(&p.left, budget, depth + 1)?;
            consume_expression_budget(&p.right, budget, depth + 1)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) => {
            consume_expression_budget(&p.left, budget, depth + 1)?;
            consume_expression_budget(&p.right, budget, depth + 1)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) => {
            consume_expression_budget(&p.left, budget, depth + 1)?;
            consume_expression_budget(&p.right, budget, depth + 1)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Div(p)) => {
            consume_expression_budget(&p.left, budget, depth + 1)?;
            consume_expression_budget(&p.right, budget, depth + 1)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(p)) => {
            consume_expression_budget(&p.base, budget, depth + 1)?;
            consume_expression_budget(&p.exponent, budget, depth + 1)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(p)) => {
            consume_expression_budget(&p.arg, budget, depth + 1)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Abs(p)) => {
            consume_expression_budget(&p.arg, budget, depth + 1)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Min(p)) => {
            consume_expression_budget(&p.left, budget, depth + 1)?;
            consume_expression_budget(&p.right, budget, depth + 1)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Max(p)) => {
            consume_expression_budget(&p.left, budget, depth + 1)?;
            consume_expression_budget(&p.right, budget, depth + 1)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Sign(p)) => {
            consume_expression_budget(&p.arg, budget, depth + 1)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Floor(p)) => {
            consume_expression_budget(&p.arg, budget, depth + 1)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Ceil(p)) => {
            consume_expression_budget(&p.arg, budget, depth + 1)
        }
        _ => Some(()),
    }
}

fn expansion_bound(
    expression: &Obj,
    parameter: IdentifierId,
    budget: &mut usize,
    depth: usize,
) -> Option<usize> {
    if depth >= 64 || *budget == 0 {
        return None;
    }
    if !depends(expression, parameter) {
        consume_expression_budget(expression, budget, depth)?;
        return Some(1);
    }
    *budget -= 1;
    let bound =
        match expression {
            Obj::ArithmeticOperator(ArithmeticOperator::Add(p)) => {
                expansion_bound(&p.left, parameter, budget, depth + 1)?
                    .checked_add(expansion_bound(&p.right, parameter, budget, depth + 1)?)?
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) => {
                expansion_bound(&p.left, parameter, budget, depth + 1)?
                    .checked_add(expansion_bound(&p.right, parameter, budget, depth + 1)?)?
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) => {
                expansion_bound(&p.left, parameter, budget, depth + 1)?
                    .checked_mul(expansion_bound(&p.right, parameter, budget, depth + 1)?)?
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(p)) => {
                expansion_bound(&p.arg, parameter, budget, depth + 1)?
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Div(p))
                if !depends(&p.right, parameter) =>
            {
                consume_expression_budget(&p.right, budget, depth + 1)?;
                expansion_bound(&p.left, parameter, budget, depth + 1)?
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(p))
                if !depends(&p.exponent, parameter) =>
            {
                consume_expression_budget(&p.exponent, budget, depth + 1)?;
                if let Some(n) =
                    crate::rational_expression::evaluate_obj_to_normalized_decimal_number(
                        &p.exponent,
                    )
                    .and_then(|n| n.normalized_value.parse::<u32>().ok())
                    .filter(|n| *n <= 32)
                {
                    expansion_bound(&p.base, parameter, budget, depth + 1)?.checked_pow(n)?
                } else {
                    return None;
                }
            }
            _ if is_parameter(expression, parameter) => 1,
            _ => return None,
        };
    (bound <= 512).then_some(bound)
}

fn coefficient_divisions(expression: &Obj, parameter: IdentifierId) -> Obj {
    if !depends(expression, parameter) {
        return expression.clone();
    }
    match expression {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(p)) => add_objs(
            coefficient_divisions(&p.left, parameter),
            coefficient_divisions(&p.right, parameter),
        ),
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) => sub_objs(
            coefficient_divisions(&p.left, parameter),
            coefficient_divisions(&p.right, parameter),
        ),
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) => mul_objs(
            coefficient_divisions(&p.left, parameter),
            coefficient_divisions(&p.right, parameter),
        ),
        Obj::ArithmeticOperator(ArithmeticOperator::Div(p)) if !depends(&p.right, parameter) => {
            mul_objs(
                coefficient_divisions(&p.left, parameter),
                div_objs(num("1"), *p.right.clone()),
            )
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(p)) => {
            sub_objs(num("0"), coefficient_divisions(&p.arg, parameter))
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(p)) => {
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
                base: Box::new(coefficient_divisions(&p.base, parameter)),
                exponent: p.exponent.clone(),
            }))
        }
        _ => expression.clone(),
    }
}

pub(super) fn normalization_equalities(source: &Obj, normalized: &Obj) -> Vec<(Obj, Obj)> {
    let mut steps = Vec::new();
    if let (
        Obj::ArithmeticOperator(ArithmeticOperator::Div(source)),
        Obj::ArithmeticOperator(ArithmeticOperator::Div(normalized)),
    ) = (source, normalized)
    {
        if source.right.ir() == normalized.right.ir() {
            steps.extend(normalization_equalities(&source.left, &normalized.left));
        }
    }
    steps.push((source.clone(), normalized.clone()));
    steps
}

fn find_parameter(expression: &Obj, parameter: IdentifierId) -> Option<Obj> {
    if is_parameter(expression, parameter) {
        return Some(expression.clone());
    }
    match expression {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(p)) => {
            find_parameter(&p.left, parameter).or_else(|| find_parameter(&p.right, parameter))
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) => {
            find_parameter(&p.left, parameter).or_else(|| find_parameter(&p.right, parameter))
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) => {
            find_parameter(&p.left, parameter).or_else(|| find_parameter(&p.right, parameter))
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(p)) => find_parameter(&p.base, parameter),
        Obj::ArithmeticOperator(ArithmeticOperator::Div(p)) => find_parameter(&p.left, parameter),
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(p)) => find_parameter(&p.arg, parameter),
        _ => None,
    }
}
