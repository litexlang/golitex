//! Structural continuity on the actual checked function domain.
#[cfg(test)]
#[path = "../../../tests/unit/execute/pointwise_analysis/continuity.rs"]
mod pointwise_continuity_tests;
use super::function_domain::function_domains_alpha_equal;
use super::function_limit::RealFunctionLimitDomainProof;
use crate::prelude::*;
use std::collections::{HashMap, HashSet};

pub struct PointwiseContinuityProof {
    pub function: Obj,
    pub point: Obj,
    pub domain: Box<RealFunctionLimitDomainProof>,
    pub body: AnonymousFn,
    pub body_equal: KnownEqualityPathProof,
    pub body_well_defined: Box<ObjWellDefinedProof>,
    pub expression: PointwiseContinuityExpressionProof,
}
pub struct PointwiseContinuityExpressionProof {
    pub expression: Obj,
    pub value: Obj,
    pub value_real: Box<VerifyFactResult>,
    pub constructor: PointwiseContinuityConstructorProof,
}
pub enum PointwiseContinuityConstructorProof {
    Constant,
    Variable,
    Neg {
        argument: Box<PointwiseContinuityExpressionProof>,
    },
    Abs {
        argument: Box<PointwiseContinuityExpressionProof>,
    },
    Add {
        left: Box<PointwiseContinuityExpressionProof>,
        right: Box<PointwiseContinuityExpressionProof>,
    },
    Sub {
        left: Box<PointwiseContinuityExpressionProof>,
        right: Box<PointwiseContinuityExpressionProof>,
    },
    Mul {
        left: Box<PointwiseContinuityExpressionProof>,
        right: Box<PointwiseContinuityExpressionProof>,
    },
    Div {
        left: Box<PointwiseContinuityExpressionProof>,
        right: Box<PointwiseContinuityExpressionProof>,
        denominator_nonzero: Box<VerifyFactResult>,
    },
    NaturalPower {
        base: Box<PointwiseContinuityExpressionProof>,
        exponent_natural: Box<VerifyFactResult>,
    },
    Compose {
        function: Obj,
        argument: Box<PointwiseContinuityExpressionProof>,
        outer_continuity: Box<VerifyFactResult>,
    },
}
impl Runtime {
    pub(crate) fn search_pointwise_continuity_strategy(
        &mut self,
        fact: &AtomicFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<PointwiseContinuityProof>> {
        let AtomicFact::FunctionContinuousAtFact(goal) = fact else {
            return Ok(None);
        };
        if goal.side != RealApproachSide::Both {
            return Ok(None);
        }
        let Some(domain) = self.checked_real_function_limit_domain(&goal.function, state)? else {
            return Ok(None);
        };
        let mut remaining = 512;
        for (value, path) in self
            .exact_property_object_values_of_shapes(&goal.function, &[EqualToObjShape::AnonymousFn])
        {
            let Obj::FunctionSpace(FunctionSpace::AnonymousFn(body)) = &value else {
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
            let param = params[0].id;
            let VerifyObjWellDefinedResult::Success(body_well_defined) =
                self.verify_obj_well_definedness(&value, state)?
            else {
                continue;
            };
            let Some(expression) = self.prove_continuous_expression(
                &body.equal_to,
                param,
                &goal.point,
                state,
                0,
                &mut remaining,
            )?
            else {
                continue;
            };
            return Ok(Some(PointwiseContinuityProof {
                function: goal.function.clone(),
                point: goal.point.clone(),
                domain: Box::new(domain),
                body: body.clone(),
                body_equal: KnownEqualityPathProof::new(path),
                body_well_defined: Box::new(body_well_defined),
                expression,
            }));
        }
        Ok(None)
    }
    pub(crate) fn prove_continuous_expression(
        &mut self,
        expression: &Obj,
        parameter: IdentifierId,
        point: &Obj,
        state: VerifyState,
        depth: usize,
        remaining: &mut usize,
    ) -> RuntimeResult<Option<PointwiseContinuityExpressionProof>> {
        if depth >= 64 || *remaining == 0 {
            return Ok(None);
        }
        *remaining -= 1;
        let Ok(value) = self.inst_obj(expression, &HashMap::from([(parameter, point.clone())]))
        else {
            return Ok(None);
        };
        let real = InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: value.clone(),
            set: Obj::StandardSet(StandardSet::R),
            line_file: None,
        }
        .into();
        let value_real = self.verify_fact(&real, state)?;
        if value_real.is_failed() {
            return Ok(None);
        }
        let mut free = HashSet::new();
        crate::instantiate::collect_free_plain_ids(expression, &HashSet::new(), &mut free);
        use PointwiseContinuityConstructorProof as C;
        let constructor = if !free.contains(&parameter) {
            C::Constant
        } else if matches!(expression, Obj::Identifier(IdentifierObj::Plain { id, .. }) if *id == parameter)
        {
            C::Variable
        } else {
            match expression {
                Obj::ArithmeticOperator(ArithmeticOperator::Neg(a)) => {
                    let Some(argument) = self.prove_continuous_expression(
                        &a.arg,
                        parameter,
                        point,
                        state,
                        depth + 1,
                        remaining,
                    )?
                    else {
                        return Ok(None);
                    };
                    C::Neg {
                        argument: Box::new(argument),
                    }
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Abs(a)) => {
                    let Some(argument) = self.prove_continuous_expression(
                        &a.arg,
                        parameter,
                        point,
                        state,
                        depth + 1,
                        remaining,
                    )?
                    else {
                        return Ok(None);
                    };
                    C::Abs {
                        argument: Box::new(argument),
                    }
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Add(a)) => {
                    let Some(left) = self.prove_continuous_expression(
                        &a.left,
                        parameter,
                        point,
                        state,
                        depth + 1,
                        remaining,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some(right) = self.prove_continuous_expression(
                        &a.right,
                        parameter,
                        point,
                        state,
                        depth + 1,
                        remaining,
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
                    let Some(left) = self.prove_continuous_expression(
                        &a.left,
                        parameter,
                        point,
                        state,
                        depth + 1,
                        remaining,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some(right) = self.prove_continuous_expression(
                        &a.right,
                        parameter,
                        point,
                        state,
                        depth + 1,
                        remaining,
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
                    let Some(left) = self.prove_continuous_expression(
                        &a.left,
                        parameter,
                        point,
                        state,
                        depth + 1,
                        remaining,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some(right) = self.prove_continuous_expression(
                        &a.right,
                        parameter,
                        point,
                        state,
                        depth + 1,
                        remaining,
                    )?
                    else {
                        return Ok(None);
                    };
                    C::Mul {
                        left: Box::new(left),
                        right: Box::new(right),
                    }
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Div(a)) => {
                    let Some(left) = self.prove_continuous_expression(
                        &a.left,
                        parameter,
                        point,
                        state,
                        depth + 1,
                        remaining,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some(right) = self.prove_continuous_expression(
                        &a.right,
                        parameter,
                        point,
                        state,
                        depth + 1,
                        remaining,
                    )?
                    else {
                        return Ok(None);
                    };
                    let required = NotEqualFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        left: right.value.clone(),
                        right: Obj::Literal(Literal::Number(Number::new("0".into()))),
                        line_file: None,
                    }
                    .into();
                    let denominator_nonzero = self.verify_fact(&required, state)?;
                    if denominator_nonzero.is_failed() {
                        return Ok(None);
                    }
                    C::Div {
                        left: Box::new(left),
                        right: Box::new(right),
                        denominator_nonzero: Box::new(denominator_nonzero),
                    }
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(a)) => {
                    let mut exponent_free = HashSet::new();
                    crate::instantiate::collect_free_plain_ids(
                        &a.exponent,
                        &HashSet::new(),
                        &mut exponent_free,
                    );
                    if exponent_free.contains(&parameter) {
                        return Ok(None);
                    }
                    let Some(base) = self.prove_continuous_expression(
                        &a.base,
                        parameter,
                        point,
                        state,
                        depth + 1,
                        remaining,
                    )?
                    else {
                        return Ok(None);
                    };
                    let required = InFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        element: *a.exponent.clone(),
                        set: Obj::StandardSet(StandardSet::N),
                        line_file: None,
                    }
                    .into();
                    let exponent_natural = self.verify_fact(&required, state)?;
                    if exponent_natural.is_failed() {
                        return Ok(None);
                    }
                    C::NaturalPower {
                        base: Box::new(base),
                        exponent_natural: Box::new(exponent_natural),
                    }
                }
                Obj::FnObj(call) if call.body.len() == 1 && call.body[0].len() == 1 => {
                    let function = match call.head.as_ref() {
                        FnObjHead::Identifier(a) => Obj::Identifier(a.clone()),
                        FnObjHead::AnonymousFnLiteral(a) => {
                            Obj::FunctionSpace(FunctionSpace::AnonymousFn(*a.clone()))
                        }
                        FnObjHead::Object(a) => *a.clone(),
                        FnObjHead::FieldAccess(a) => Obj::StructAndFieldAccessObj(
                            StructAndFieldAccessObj::FieldAccess(a.clone()),
                        ),
                        FnObjHead::InstantiatedTemplateObj(a) => {
                            Obj::InstantiatedTemplateObj(a.clone())
                        }
                    };
                    let mut function_free = HashSet::new();
                    crate::instantiate::collect_free_plain_ids(
                        &function,
                        &HashSet::new(),
                        &mut function_free,
                    );
                    if function_free.contains(&parameter) {
                        return Ok(None);
                    }
                    let Some(argument) = self.prove_continuous_expression(
                        &call.body[0][0],
                        parameter,
                        point,
                        state,
                        depth + 1,
                        remaining,
                    )?
                    else {
                        return Ok(None);
                    };
                    let required = FunctionContinuousAtFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        function: function.clone(),
                        point: argument.value.clone(),
                        side: RealApproachSide::Both,
                        line_file: None,
                    }
                    .into();
                    let outer_continuity = self.verify_fact(&required, state)?;
                    if outer_continuity.is_failed() {
                        return Ok(None);
                    }
                    C::Compose {
                        function,
                        argument: Box::new(argument),
                        outer_continuity: Box::new(outer_continuity),
                    }
                }
                _ => return Ok(None),
            }
        };
        Ok(Some(PointwiseContinuityExpressionProof {
            expression: expression.clone(),
            value,
            value_real: Box::new(value_real),
            constructor,
        }))
    }
}
