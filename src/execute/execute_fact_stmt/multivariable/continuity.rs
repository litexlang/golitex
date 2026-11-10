//! Joint continuity follows the expression constructors, independently of derivatives.
use super::super::pointwise_elementary::ElementaryRealFunction;
use super::expression::{call_head, depends_on, literal_dimension, MultivariableReductionProof};
use super::helper::*;
use crate::prelude::*;
use std::collections::HashMap;

pub struct ContinuousExpressionProof {
    pub expression: Obj,
    pub value: Obj,
    pub value_source_well_defined: Box<ObjWellDefinedProof>,
    pub value_reduction: MultivariableReductionProof,
    pub value_real: Box<VerifyFactResult>,
    pub constructor: ContinuousExpressionConstructorProof,
}

pub enum ContinuousExpressionConstructorProof {
    Constant,
    Coordinate {
        index: Obj,
        index_member: Box<VerifyFactResult>,
    },
    Neg {
        argument: Box<ContinuousExpressionProof>,
    },
    Abs {
        argument: Box<ContinuousExpressionProof>,
    },
    Add {
        left: Box<ContinuousExpressionProof>,
        right: Box<ContinuousExpressionProof>,
    },
    Subtract {
        left: Box<ContinuousExpressionProof>,
        right: Box<ContinuousExpressionProof>,
    },
    Multiply {
        left: Box<ContinuousExpressionProof>,
        right: Box<ContinuousExpressionProof>,
    },
    Divide {
        left: Box<ContinuousExpressionProof>,
        right: Box<ContinuousExpressionProof>,
        nonzero: Box<VerifyFactResult>,
    },
    NaturalPower {
        base: Box<ContinuousExpressionProof>,
        exponent_natural: Box<VerifyFactResult>,
    },
    Elementary {
        kind: ElementaryRealFunction,
        argument: Box<ContinuousExpressionProof>,
        domain: Box<VerifyFactResult>,
    },
}

pub struct ContinuousMultivariableCoordinateProof {
    pub row: usize,
    pub reduction: MultivariableReductionProof,
    pub expression: ContinuousExpressionProof,
}

impl Runtime {
    pub(crate) fn prove_multivariable_continuous_expression(
        &mut self,
        expression: &Obj,
        parameter: IdentifierId,
        point: &Obj,
        n: &Obj,
        state: VerifyState,
        depth: usize,
        budget: &mut usize,
    ) -> RuntimeResult<Option<ContinuousExpressionProof>> {
        if depth >= 64 || *budget == 0 {
            return Ok(None);
        }
        *budget -= 1;
        let Ok(evaluated) = self.inst_obj(expression, &HashMap::from([(parameter, point.clone())]))
        else {
            return Ok(None);
        };
        let VerifyObjWellDefinedResult::Success(value_source_well_defined) =
            self.verify_obj_well_definedness(&evaluated, state)?
        else {
            return Ok(None);
        };
        let Some(value_reduction) = self.reduce_multivariable_expression(&evaluated, state)? else {
            return Ok(None);
        };
        let value = value_reduction.result.clone();
        let real = member(self, value.clone(), real());
        let value_real = self.verify_fact(&real, state)?;
        if value_real.is_failed() {
            return Ok(None);
        }
        use ContinuousExpressionConstructorProof as C;
        let constructor = if !depends_on(expression, parameter) {
            C::Constant
        } else if let Some(index) = coordinate_index(expression, parameter) {
            let condition = member(self, index.clone(), indices(n.clone()));
            let index_member = self.verify_fact(&condition, state)?;
            if index_member.is_failed() {
                return Ok(None);
            }
            C::Coordinate {
                index: index.clone(),
                index_member: Box::new(index_member),
            }
        } else if let Some((kind, arg)) = ElementaryRealFunction::from_expression(expression) {
            let Some(argument) = self.prove_multivariable_continuous_expression(
                arg,
                parameter,
                point,
                n,
                state,
                depth + 1,
                budget,
            )?
            else {
                return Ok(None);
            };
            let condition = self.elementary_real_condition(kind, argument.value.clone(), false);
            let domain = self.verify_fact(&condition, state)?;
            if domain.is_failed() {
                return Ok(None);
            }
            C::Elementary {
                kind,
                argument: Box::new(argument),
                domain: Box::new(domain),
            }
        } else if let Obj::ArithmeticOperator(op) = expression {
            match op {
                ArithmeticOperator::Neg(Neg { arg }) | ArithmeticOperator::Abs(Abs { arg }) => {
                    let Some(argument) = self.prove_multivariable_continuous_expression(
                        arg,
                        parameter,
                        point,
                        n,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    if matches!(op, ArithmeticOperator::Abs(_)) {
                        C::Abs {
                            argument: Box::new(argument),
                        }
                    } else {
                        C::Neg {
                            argument: Box::new(argument),
                        }
                    }
                }
                ArithmeticOperator::Pow(power) => {
                    if depends_on(&power.exponent, parameter) {
                        return Ok(None);
                    }
                    let condition = member(
                        self,
                        *power.exponent.clone(),
                        Obj::StandardSet(StandardSet::N),
                    );
                    let exponent_natural = self.verify_fact(&condition, state)?;
                    if exponent_natural.is_failed() {
                        return Ok(None);
                    }
                    let Some(base) = self.prove_multivariable_continuous_expression(
                        &power.base,
                        parameter,
                        point,
                        n,
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
                _ => {
                    let (left, right) = match op {
                        ArithmeticOperator::Add(p) => (&p.left, &p.right),
                        ArithmeticOperator::Sub(p) => (&p.left, &p.right),
                        ArithmeticOperator::Mul(p) => (&p.left, &p.right),
                        ArithmeticOperator::Div(p) => (&p.left, &p.right),
                        _ => return Ok(None),
                    };
                    let Some(left) = self.prove_multivariable_continuous_expression(
                        left,
                        parameter,
                        point,
                        n,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some(right) = self.prove_multivariable_continuous_expression(
                        right,
                        parameter,
                        point,
                        n,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    let (left, right) = (Box::new(left), Box::new(right));
                    match op {
                        ArithmeticOperator::Add(_) => C::Add { left, right },
                        ArithmeticOperator::Sub(_) => C::Subtract { left, right },
                        ArithmeticOperator::Mul(_) => C::Multiply { left, right },
                        ArithmeticOperator::Div(_) => {
                            let condition = nonzero(self, right.value.clone());
                            let nonzero = self.verify_fact(&condition, state)?;
                            if nonzero.is_failed() {
                                return Ok(None);
                            }
                            C::Divide {
                                left,
                                right,
                                nonzero: Box::new(nonzero),
                            }
                        }
                        _ => unreachable!(),
                    }
                }
            }
        } else {
            return Ok(None);
        };
        Ok(Some(ContinuousExpressionProof {
            expression: expression.clone(),
            value,
            value_source_well_defined: Box::new(value_source_well_defined),
            value_reduction,
            value_real: Box::new(value_real),
            constructor,
        }))
    }

    pub(super) fn prove_continuous_multivariable_body(
        &mut self,
        relation: &MultivariableAnalysisRelation,
        body: &AnonymousFn,
        parameter: IdentifierId,
        point: &Obj,
        n: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<
        Option<(
            Vec<ContinuousMultivariableCoordinateProof>,
            Vec<super::strategy::MultivariableReducedEqualityProof>,
        )>,
    > {
        use MultivariableAnalysisRelation as R;
        if !matches!(
            relation,
            R::ScalarLimit(_)
                | R::VectorLimit(_)
                | R::ScalarContinuousAt(_)
                | R::VectorContinuousAt(_)
                | R::ScalarDifferentiableAt(_)
                | R::TotalDifferentiableAt(_)
        ) {
            return Ok(None);
        }
        let output = function_output_dimension(relation);
        let rows = match output.as_ref() {
            Some(m) => {
                let Some(count) = literal_dimension(m) else {
                    return Ok(None);
                };
                count
            }
            None => 1,
        };
        let mut coordinates = Vec::new();
        let mut equalities = Vec::new();
        let mut budget = 4096;
        for row in 1..=rows {
            let raw = if output.is_some() {
                apply(&body.equal_to, vec![number(row as i64)])
            } else {
                *body.equal_to.clone()
            };
            let Some(reduction) = self.reduce_multivariable_expression(&raw, state)? else {
                return Ok(None);
            };
            let Some(expression) = self.prove_multivariable_continuous_expression(
                &reduction.result,
                parameter,
                point,
                n,
                state,
                0,
                &mut budget,
            )?
            else {
                return Ok(None);
            };
            let target = match relation {
                R::ScalarLimit(p) => Some(p.value.clone()),
                R::VectorLimit(p) => Some(apply(&p.value, vec![number(row as i64)])),
                _ => None,
            };
            if let Some(target) = target {
                let Some(target_reduction) =
                    self.reduce_multivariable_expression(&target, state)?
                else {
                    return Ok(None);
                };
                let condition = equal(
                    self,
                    expression.value.clone(),
                    target_reduction.result.clone(),
                );
                let equality = self.verify_fact(&condition, state)?;
                if equality.is_failed() {
                    return Ok(None);
                }
                equalities.push(super::strategy::MultivariableReducedEqualityProof {
                    target_reduction,
                    equality: Box::new(equality),
                });
            }
            coordinates.push(ContinuousMultivariableCoordinateProof {
                row,
                reduction,
                expression,
            });
        }
        Ok(Some((coordinates, equalities)))
    }
}

impl Runtime {
    // Whole-expression differentiability is independent of a selected axis.
    // Continuous constructors supply the common tree; sqrt needs the stronger
    // positive-at-point condition, and abs is deliberately excluded.
    pub(super) fn prove_expression_smoothness(
        &mut self,
        expression: &ContinuousExpressionProof,
        state: VerifyState,
        domains: &mut Vec<VerifyFactResult>,
    ) -> RuntimeResult<bool> {
        use ContinuousExpressionConstructorProof as C;
        Ok(match &expression.constructor {
            C::Constant | C::Coordinate { .. } => true,
            C::Abs { .. } => false,
            C::Neg { argument } | C::NaturalPower { base: argument, .. } => {
                self.prove_expression_smoothness(argument, state, domains)?
            }
            C::Add { left, right }
            | C::Subtract { left, right }
            | C::Multiply { left, right }
            | C::Divide { left, right, .. } => {
                self.prove_expression_smoothness(left, state, domains)?
                    && self.prove_expression_smoothness(right, state, domains)?
            }
            C::Elementary { kind, argument, .. } => {
                if !self.prove_expression_smoothness(argument, state, domains)? {
                    return Ok(false);
                }
                let condition = self.elementary_real_condition(*kind, argument.value.clone(), true);
                let proof = self.verify_fact(&condition, state)?;
                if proof.is_failed() {
                    return Ok(false);
                }
                domains.push(proof);
                true
            }
        })
    }
}

pub(super) fn coordinate_index(expression: &Obj, parameter: IdentifierId) -> Option<&Obj> {
    let Obj::FnObj(call) = expression else {
        return None;
    };
    if call.body.len() != 1
        || call.body[0].len() != 1
        || !matches!(call_head(&call.head), Obj::Identifier(IdentifierObj::Plain { id, .. }) if id == parameter)
        || depends_on(&call.body[0][0], parameter)
    {
        return None;
    }
    Some(&call.body[0][0])
}
