//! Finite smooth-expression certificates, with symbolic coordinate derivatives.
//! No selector WD calls this prover. Unsupported constructors are a soft miss.
use super::super::pointwise_elementary::ElementaryRealFunction;
use super::helper::*;
use crate::prelude::*;
use crate::rational_expression::helper::{add_objs, div_objs, mul_objs, sub_objs};
use std::collections::{HashMap, HashSet};

pub struct SmoothCoordinateExpressionProof {
    pub expression: Obj,
    pub value: Obj,
    pub value_source_well_defined: Box<super::super::ObjWellDefinedProof>,
    pub value_reduction: MultivariableReductionProof,
    pub value_real: Box<VerifyFactResult>,
    pub derivative_expression: Obj,
    pub derivative_value: Obj,
    pub derivative_source_well_defined: Box<super::super::ObjWellDefinedProof>,
    pub derivative_reduction: MultivariableReductionProof,
    pub derivative_real: Box<VerifyFactResult>,
    pub constructor: SmoothCoordinateConstructorProof,
}
pub enum SmoothCoordinateConstructorProof {
    Constant,
    Coordinate {
        index: Obj,
        index_member: Box<VerifyFactResult>,
        axis_comparison: Box<VerifyFactResult>,
    },
    Neg {
        argument: Box<SmoothCoordinateExpressionProof>,
    },
    Add {
        left: Box<SmoothCoordinateExpressionProof>,
        right: Box<SmoothCoordinateExpressionProof>,
    },
    Subtract {
        left: Box<SmoothCoordinateExpressionProof>,
        right: Box<SmoothCoordinateExpressionProof>,
    },
    Multiply {
        left: Box<SmoothCoordinateExpressionProof>,
        right: Box<SmoothCoordinateExpressionProof>,
    },
    Divide {
        left: Box<SmoothCoordinateExpressionProof>,
        right: Box<SmoothCoordinateExpressionProof>,
        nonzero: Box<VerifyFactResult>,
    },
    NaturalPower {
        base: Box<SmoothCoordinateExpressionProof>,
        exponent_natural: Box<VerifyFactResult>,
    },
    Elementary {
        kind: ElementaryRealFunction,
        argument: Box<SmoothCoordinateExpressionProof>,
        domain: Box<VerifyFactResult>,
    },
}
pub struct MultivariableReductionProof {
    pub source: Obj,
    pub result: Obj,
    pub steps: Vec<MultivariableReductionStep>,
}
pub enum MultivariableReductionStep {
    ExactRational {source:Obj,value:Obj},
    PeriodicTrig {source:Obj,proof:crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_periodic_trig::PeriodicTrigBuiltinRuleProof},
    NativeMatrixBeta {source:Box<super::super::native_matrix::MatrixCallableProof>,arguments:Vec<Obj>},
    FiniteSetEvaluation {source:Obj,left:crate::rational_expression::exact_rational::EvalRational,right:crate::rational_expression::exact_rational::EvalRational,value:Obj},
    AnonymousBeta {function:AnonymousFn,arguments:Vec<Obj>},
    TupleProjection {tuple:Tuple,index:usize},
}
pub(crate) fn depends_on(expression: &Obj, parameter: IdentifierId) -> bool {
    let mut free = HashSet::new();
    crate::instantiate::collect_free_plain_ids(expression, &HashSet::new(), &mut free);
    free.contains(&parameter)
}
pub(crate) fn literal_dimension(obj: &Obj) -> Option<usize> {
    let Obj::Literal(Literal::Number(n)) = obj else {
        return None;
    };
    let value = n.normalized_value.parse::<usize>().ok()?;
    if (1..=16).contains(&value) {
        Some(value)
    } else {
        None
    }
}
fn is_number(obj: &Obj, n: i64) -> bool {
    obj == &number(n)
}
fn plus(a: Obj, b: Obj) -> Obj {
    if is_number(&a, 0) {
        b
    } else if is_number(&b, 0) {
        a
    } else {
        add_objs(a, b)
    }
}
fn times(a: Obj, b: Obj) -> Obj {
    if is_number(&a, 0) || is_number(&b, 0) {
        number(0)
    } else if is_number(&a, 1) {
        b
    } else if is_number(&b, 1) {
        a
    } else {
        mul_objs(a, b)
    }
}
fn minus(a: Obj, b: Obj) -> Obj {
    if a == b {
        number(0)
    } else if is_number(&b, 0) {
        a
    } else {
        sub_objs(a, b)
    }
}
fn power(a: Obj, b: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
        base: Box::new(a),
        exponent: Box::new(b),
    }))
}
pub(crate) fn call_head(head: &FnObjHead) -> Obj {
    match head {
        FnObjHead::Identifier(x) => Obj::Identifier(x.clone()),
        FnObjHead::AnonymousFnLiteral(x) => {
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(*x.clone()))
        }
        FnObjHead::Object(x) => *x.clone(),
        FnObjHead::FieldAccess(x) => {
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(x.clone()))
        }
        FnObjHead::InstantiatedTemplateObj(x) => Obj::InstantiatedTemplateObj(x.clone()),
    }
}
impl Runtime {
    pub(crate) fn reduce_multivariable_expression(
        &mut self,
        source: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<Option<MultivariableReductionProof>> {
        let mut steps = Vec::new();
        let mut budget = 512;
        let Some(result) =
            self.reduce_multivariable_inner(source, &mut steps, 0, &mut budget, state)?
        else {
            return Ok(None);
        };
        Ok(Some(MultivariableReductionProof {
            source: source.clone(),
            result,
            steps,
        }))
    }
    fn reduce_multivariable_inner(
        &mut self,
        source: &Obj,
        steps: &mut Vec<MultivariableReductionStep>,
        depth: usize,
        budget: &mut usize,
        state: VerifyState,
    ) -> RuntimeResult<Option<Obj>> {
        if depth >= 64 || *budget == 0 {
            return Ok(None);
        }
        *budget -= 1;
        if let Some(value) =
            crate::rational_expression::exact_rational::evaluate_obj_to_exact_rational_obj_for_eval(
                source,
            )
        {
            if value != *source {
                steps.push(MultivariableReductionStep::ExactRational {
                    source: source.clone(),
                    value: value.clone(),
                });
            }
            return Ok(Some(value));
        }
        if let Some(proof) = self.periodic_trig_value(source, state)? {
            let value = proof.value.clone();
            steps.push(MultivariableReductionStep::PeriodicTrig {
                source: source.clone(),
                proof,
            });
            return Ok(Some(value));
        }
        // Reuse exact finite-singleton evaluation, with closed rational operands.
        // This classification proves the set finite and excludes undefined terms;
        // it does not reopen a weaker-ceiling WD search on generated cardinality.
        if let Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(size)) = source {
            if let Obj::SetOperator(SetOperator::Intersect(intersection)) = size.set.as_ref() {
                if let (
                    Obj::SetFormer(SetFormer::ListSet(left)),
                    Obj::SetFormer(SetFormer::ListSet(right)),
                ) = (intersection.left.as_ref(), intersection.right.as_ref())
                {
                    if left.list.len() == 1 && right.list.len() == 1 {
                        if let (Some(left), Some(right)) = (
                            crate::rational_expression::exact_rational::EvalRational::from_obj(
                                &left.list[0],
                            ),
                            crate::rational_expression::exact_rational::EvalRational::from_obj(
                                &right.list[0],
                            ),
                        ) {
                            let mut context =
                                crate::execute::execute_eval_stmt::helper::ActiveAlgoCalls::new();
                            context.proof_mode = true;
                            context.function_proof_state = state;
                            if let Ok(value) =
                                crate::execute::execute_eval_stmt::evaluate_finite_object(
                                    self,
                                    source,
                                    0,
                                    &mut context,
                                )?
                            {
                                if context.function_evaluations.is_empty()
                                    && context.algo_evaluations.is_empty()
                                    && context.aggregate_evaluations.is_empty()
                                    && context.matrix_scalar_evaluations.is_empty()
                                    && context.cited_equal_fact_ids.is_empty()
                                {
                                    steps.push(MultivariableReductionStep::FiniteSetEvaluation {
                                        source: source.clone(),
                                        left,
                                        right,
                                        value: value.clone(),
                                    });
                                    return Ok(Some(value));
                                }
                            }
                        }
                    }
                }
            }
        }
        if let Obj::FnObj(call) = source {
            let Some(mut current) = self.reduce_multivariable_inner(
                &call_head(&call.head),
                steps,
                depth + 1,
                budget,
                state,
            )?
            else {
                return Ok(None);
            };
            for group in &call.body {
                let mut args = Vec::new();
                for arg in group {
                    let Some(a) =
                        self.reduce_multivariable_inner(arg, steps, depth + 1, budget, state)?
                    else {
                        return Ok(None);
                    };
                    args.push(a);
                }
                if let Obj::FunctionSpace(FunctionSpace::AnonymousFn(body)) = &current {
                    // Guarded calls require a local domain theorem; do not erase it by beta reduction.
                    let params: Vec<_> = body
                        .body
                        .set_bound_parameters
                        .groups
                        .iter()
                        .flat_map(|g| &g.params)
                        .collect();
                    if body.body.dom_facts.is_empty() && params.len() == args.len() {
                        let map = params
                            .iter()
                            .zip(&args)
                            .map(|(p, a)| (p.id, a.clone()))
                            .collect();
                        let Ok(result) = self.inst_obj(&body.equal_to, &map) else {
                            return Ok(None);
                        };
                        steps.push(MultivariableReductionStep::AnonymousBeta {
                            function: body.clone(),
                            arguments: args,
                        });
                        let Some(next) = self.reduce_multivariable_inner(
                            &result,
                            steps,
                            depth + 1,
                            budget,
                            state,
                        )?
                        else {
                            return Ok(None);
                        };
                        current = next;
                        continue;
                    }
                }
                if matches!(current, Obj::MatrixOperator(_)) {
                    let sources = self.matrix_callables(&current, state)?;
                    for source in sources.into_iter().take(1) {
                        let params: Vec<_> = source
                            .function
                            .body
                            .set_bound_parameters
                            .groups
                            .iter()
                            .flat_map(|g| &g.params)
                            .collect();
                        if source.function.body.dom_facts.is_empty() && params.len() == args.len() {
                            let map = params
                                .iter()
                                .zip(&args)
                                .map(|(p, a)| (p.id, a.clone()))
                                .collect();
                            let Ok(result) = self.inst_obj(&source.function.equal_to, &map) else {
                                return Ok(None);
                            };
                            steps.push(MultivariableReductionStep::NativeMatrixBeta {
                                source: Box::new(source),
                                arguments: args.clone(),
                            });
                            let Some(next) = self.reduce_multivariable_inner(
                                &result,
                                steps,
                                depth + 1,
                                budget,
                                state,
                            )?
                            else {
                                return Ok(None);
                            };
                            current = next;
                            break;
                        }
                    }
                    if !matches!(current, Obj::MatrixOperator(_)) {
                        continue;
                    }
                }
                if let Obj::ProductShape(ProductShape::Tuple(tuple)) = &current {
                    if args.len() == 1 {
                        if let Some(index) = literal_dimension(&args[0]) {
                            if let Some(result) = tuple.args.get(index - 1) {
                                steps.push(MultivariableReductionStep::TupleProjection {
                                    tuple: tuple.clone(),
                                    index,
                                });
                                current = *result.clone();
                                continue;
                            }
                        }
                    }
                }
                current = apply(&current, args);
            }
            return Ok(Some(current));
        }
        if let Some((kind, arg)) = ElementaryRealFunction::from_expression(source) {
            let Some(a) = self.reduce_multivariable_inner(arg, steps, depth + 1, budget, state)?
            else {
                return Ok(None);
            };
            let result = kind.apply(a);
            if result == *source {
                return Ok(Some(result));
            }
            return self.reduce_multivariable_inner(&result, steps, depth + 1, budget, state);
        }
        if let Obj::ArithmeticOperator(op) = source {
            let pair = match op {
                ArithmeticOperator::Add(x) => Some((&x.left, &x.right)),
                ArithmeticOperator::Sub(x) => Some((&x.left, &x.right)),
                ArithmeticOperator::Mul(x) => Some((&x.left, &x.right)),
                ArithmeticOperator::Div(x) => Some((&x.left, &x.right)),
                ArithmeticOperator::Pow(x) => Some((&x.base, &x.exponent)),
                _ => None,
            };
            if let Some((a, b)) = pair {
                let Some(a) =
                    self.reduce_multivariable_inner(a, steps, depth + 1, budget, state)?
                else {
                    return Ok(None);
                };
                let Some(b) =
                    self.reduce_multivariable_inner(b, steps, depth + 1, budget, state)?
                else {
                    return Ok(None);
                };
                let result = match op {
                    ArithmeticOperator::Add(_) => add_objs(a, b),
                    ArithmeticOperator::Sub(_) => sub_objs(a, b),
                    ArithmeticOperator::Mul(_) => mul_objs(a, b),
                    ArithmeticOperator::Div(_) => div_objs(a, b),
                    ArithmeticOperator::Pow(_) => power(a, b),
                    _ => unreachable!(),
                };
                if result == *source {
                    return Ok(Some(result));
                }
                return self.reduce_multivariable_inner(&result, steps, depth + 1, budget, state);
            }
            if let ArithmeticOperator::Neg(a) = op {
                return Ok(self
                    .reduce_multivariable_inner(&a.arg, steps, depth + 1, budget, state)?
                    .map(negate));
            }
        }
        Ok(Some(source.clone()))
    }
    pub(crate) fn prove_smooth_coordinate_expression(
        &mut self,
        expression: &Obj,
        parameter: IdentifierId,
        point: &Obj,
        n: &Obj,
        axis: &Obj,
        state: VerifyState,
        depth: usize,
        budget: &mut usize,
    ) -> RuntimeResult<Option<SmoothCoordinateExpressionProof>> {
        if depth >= 64 || *budget == 0 {
            return Ok(None);
        }
        *budget -= 1;
        let Ok(evaluated) = self.inst_obj(expression, &HashMap::from([(parameter, point.clone())]))
        else {
            return Ok(None);
        };
        let super::super::VerifyObjWellDefinedResult::Success(value_source_well_defined) =
            self.verify_obj_well_definedness(&evaluated, state)?
        else {
            return Ok(None);
        };
        let Some(reduction) = self.reduce_multivariable_expression(&evaluated, state)? else {
            return Ok(None);
        };
        // Reduction steps are separately retained by the source proof for bound components.
        // At the point, exact evaluation uses the ordinary expression verifier.
        let value = reduction.result.clone();
        let real_fact = member(self, value.clone(), real());
        let value_real = self.verify_fact(&real_fact, state)?;
        if value_real.is_failed() {
            return Ok(None);
        }
        use SmoothCoordinateConstructorProof as C;
        let (derivative_expression, constructor) = if !depends_on(expression, parameter) {
            (number(0), C::Constant)
        } else if let Obj::FnObj(call) = expression {
            if call.body.len() != 1 || call.body[0].len() != 1 {
                return Ok(None);
            }
            if !matches!(call_head(&call.head),Obj::Identifier(IdentifierObj::Plain{id,..}) if id==parameter)
            {
                return Ok(None);
            }
            let index = call.body[0][0].as_ref();
            if depends_on(index, parameter) {
                return Ok(None);
            }
            let fact = member(self, index.clone(), indices(n.clone()));
            let index_member = self.verify_fact(&fact, state)?;
            if index_member.is_failed() {
                return Ok(None);
            }
            let fact = equal(self, index.clone(), axis.clone());
            let same = self.verify_fact(&fact, state)?;
            let (slope, axis_comparison) = if !same.is_failed() {
                (number(1), same)
            } else {
                let fact: Fact = NotEqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: index.clone(),
                    right: axis.clone(),
                    line_file: None,
                }
                .into();
                let different = self.verify_fact(&fact, state)?;
                if different.is_failed() {
                    return Ok(None);
                }
                (number(0), different)
            };
            (
                slope,
                C::Coordinate {
                    index: index.clone(),
                    index_member: Box::new(index_member),
                    axis_comparison: Box::new(axis_comparison),
                },
            )
        } else if let Some((kind, arg)) = ElementaryRealFunction::from_expression(expression) {
            let Some(argument) = self.prove_smooth_coordinate_expression(
                arg,
                parameter,
                point,
                n,
                axis,
                state,
                depth + 1,
                budget,
            )?
            else {
                return Ok(None);
            };
            let condition = self.elementary_real_condition(kind, argument.value.clone(), true);
            let domain = self.verify_fact(&condition, state)?;
            if domain.is_failed() {
                return Ok(None);
            }
            let derivative = kind.derivative(
                argument.expression.clone(),
                argument.derivative_expression.clone(),
            );
            (
                derivative,
                C::Elementary {
                    kind,
                    argument: Box::new(argument),
                    domain: Box::new(domain),
                },
            )
        } else if let Obj::ArithmeticOperator(op) = expression {
            if let ArithmeticOperator::Neg(arg) = op {
                let Some(argument) = self.prove_smooth_coordinate_expression(
                    &arg.arg,
                    parameter,
                    point,
                    n,
                    axis,
                    state,
                    depth + 1,
                    budget,
                )?
                else {
                    return Ok(None);
                };
                (
                    negate(argument.derivative_expression.clone()),
                    C::Neg {
                        argument: Box::new(argument),
                    },
                )
            } else if let ArithmeticOperator::Pow(arg) = op {
                if depends_on(&arg.exponent, parameter) {
                    return Ok(None);
                }
                let condition = member(
                    self,
                    *arg.exponent.clone(),
                    Obj::StandardSet(StandardSet::N),
                );
                let exponent_natural = self.verify_fact(&condition, state)?;
                if exponent_natural.is_failed() {
                    return Ok(None);
                }
                let Some(base) = self.prove_smooth_coordinate_expression(
                    &arg.base,
                    parameter,
                    point,
                    n,
                    axis,
                    state,
                    depth + 1,
                    budget,
                )?
                else {
                    return Ok(None);
                };
                let exponent = sub_objs(
                    Obj::ArithmeticOperator(ArithmeticOperator::Max(Max {
                        left: arg.exponent.clone(),
                        right: Box::new(number(1)),
                    })),
                    number(1),
                );
                let derivative = times(
                    times(
                        *arg.exponent.clone(),
                        power(base.expression.clone(), exponent),
                    ),
                    base.derivative_expression.clone(),
                );
                (
                    derivative,
                    C::NaturalPower {
                        base: Box::new(base),
                        exponent_natural: Box::new(exponent_natural),
                    },
                )
            } else {
                let (a, b) = match op {
                    ArithmeticOperator::Add(x) => (&x.left, &x.right),
                    ArithmeticOperator::Sub(x) => (&x.left, &x.right),
                    ArithmeticOperator::Mul(x) => (&x.left, &x.right),
                    ArithmeticOperator::Div(x) => (&x.left, &x.right),
                    _ => return Ok(None),
                };
                let Some(left) = self.prove_smooth_coordinate_expression(
                    a,
                    parameter,
                    point,
                    n,
                    axis,
                    state,
                    depth + 1,
                    budget,
                )?
                else {
                    return Ok(None);
                };
                let Some(right) = self.prove_smooth_coordinate_expression(
                    b,
                    parameter,
                    point,
                    n,
                    axis,
                    state,
                    depth + 1,
                    budget,
                )?
                else {
                    return Ok(None);
                };
                let dl = left.derivative_expression.clone();
                let dr = right.derivative_expression.clone();
                let derivative = match op {
                    ArithmeticOperator::Add(_) => plus(dl, dr),
                    ArithmeticOperator::Sub(_) => minus(dl, dr),
                    ArithmeticOperator::Mul(_) => plus(
                        times(dl, right.expression.clone()),
                        times(left.expression.clone(), dr),
                    ),
                    ArithmeticOperator::Div(_) => div_objs(
                        div_objs(
                            minus(
                                times(dl, right.expression.clone()),
                                times(left.expression.clone(), dr),
                            ),
                            right.expression.clone(),
                        ),
                        right.expression.clone(),
                    ),
                    _ => unreachable!(),
                };
                let constructor = match op {
                    ArithmeticOperator::Add(_) => C::Add {
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    ArithmeticOperator::Sub(_) => C::Subtract {
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    ArithmeticOperator::Mul(_) => C::Multiply {
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    ArithmeticOperator::Div(_) => {
                        let condition = nonzero(self, right.value.clone());
                        let nonzero = self.verify_fact(&condition, state)?;
                        if nonzero.is_failed() {
                            return Ok(None);
                        }
                        C::Divide {
                            left: Box::new(left),
                            right: Box::new(right),
                            nonzero: Box::new(nonzero),
                        }
                    }
                    _ => unreachable!(),
                };
                (derivative, constructor)
            }
        } else {
            return Ok(None);
        };
        let Ok(derivative_value) = self.inst_obj(
            &derivative_expression,
            &HashMap::from([(parameter, point.clone())]),
        ) else {
            return Ok(None);
        };
        let super::super::VerifyObjWellDefinedResult::Success(derivative_source_well_defined) =
            self.verify_obj_well_definedness(&derivative_value, state)?
        else {
            return Ok(None);
        };
        let Some(derivative_reduction) =
            self.reduce_multivariable_expression(&derivative_value, state)?
        else {
            return Ok(None);
        };
        let derivative_value = derivative_reduction.result.clone();
        let real_fact = member(self, derivative_value.clone(), real());
        let derivative_real = self.verify_fact(&real_fact, state)?;
        if derivative_real.is_failed() {
            return Ok(None);
        }
        Ok(Some(SmoothCoordinateExpressionProof {
            expression: expression.clone(),
            value,
            value_source_well_defined: Box::new(value_source_well_defined),
            value_reduction: reduction,
            value_real: Box::new(value_real),
            derivative_expression,
            derivative_value,
            derivative_source_well_defined: Box::new(derivative_source_well_defined),
            derivative_reduction,
            derivative_real: Box::new(derivative_real),
            constructor,
        }))
    }
}
