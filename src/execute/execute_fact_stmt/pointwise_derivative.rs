//! Classical derivative certificates built by descending a finite expression tree.
#[cfg(test)]
#[path = "../../../tests/unit/execute/pointwise_analysis/derivative.rs"]
mod pointwise_derivative_tests;
use super::function_domain::function_domains_alpha_equal;
use super::function_limit::RealFunctionLimitDomainProof;
use super::helper::multiply_derivative_terms;
use super::pointwise_continuity::PointwiseContinuityExpressionProof;
use super::pointwise_elementary::ElementaryRealFunction;
use super::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use super::well_defined_results::verify_obj::*;
use crate::prelude::*;
use crate::rational_expression::helper::{add_objs, div_objs, mul_objs, sub_objs};
use std::collections::{HashMap, HashSet};

pub struct PointwiseDerivativeProof {
    pub function: Obj,
    pub point: Obj,
    pub domain: Box<RealFunctionLimitDomainProof>,
    pub body: AnonymousFn,
    pub body_equal: KnownEqualityPathProof,
    pub body_well_defined: Box<ObjWellDefinedProof>,
    pub interior: PointInteriorProof,
    pub expression: DerivativeExpressionProof,
    pub conclusion: DerivativeConclusionProof,
}
pub enum DerivativeConclusionProof {
    Candidate(Box<VerifyFactResult>),
    Differentiable,
}
pub enum PointInteriorProof {
    Known {
        condition: Fact,
        proof: Box<VerifyFactResult>,
    },
    StandardOpen {
        set: StandardSet,
        domain_equal: Box<EqualFactSearchedProof>,
        point_member: Box<VerifyFactResult>,
    },
    Guarded {
        base: Box<PointInteriorProof>,
        point_member: Box<VerifyFactResult>,
        guards: Vec<InteriorGuardProof>,
    },
}
pub struct InteriorGuardProof {
    pub guard: AtomicFact,
    pub point_fact: Fact,
    pub point_proof: Box<VerifyFactResult>,
    pub operands: Vec<InteriorOperandProof>,
}
pub enum InteriorOperandProof {
    Continuous(PointwiseContinuityExpressionProof),
    Differentiable(DerivativeExpressionProof),
}
pub struct DerivativeExpressionProof {
    pub expression: Obj,
    pub value: Obj,
    pub value_real: Box<VerifyFactResult>,
    pub derivative: Obj,
    pub derivative_real: Box<VerifyFactResult>,
    pub constructor: DerivativeConstructorProof,
}
pub enum DerivativeConstructorProof {
    Elementary {
        kind: ElementaryRealFunction,
        argument: Box<DerivativeExpressionProof>,
        domain: Box<VerifyFactResult>,
    },
    Constant,
    Variable,
    Neg {
        argument: Box<DerivativeExpressionProof>,
    },
    Add {
        left: Box<DerivativeExpressionProof>,
        right: Box<DerivativeExpressionProof>,
    },
    Sub {
        left: Box<DerivativeExpressionProof>,
        right: Box<DerivativeExpressionProof>,
    },
    Mul {
        left: Box<DerivativeExpressionProof>,
        right: Box<DerivativeExpressionProof>,
    },
    Div {
        left: Box<DerivativeExpressionProof>,
        right: Box<DerivativeExpressionProof>,
        denominator_nonzero: Box<VerifyFactResult>,
    },
    NaturalPower {
        base: Box<DerivativeExpressionProof>,
        exponent_natural: Box<VerifyFactResult>,
    },
    Compose {
        function: Obj,
        argument: Box<DerivativeExpressionProof>,
        outer: DerivativeLeafProof,
    },
}
pub enum DerivativeLeafProof {
    Candidate(AtomicExceptEqualityFactKnownProof),
    Selected {
        differentiability: Box<VerifyFactResult>,
        value_well_defined: Box<ObjWellDefinedProof>,
    },
}
fn real() -> Obj {
    Obj::StandardSet(StandardSet::R)
}
fn number(n: &str) -> Obj {
    Obj::Literal(Literal::Number(Number::new(n.into())))
}
fn depends(expression: &Obj, id: IdentifierId) -> bool {
    let mut free = HashSet::new();
    crate::instantiate::collect_free_plain_ids(expression, &HashSet::new(), &mut free);
    free.contains(&id)
}
fn function_head(head: &FnObjHead) -> Obj {
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
impl Runtime {
    pub(crate) fn search_pointwise_derivative_strategy(
        &mut self,
        goal: &AtomicFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<PointwiseDerivativeProof>> {
        let (function, point, value) = match goal {
            AtomicFact::HasDerivativeAtFact(f) => (&f.function, &f.point, Some(&f.value)),
            AtomicFact::FunctionDifferentiableAtFact(f) => (&f.function, &f.point, None),
            _ => return Ok(None),
        };
        let Some(domain) = self.checked_real_function_limit_domain(function, state)? else {
            return Ok(None);
        };
        let mut budget = 512;
        for (literal, path) in
            self.exact_property_object_values_of_shapes(function, &[EqualToObjShape::AnonymousFn])
        {
            if budget == 0 {
                break;
            }
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
            let VerifyObjWellDefinedResult::Success(body_well_defined) =
                self.verify_obj_well_definedness(&literal, state)?
            else {
                continue;
            };
            let Some(interior) =
                self.prove_point_interior(&domain.domain, point, state, 0, &mut budget)?
            else {
                continue;
            };
            let Some(expression) = self.prove_derivative_expression(
                &body.equal_to,
                params[0].id,
                point,
                state,
                0,
                &mut budget,
            )?
            else {
                continue;
            };
            let conclusion = match value {
                Some(value) => {
                    let equal: Fact = EqualFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        left: expression.derivative.clone(),
                        right: value.clone(),
                        line_file: None,
                    }
                    .into();
                    let proof = self.verify_fact(&equal, state)?;
                    if proof.is_failed() {
                        continue;
                    }
                    DerivativeConclusionProof::Candidate(Box::new(proof))
                }
                None => DerivativeConclusionProof::Differentiable,
            };
            return Ok(Some(PointwiseDerivativeProof {
                function: function.clone(),
                point: point.clone(),
                domain: Box::new(domain),
                body: body.clone(),
                body_equal: KnownEqualityPathProof::new(path),
                body_well_defined: Box::new(body_well_defined),
                interior,
                expression,
                conclusion,
            }));
        }
        Ok(None)
    }
    pub(crate) fn prove_point_interior(
        &mut self,
        domain: &Obj,
        point: &Obj,
        state: VerifyState,
        depth: usize,
        budget: &mut usize,
    ) -> RuntimeResult<Option<PointInteriorProof>> {
        if depth >= 64 || *budget == 0 {
            return Ok(None);
        }
        *budget -= 1;
        let condition = self.derivative_interior_condition(domain.clone(), point.clone());
        let proof = self.verify_fact(&condition, state)?;
        if !proof.is_failed() {
            return Ok(Some(PointInteriorProof::Known {
                condition,
                proof: Box::new(proof),
            }));
        }
        for set in [
            StandardSet::R,
            StandardSet::RPos,
            StandardSet::RNeg,
            StandardSet::RStar,
        ] {
            let Some(equal) =
                self.lookup_exact_property_obj_equality(domain, &Obj::StandardSet(set.clone()))
            else {
                continue;
            };
            let member: Fact = InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: point.clone(),
                set: domain.clone(),
                line_file: None,
            }
            .into();
            let point_member = self.verify_fact(&member, state)?;
            if !point_member.is_failed() {
                return Ok(Some(PointInteriorProof::StandardOpen {
                    set,
                    domain_equal: Box::new(equal),
                    point_member: Box::new(point_member),
                }));
            }
        }
        let Obj::SetFormer(SetFormer::SetBuilder(builder)) = domain else {
            return Ok(None);
        };
        let Some(base) =
            self.prove_point_interior(&builder.param_set, point, state, depth + 1, budget)?
        else {
            return Ok(None);
        };
        let member: Fact = InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: point.clone(),
            set: domain.clone(),
            line_file: None,
        }
        .into();
        let point_member = self.verify_fact(&member, state)?;
        if point_member.is_failed() {
            return Ok(None);
        }
        let mut guards = Vec::new();
        for fact in &builder.facts {
            let QuantifierFreeFact::AtomicFact(guard) = fact else {
                return Ok(None);
            };
            let operands: Vec<&Obj> = match guard {
                AtomicFact::LessFact(f) => vec![&f.left, &f.right],
                AtomicFact::GreaterFact(f) => vec![&f.left, &f.right],
                AtomicFact::LessEqualFact(f) => vec![&f.left, &f.right],
                AtomicFact::GreaterEqualFact(f) => vec![&f.left, &f.right],
                AtomicFact::NotEqualFact(f) => vec![&f.left, &f.right],
                AtomicFact::InFact(f)
                    if matches!(
                        &f.set,
                        Obj::StandardSet(
                            StandardSet::R
                                | StandardSet::RPos
                                | StandardSet::RNeg
                                | StandardSet::RStar
                        )
                    ) =>
                {
                    vec![&f.element]
                }
                _ => return Ok(None),
            };
            let mut operand_proofs = Vec::new();
            for operand in operands {
                if let Some(proof) = self.prove_continuous_expression(
                    operand,
                    builder.param_binding.id,
                    point,
                    state,
                    depth + 1,
                    budget,
                )? {
                    operand_proofs.push(InteriorOperandProof::Continuous(proof));
                } else if let Some(proof) = self.prove_derivative_expression(
                    operand,
                    builder.param_binding.id,
                    point,
                    state,
                    depth + 1,
                    budget,
                )? {
                    operand_proofs.push(InteriorOperandProof::Differentiable(proof));
                } else {
                    return Ok(None);
                }
            }
            let Ok(point_atomic) = self.inst_atomic_fact(
                guard,
                &HashMap::from([(builder.param_binding.id, point.clone())]),
            ) else {
                return Ok(None);
            };
            // A weak guard is stable on a neighbourhood only when it has
            // strict slack here. Endpoint equality never supplies interior.
            let point_fact: Fact = match point_atomic {
                AtomicFact::LessEqualFact(f) => LessFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: f.left,
                    right: f.right,
                    line_file: f.line_file,
                }
                .into(),
                AtomicFact::GreaterEqualFact(f) => GreaterFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: f.left,
                    right: f.right,
                    line_file: f.line_file,
                }
                .into(),
                fact => fact.into(),
            };
            let point_proof = self.verify_fact(&point_fact, state)?;
            if point_proof.is_failed() {
                return Ok(None);
            }
            guards.push(InteriorGuardProof {
                guard: guard.clone(),
                point_fact,
                point_proof: Box::new(point_proof),
                operands: operand_proofs,
            });
        }
        Ok(Some(PointInteriorProof::Guarded {
            base: Box::new(base),
            point_member: Box::new(point_member),
            guards,
        }))
    }
    fn prove_derivative_expression(
        &mut self,
        expression: &Obj,
        parameter: IdentifierId,
        point: &Obj,
        state: VerifyState,
        depth: usize,
        budget: &mut usize,
    ) -> RuntimeResult<Option<DerivativeExpressionProof>> {
        if depth >= 64 || *budget == 0 {
            return Ok(None);
        }
        *budget -= 1;
        let Ok(value) = self.inst_obj(expression, &HashMap::from([(parameter, point.clone())]))
        else {
            return Ok(None);
        };
        let member: Fact = InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: value.clone(),
            set: real(),
            line_file: None,
        }
        .into();
        let value_real = self.verify_fact(&member, state)?;
        if value_real.is_failed() {
            return Ok(None);
        }
        use DerivativeConstructorProof as C;
        let (derivative, constructor) = if !depends(expression, parameter) {
            (number("0"), C::Constant)
        } else if matches!(expression,Obj::Identifier(IdentifierObj::Plain{id,..}) if *id==parameter)
        {
            (number("1"), C::Variable)
        } else if let Some((kind, input)) = ElementaryRealFunction::from_expression(expression) {
            let Some(argument) = self.prove_derivative_expression(
                input,
                parameter,
                point,
                state,
                depth + 1,
                budget,
            )?
            else {
                return Ok(None);
            };
            let requirement = self.elementary_real_condition(kind, argument.value.clone(), true);
            let domain = self.verify_fact(&requirement, state)?;
            if domain.is_failed() {
                return Ok(None);
            }
            (
                kind.derivative(argument.value.clone(), argument.derivative.clone()),
                C::Elementary {
                    kind,
                    argument: Box::new(argument),
                    domain: Box::new(domain),
                },
            )
        } else {
            match expression {
                Obj::ArithmeticOperator(ArithmeticOperator::Neg(a)) => {
                    let Some(argument) = self.prove_derivative_expression(
                        &a.arg,
                        parameter,
                        point,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    (
                        Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg {
                            arg: Box::new(argument.derivative.clone()),
                        })),
                        C::Neg {
                            argument: Box::new(argument),
                        },
                    )
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Add(a)) => {
                    let Some(left) = self.prove_derivative_expression(
                        &a.left,
                        parameter,
                        point,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some(right) = self.prove_derivative_expression(
                        &a.right,
                        parameter,
                        point,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    (
                        add_objs(left.derivative.clone(), right.derivative.clone()),
                        C::Add {
                            left: Box::new(left),
                            right: Box::new(right),
                        },
                    )
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(a)) => {
                    let Some(left) = self.prove_derivative_expression(
                        &a.left,
                        parameter,
                        point,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some(right) = self.prove_derivative_expression(
                        &a.right,
                        parameter,
                        point,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    (
                        sub_objs(left.derivative.clone(), right.derivative.clone()),
                        C::Sub {
                            left: Box::new(left),
                            right: Box::new(right),
                        },
                    )
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(a)) => {
                    let Some(left) = self.prove_derivative_expression(
                        &a.left,
                        parameter,
                        point,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some(right) = self.prove_derivative_expression(
                        &a.right,
                        parameter,
                        point,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    (
                        add_objs(
                            mul_objs(left.derivative.clone(), right.value.clone()),
                            mul_objs(left.value.clone(), right.derivative.clone()),
                        ),
                        C::Mul {
                            left: Box::new(left),
                            right: Box::new(right),
                        },
                    )
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Div(a)) => {
                    let Some(left) = self.prove_derivative_expression(
                        &a.left,
                        parameter,
                        point,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some(right) = self.prove_derivative_expression(
                        &a.right,
                        parameter,
                        point,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    let nonzero: Fact = NotEqualFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        left: right.value.clone(),
                        right: number("0"),
                        line_file: None,
                    }
                    .into();
                    let denominator_nonzero = self.verify_fact(&nonzero, state)?;
                    if denominator_nonzero.is_failed() {
                        return Ok(None);
                    }
                    (
                        div_objs(
                            div_objs(
                                sub_objs(
                                    mul_objs(left.derivative.clone(), right.value.clone()),
                                    mul_objs(left.value.clone(), right.derivative.clone()),
                                ),
                                right.value.clone(),
                            ),
                            right.value.clone(),
                        ),
                        C::Div {
                            left: Box::new(left),
                            right: Box::new(right),
                            denominator_nonzero: Box::new(denominator_nonzero),
                        },
                    )
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(a)) => {
                    if depends(&a.exponent, parameter) {
                        return Ok(None);
                    }
                    let Some(base) = self.prove_derivative_expression(
                        &a.base,
                        parameter,
                        point,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    let natural: Fact = InFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        element: *a.exponent.clone(),
                        set: Obj::StandardSet(StandardSet::N),
                        line_file: None,
                    }
                    .into();
                    let exponent_natural = self.verify_fact(&natural, state)?;
                    if exponent_natural.is_failed() {
                        return Ok(None);
                    }
                    let index = sub_objs(
                        Obj::ArithmeticOperator(ArithmeticOperator::Max(Max {
                            left: a.exponent.clone(),
                            right: Box::new(number("1")),
                        })),
                        number("1"),
                    );
                    let factor = Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
                        base: Box::new(base.value.clone()),
                        exponent: Box::new(index),
                    }));
                    (
                        mul_objs(
                            mul_objs(*a.exponent.clone(), factor),
                            base.derivative.clone(),
                        ),
                        C::NaturalPower {
                            base: Box::new(base),
                            exponent_natural: Box::new(exponent_natural),
                        },
                    )
                }
                Obj::FnObj(call) if call.body.len() == 1 && call.body[0].len() == 1 => {
                    let function = function_head(&call.head);
                    if depends(&function, parameter) {
                        return Ok(None);
                    }
                    let Some(argument) = self.prove_derivative_expression(
                        &call.body[0][0],
                        parameter,
                        point,
                        state,
                        depth + 1,
                        budget,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some((slope, outer)) =
                        self.prove_derivative_leaf(&function, &argument.value, state)?
                    else {
                        return Ok(None);
                    };
                    (
                        multiply_derivative_terms(slope, argument.derivative.clone()),
                        C::Compose {
                            function,
                            argument: Box::new(argument),
                            outer,
                        },
                    )
                }
                _ => return Ok(None),
            }
        };
        let member: Fact = InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: derivative.clone(),
            set: real(),
            line_file: None,
        }
        .into();
        let derivative_real = self.verify_fact(&member, state)?;
        if derivative_real.is_failed() {
            return Ok(None);
        }
        Ok(Some(DerivativeExpressionProof {
            expression: expression.clone(),
            value,
            value_real: Box::new(value_real),
            derivative,
            derivative_real: Box::new(derivative_real),
            constructor,
        }))
    }
    fn prove_derivative_leaf(
        &mut self,
        function: &Obj,
        point: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<Option<(Obj, DerivativeLeafProof)>> {
        for known in self.known_derivative_candidates() {
            let query =
                self.derivative_candidate(function.clone(), point.clone(), known.value.clone());
            if let Some(proof) = self.lookup_known_atomic_premise(query) {
                return Ok(Some((known.value, DerivativeLeafProof::Candidate(proof))));
            }
        }
        let goal: Fact = FunctionDifferentiableAtFact {
            fact_id: self.global_ids.allocate_fact_id(),
            function: function.clone(),
            point: point.clone(),
            line_file: None,
        }
        .into();
        let differentiability = self.verify_fact(&goal, state)?;
        if differentiability.is_failed() {
            return Ok(None);
        }
        let value: Obj = DerivativeAt::new(function.clone(), point.clone()).into();
        let VerifyObjWellDefinedResult::Success(value_well_defined) =
            self.verify_obj_well_definedness(&value, state)?
        else {
            return Ok(None);
        };
        Ok(Some((
            value,
            DerivativeLeafProof::Selected {
                differentiability: Box::new(differentiability),
                value_well_defined: Box::new(value_well_defined),
            },
        )))
    }
}
