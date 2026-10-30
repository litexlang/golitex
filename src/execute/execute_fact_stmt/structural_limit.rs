//! Bounded arithmetic limit checking over an already checked function body.
//! Example: a -> A and b -> B prove (k |-> a(k)+b(k)) -> A+B.
//! This engine is a truth-search strategy; selectors never invoke it from WD.
#[cfg(test)]
#[path = "../../../tests/unit/execute/pointwise_analysis/structural_limit.rs"]
mod structural_limit_tests;
use super::function_domain::{function_domains_alpha_equal, CheckedFunctionBodyProof};
use super::function_limit::RealFunctionLimitDomainProof;
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

#[derive(Clone)]
pub enum StructuralLimitApproach {
    Sequence,
    Function(LimitApproach),
}

pub enum StructuralLimitGeometryProof {
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
    Constant,
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
                parameters[0].id,
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
                right: target.clone(),
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
        parameter: IdentifierId,
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
        let (limit, constructor) = if !depends_on_limit_parameter(expression, parameter) {
            (expression.clone(), C::Constant)
        } else if is_limit_parameter(expression, parameter) {
            let StructuralLimitApproach::Function(approach) = approach else {
                return Ok(None);
            };
            let Some(point) = approach.point() else {
                return Ok(None);
            };
            (point.clone(), C::FiniteIdentity)
        } else {
            match expression {
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
                    if depends_on_limit_parameter(&a.exponent, parameter) {
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
                    if depends_on_limit_parameter(&function, parameter) {
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
                    let offset = if is_limit_parameter(input, parameter) {
                        None
                    } else if matches!(approach, StructuralLimitApproach::Sequence) {
                        let Obj::ArithmeticOperator(ArithmeticOperator::Add(add)) = input.as_ref()
                        else {
                            return Ok(None);
                        };
                        let offset = if is_limit_parameter(&add.left, parameter) {
                            &add.right
                        } else if is_limit_parameter(&add.right, parameter) {
                            &add.left
                        } else {
                            return Ok(None);
                        };
                        if depends_on_limit_parameter(offset, parameter) {
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
