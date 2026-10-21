//! Defining clauses for real bounds, real sequences and relative continuity.
use super::function_limit::{function_limit_exists, function_limit_forall};
use super::sequence_limit::{identifier, real};
use crate::ast::param::*;
use crate::prelude::*;
use crate::rational_expression::helper::{mul_objs, sub_objs};

impl Runtime {
    pub(crate) fn store_real_analysis_definition(
        &mut self,
        fact: &AtomicFact,
        state: VerifyState,
    ) -> RuntimeResult<Vec<crate::store_fact_and_infer::StoreInferredFactResult>> {
        let mut derived = Vec::new();
        for clause in self
            .real_analysis_defining_clauses(fact, state)?
            .unwrap_or_default()
        {
            derived.push(self.store_inferred_fact(&clause)?);
            // Sequence boundedness is defined on its real image. Expose the
            // corresponding bound witnesses in this fixed definition rule;
            // store_inferred_fact itself deliberately does not reopen inference.
            if matches!(fact, AtomicFact::SequenceAnalysisFact(_)) {
                if let Fact::AtomicFact(AtomicFact::RealSetBoundedFact(_)) = &clause {
                    let Fact::AtomicFact(atom) = &clause else {
                        unreachable!()
                    };
                    for witness in self
                        .real_analysis_defining_clauses(atom, state)?
                        .unwrap_or_default()
                    {
                        derived.push(self.store_inferred_fact(&witness)?);
                    }
                }
            }
        }
        if let AtomicFact::HasDerivativeAtFact(f) = fact {
            let existence = self.derivative_existence(f.function.clone(), f.point.clone());
            derived.push(self.store_inferred_fact(&existence)?);
            let differentiable: Fact = FunctionDifferentiableAtFact {
                fact_id: self.global_ids.allocate_fact_id(),
                function: f.function.clone(),
                point: f.point.clone(),
                line_file: None,
            }
            .into();
            derived.push(self.store_inferred_fact(&differentiable)?);
        }
        if let AtomicFact::FunctionDifferentiableAtFact(f) = fact {
            if let Some(domain) = self.checked_real_function_limit_domain(&f.function, state)? {
                let interior = self.derivative_interior_condition(domain.domain, f.point.clone());
                derived.push(self.store_inferred_fact(&interior)?);
            }
        }
        // Both bounds are a conjunction; exposing either part is definition
        // elimination, without invoking any convergence or completeness law.
        match fact {
            AtomicFact::RealSetBoundedFact(f) if f.boundedness == RealBoundedness::Both => {
                for boundedness in [RealBoundedness::Above, RealBoundedness::Below] {
                    let part = RealSetBoundedFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        set: f.set.clone(),
                        boundedness,
                        line_file: None,
                    };
                    derived.push(self.store_inferred_fact(&part.into())?);
                }
            }
            AtomicFact::SequenceAnalysisFact(f)
                if f.property == SequenceAnalysisProperty::Bounded =>
            {
                for property in [
                    SequenceAnalysisProperty::BoundedAbove,
                    SequenceAnalysisProperty::BoundedBelow,
                ] {
                    let part = SequenceAnalysisFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        sequence: f.sequence.clone(),
                        property,
                        line_file: None,
                    };
                    derived.push(self.store_inferred_fact(&part.into())?);
                }
            }
            _ => {}
        }
        Ok(derived)
    }

    pub(crate) fn real_analysis_defining_clauses(
        &mut self,
        fact: &AtomicFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<Vec<Fact>>> {
        let clauses = match fact {
            AtomicFact::HasDerivativeAtFact(_) | AtomicFact::FunctionDifferentiableAtFact(_) => {
                return self.derivative_defining_clauses(fact, state)
            }

            AtomicFact::RealSetBoundFact(f) => {
                let x = self.fresh_internal_param();
                let bound = match f.direction {
                    RealBoundDirection::Upper => analysis_le(self, identifier(&x), f.bound.clone()),
                    RealBoundDirection::Lower => analysis_le(self, f.bound.clone(), identifier(&x)),
                };
                vec![function_limit_forall(
                    self,
                    x,
                    f.set.clone(),
                    vec![],
                    vec![bound.into()],
                )]
            }
            AtomicFact::RealSetBoundedFact(f) => {
                let mut clauses = Vec::new();
                for direction in [RealBoundDirection::Lower, RealBoundDirection::Upper] {
                    if (f.boundedness == RealBoundedness::Above
                        && direction == RealBoundDirection::Lower)
                        || (f.boundedness == RealBoundedness::Below
                            && direction == RealBoundDirection::Upper)
                    {
                        continue;
                    }
                    let b = self.fresh_internal_param();
                    let bound = RealSetBoundFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        set: f.set.clone(),
                        bound: identifier(&b),
                        direction,
                        line_file: None,
                    }
                    .into();
                    clauses.push(function_limit_exists(self, b, real(), vec![bound]));
                }
                clauses
            }
            AtomicFact::SequenceAnalysisFact(f) => self.sequence_analysis_clauses(f),
            AtomicFact::RealAccumulationFact(f) => vec![self.function_limit_accumulation(
                f.domain.clone(),
                f.side.limit_approach(f.point.clone()),
            )],
            AtomicFact::FunctionContinuousAtFact(f) => {
                let Some(domain) = self.checked_real_function_limit_domain(&f.function, state)?
                else {
                    return Ok(None);
                };
                vec![self.continuity_epsilon(
                    f.function.clone(),
                    domain.domain,
                    f.point.clone(),
                    f.side,
                )]
            }
            AtomicFact::FunctionContinuousFact(f) => {
                let Some(domain) = self.checked_real_function_limit_domain(&f.function, state)?
                else {
                    return Ok(None);
                };
                match f.property {
                    FunctionContinuityProperty::Continuous => {
                        let x = self.fresh_internal_param();
                        let continuous = FunctionContinuousAtFact {
                            fact_id: self.global_ids.allocate_fact_id(),
                            function: f.function.clone(),
                            point: identifier(&x),
                            side: RealApproachSide::Both,
                            line_file: None,
                        };
                        vec![function_limit_forall(
                            self,
                            x,
                            domain.domain,
                            vec![],
                            vec![Fact::from(AtomicFact::from(continuous))],
                        )]
                    }
                    FunctionContinuityProperty::UniformContinuous => {
                        vec![self.uniform_continuity_epsilon(f.function.clone(), domain.domain)]
                    }
                }
            }
            AtomicFact::FunctionLipschitzFact(f) => {
                let Some(domain) = self.checked_real_function_limit_domain(&f.function, state)?
                else {
                    return Ok(None);
                };
                let p = self.fresh_internal_param();
                let pair = identifier(&p);
                let x = analysis_coordinate(pair.clone(), "1");
                let y = analysis_coordinate(pair, "2");
                let image_distance = analysis_distance(
                    analysis_apply(f.function.clone(), x.clone()),
                    analysis_apply(f.function.clone(), y.clone()),
                );
                let bound = analysis_le(
                    self,
                    image_distance,
                    mul_objs(f.constant.clone(), analysis_distance(x, y)),
                );
                vec![function_limit_forall(
                    self,
                    p,
                    analysis_cart(domain.domain.clone(), domain.domain),
                    vec![],
                    vec![bound.into()],
                )]
            }
            _ => return Ok(None),
        };
        Ok(Some(clauses))
    }

    pub(crate) fn sequence_analysis_clauses(&mut self, f: &SequenceAnalysisFact) -> Vec<Fact> {
        use SequenceAnalysisProperty::*;
        match f.property {
            Convergent => vec![self.sequence_limit_existence(f.sequence.clone())],
            BoundedAbove | BoundedBelow | Bounded => {
                let boundedness = match f.property {
                    BoundedAbove => RealBoundedness::Above,
                    BoundedBelow => RealBoundedness::Below,
                    _ => RealBoundedness::Both,
                };
                let range = Obj::FunctionSpace(FunctionSpace::FnRange(FnRange {
                    function: Box::new(f.sequence.clone()),
                }));
                vec![Fact::from(AtomicFact::from(RealSetBoundedFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    set: range,
                    boundedness,
                    line_file: None,
                }))]
            }
            Cauchy => {
                let epsilon = self.fresh_internal_param();
                let cutoff = self.fresh_internal_param();
                let inclusion = self.sequence_cauchy_control(
                    f.sequence.clone(),
                    identifier(&epsilon),
                    identifier(&cutoff),
                );
                let exists =
                    function_limit_exists(self, cutoff, analysis_nat_pos(), vec![inclusion]);
                vec![function_limit_forall(
                    self,
                    epsilon,
                    analysis_real_pos(),
                    vec![],
                    vec![exists],
                )]
            }
            Nondecreasing | Nonincreasing | StrictlyIncreasing | StrictlyDecreasing => {
                let m = self.fresh_internal_param();
                let n = self.fresh_internal_param();
                let strict = matches!(f.property, StrictlyIncreasing | StrictlyDecreasing);
                let premise = if strict {
                    analysis_lt(self, identifier(&m), identifier(&n))
                } else {
                    analysis_le(self, identifier(&m), identifier(&n))
                };
                let left = analysis_apply(f.sequence.clone(), identifier(&m));
                let right = analysis_apply(f.sequence.clone(), identifier(&n));
                let (left, right) = if matches!(f.property, Nonincreasing | StrictlyDecreasing) {
                    (right, left)
                } else {
                    (left, right)
                };
                let conclusion = if strict {
                    analysis_lt(self, left, right)
                } else {
                    analysis_le(self, left, right)
                };
                vec![Fact::ForallFact(ForallFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    typed_parameters: TypedParameterList {
                        groups: vec![TypedParameterGroup {
                            params: vec![m, n],
                            param_type: ParamType::Obj(analysis_nat_pos()),
                        }],
                    },
                    dom_facts: vec![premise.into()],
                    then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(conclusion)],
                    line_file: None,
                })]
            }
        }
    }

    pub(crate) fn sequence_cauchy_control(
        &mut self,
        sequence: Obj,
        epsilon: Obj,
        cutoff: Obj,
    ) -> AtomicFact {
        let n = self.fresh_internal_param();
        let condition = GreaterEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: identifier(&n),
            right: cutoff,
            line_file: None,
        }
        .into();
        let tail = analysis_builder(n, analysis_nat_pos(), vec![condition]);
        let p = self.fresh_internal_param();
        let pair = identifier(&p);
        let left = analysis_apply(sequence.clone(), analysis_coordinate(pair.clone(), "1"));
        let right = analysis_apply(sequence, analysis_coordinate(pair, "2"));
        let close = analysis_lt(self, analysis_distance(left, right), epsilon);
        let pairs = analysis_builder(
            p,
            analysis_cart(analysis_nat_pos(), analysis_nat_pos()),
            vec![close],
        );
        analysis_subset(self, analysis_cart(tail.clone(), tail), pairs)
    }

    pub(crate) fn continuity_epsilon(
        &mut self,
        function: Obj,
        domain: Obj,
        point: Obj,
        side: RealApproachSide,
    ) -> Fact {
        let epsilon = self.fresh_internal_param();
        let delta = self.fresh_internal_param();
        let control = self.continuity_control(
            function,
            domain,
            point,
            side,
            identifier(&epsilon),
            identifier(&delta),
        );
        let exists = function_limit_exists(self, delta, analysis_real_pos(), vec![control]);
        function_limit_forall(self, epsilon, analysis_real_pos(), vec![], vec![exists])
    }

    pub(crate) fn continuity_control(
        &mut self,
        function: Obj,
        domain: Obj,
        point: Obj,
        side: RealApproachSide,
        epsilon: Obj,
        delta: Obj,
    ) -> AtomicFact {
        let neighborhood = self.continuity_neighborhood(domain, point.clone(), side, delta);
        let y = self.fresh_internal_param();
        let value = analysis_apply(function.clone(), point);
        let close = analysis_lt(self, analysis_distance(identifier(&y), value), epsilon);
        let ball = analysis_builder(y, real(), vec![close]);
        analysis_subset(self, neighborhood, PreimageSet::new(function, ball).into())
    }

    pub(crate) fn continuity_neighborhood(
        &mut self,
        domain: Obj,
        point: Obj,
        side: RealApproachSide,
        radius: Obj,
    ) -> Obj {
        let x = self.fresh_internal_param();
        let argument = identifier(&x);
        let mut conditions = Vec::new();
        let displacement = match side {
            RealApproachSide::Both => analysis_distance(argument, point),
            RealApproachSide::Left => {
                conditions.push(analysis_le(self, argument.clone(), point.clone()));
                sub_objs(point, argument)
            }
            RealApproachSide::Right => {
                conditions.push(analysis_le(self, point.clone(), argument.clone()));
                sub_objs(argument, point)
            }
        };
        conditions.push(analysis_lt(self, displacement, radius));
        analysis_builder(x, domain, conditions)
    }

    pub(crate) fn uniform_continuity_epsilon(&mut self, function: Obj, domain: Obj) -> Fact {
        let epsilon = self.fresh_internal_param();
        let delta = self.fresh_internal_param();
        let control = self.uniform_continuity_control(
            function,
            domain,
            identifier(&epsilon),
            identifier(&delta),
        );
        let exists = function_limit_exists(self, delta, analysis_real_pos(), vec![control]);
        function_limit_forall(self, epsilon, analysis_real_pos(), vec![], vec![exists])
    }

    pub(crate) fn uniform_continuity_control(
        &mut self,
        function: Obj,
        domain: Obj,
        epsilon: Obj,
        delta: Obj,
    ) -> AtomicFact {
        let p = self.fresh_internal_param();
        let pair = identifier(&p);
        let close = analysis_lt(
            self,
            analysis_distance(
                analysis_coordinate(pair.clone(), "1"),
                analysis_coordinate(pair, "2"),
            ),
            delta,
        );
        let near = analysis_builder(
            p,
            analysis_cart(domain.clone(), domain.clone()),
            vec![close],
        );
        let q = self.fresh_internal_param();
        let pair = identifier(&q);
        let left = analysis_apply(function.clone(), analysis_coordinate(pair.clone(), "1"));
        let right = analysis_apply(function, analysis_coordinate(pair, "2"));
        let close = analysis_lt(self, analysis_distance(left, right), epsilon);
        let images = analysis_builder(q, analysis_cart(domain.clone(), domain), vec![close]);
        analysis_subset(self, near, images)
    }
}
pub(crate) fn analysis_apply(function: Obj, arg: Obj) -> Obj {
    super::function_domain::function_application(&function, vec![Box::new(arg)])
        .expect("object-valued unary head")
}
fn analysis_coordinate(pair: Obj, index: &str) -> Obj {
    analysis_apply(
        pair,
        Obj::Literal(Literal::Number(Number {
            normalized_value: index.into(),
        })),
    )
}
fn analysis_distance(left: Obj, right: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs {
        arg: Box::new(sub_objs(left, right)),
    }))
}
fn analysis_cart(left: Obj, right: Obj) -> Obj {
    Obj::ProductShape(ProductShape::Cart(Cart {
        args: vec![Box::new(left), Box::new(right)],
    }))
}
fn analysis_builder(name: crate::ast::names::BoundName, set: Obj, facts: Vec<AtomicFact>) -> Obj {
    Obj::SetFormer(SetFormer::SetBuilder(SetBuilder {
        param_binding: name,
        param_set: Box::new(set),
        facts: facts
            .into_iter()
            .map(QuantifierFreeFact::AtomicFact)
            .collect(),
    }))
}
fn analysis_le(rt: &mut Runtime, left: Obj, right: Obj) -> AtomicFact {
    LessEqualFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
}
fn analysis_lt(rt: &mut Runtime, left: Obj, right: Obj) -> AtomicFact {
    LessFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
}
fn analysis_subset(rt: &mut Runtime, left: Obj, right: Obj) -> AtomicFact {
    SubsetFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
}
fn analysis_nat_pos() -> Obj {
    Obj::StandardSet(StandardSet::NPos)
}
fn analysis_real_pos() -> Obj {
    Obj::StandardSet(StandardSet::RPos)
}
