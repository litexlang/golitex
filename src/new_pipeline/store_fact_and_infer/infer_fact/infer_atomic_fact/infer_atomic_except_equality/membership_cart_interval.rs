use crate::new_pipeline::ast::fact::{
    AtomicFact, EqualFact, Fact, InFact, IsTupleFact, LessEqualFact, LessFact,
};
use crate::new_pipeline::ast::obj::{
    IntervalObj, Literal, Number, Obj, OneSideInfinityIntervalObj, ProductShape, SetFormer,
    StandardSet, TupleDim,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::{
    InferAtomicExceptEqualityResult, InferInFactCartProjectionResult,
    InferInFactClosedRangeResult, InferInFactOneSideRealIntervalResult, InferInFactRangeResult,
    InferInFactRealIntervalResult, StoreFactAndInferResult,
};

impl Runtime {
    // When: `x $in cart` / `range` / `closed_range` / real interval / one-side interval.
    // Infers: tuple shape + coordinates; integer/real bounds (+ singleton eq when applicable).
    // Example: `u $in cart(R, Q)` ⇒ `$is_tuple(u)`, `tuple_dim(u)=2`, `u[1]$in R`, `u[2]$in Q`.
    pub(super) fn infer_in_fact_cart_interval_rules(
        &mut self,
        in_fact: &InFact,
    ) -> RuntimeResult<Vec<InferAtomicExceptEqualityResult>> {
        let mut rules = Vec::new();
        if let Some(r) = self.infer_in_fact_cart(in_fact)? {
            rules.push(r);
        }
        if let Some(r) = self.infer_in_fact_range(in_fact)? {
            rules.push(r);
        }
        if let Some(r) = self.infer_in_fact_closed_range(in_fact)? {
            rules.push(r);
        }
        if let Some(r) = self.infer_in_fact_real_interval(in_fact)? {
            rules.push(r);
        }
        if let Some(r) = self.infer_in_fact_one_side_real_interval(in_fact)? {
            rules.push(r);
        }
        Ok(rules)
    }
}

impl Runtime {
    fn infer_in_fact_cart(
        &mut self,
        in_fact: &InFact,
    ) -> RuntimeResult<Option<InferAtomicExceptEqualityResult>> {
        let Obj::ProductShape(ProductShape::Cart(cart)) = &in_fact.set else {
            return Ok(None);
        };
        if cart.args.len() < 2 {
            return Ok(None);
        }
        let lf = in_fact.line_file.clone();
        let n = cart.args.len();
        let mut derived: Vec<StoreFactAndInferResult> = Vec::new();

        let is_tuple_id = self.global_ids.allocate_fact_id();
        if let Some(ok) = self.try_store_inferred_fact_and_infer(&Fact::AtomicFact(
            AtomicFact::IsTupleFact(IsTupleFact {
                fact_id: is_tuple_id,
                set: in_fact.element.clone(),
                line_file: lf.clone(),
            }),
        ))? {
            derived.push(ok);
        }

        let dim_eq_id = self.global_ids.allocate_fact_id();
        if let Some(ok) = self.try_store_inferred_fact_and_infer(&Fact::AtomicFact(
            AtomicFact::EqualFact(EqualFact {
                fact_id: dim_eq_id,
                left: Obj::ProductShape(ProductShape::TupleDim(TupleDim {
                    arg: Box::new(in_fact.element.clone()),
                })),
                right: Obj::Literal(Literal::Number(Number {
                    normalized_value: n.to_string(),
                })),
                line_file: lf.clone(),
            }),
        ))? {
            derived.push(ok);
        }

        for (index, factor) in cart.args.iter().enumerate() {
            let projected = match &in_fact.element {
                Obj::ProductShape(ProductShape::Tuple(tuple)) if tuple.args.len() == n => {
                    tuple.args[index].as_ref().clone()
                }
                _ => Obj::ProductShape(ProductShape::ObjAtIndex(
                    crate::new_pipeline::ast::obj::ObjAtIndex {
                        obj: Box::new(in_fact.element.clone()),
                        index: Box::new(Obj::Literal(Literal::Number(Number {
                            normalized_value: (index + 1).to_string(),
                        }))),
                    },
                )),
            };
            let in_id = self.global_ids.allocate_fact_id();
            if let Some(ok) = self.try_store_inferred_fact_and_infer(&Fact::AtomicFact(
                AtomicFact::InFact(InFact {
                    fact_id: in_id,
                    element: projected,
                    set: factor.as_ref().clone(),
                    line_file: lf.clone(),
                }),
            ))? {
                derived.push(ok);
            }
        }

        if derived.is_empty() {
            return Ok(None);
        }
        Ok(Some(
            InferAtomicExceptEqualityResult::InFactCartProjection(InferInFactCartProjectionResult {
                derived,
            }),
        ))
    }

    fn infer_in_fact_range(
        &mut self,
        in_fact: &InFact,
    ) -> RuntimeResult<Option<InferAtomicExceptEqualityResult>> {
        let Obj::SetFormer(SetFormer::Range(r)) = &in_fact.set else {
            return Ok(None);
        };
        let derived = self.infer_integer_interval_bounds(
            in_fact,
            r.start.as_ref().clone(),
            r.end.as_ref().clone(),
            false,
        )?;
        Ok(Some(InferAtomicExceptEqualityResult::InFactRange(
            InferInFactRangeResult { derived },
        )))
    }

    fn infer_in_fact_closed_range(
        &mut self,
        in_fact: &InFact,
    ) -> RuntimeResult<Option<InferAtomicExceptEqualityResult>> {
        let Obj::SetFormer(SetFormer::ClosedRange(c)) = &in_fact.set else {
            return Ok(None);
        };
        let derived = self.infer_integer_interval_bounds(
            in_fact,
            c.start.as_ref().clone(),
            c.end.as_ref().clone(),
            true,
        )?;
        Ok(Some(
            InferAtomicExceptEqualityResult::InFactClosedRange(InferInFactClosedRangeResult {
                derived,
            }),
        ))
    }

    fn infer_integer_interval_bounds(
        &mut self,
        in_fact: &InFact,
        start: Obj,
        end: Obj,
        end_inclusive: bool,
    ) -> RuntimeResult<Vec<StoreFactAndInferResult>> {
        let element = in_fact.element.clone();
        let lf = in_fact.line_file.clone();
        let mut derived = Vec::new();

        let in_z_id = self.global_ids.allocate_fact_id();
        derived.push(self.store_inferred_fact_and_infer(&Fact::AtomicFact(AtomicFact::InFact(
            InFact {
                fact_id: in_z_id,
                element: element.clone(),
                set: Obj::StandardSet(StandardSet::Z),
                line_file: lf.clone(),
            },
        )))?);

        let lower_id = self.global_ids.allocate_fact_id();
        derived.push(self.store_inferred_fact_and_infer(&Fact::AtomicFact(
            AtomicFact::LessEqualFact(LessEqualFact {
                fact_id: lower_id,
                left: start.clone(),
                right: element.clone(),
                line_file: lf.clone(),
            }),
        ))?);

        if end_inclusive {
            let upper_id = self.global_ids.allocate_fact_id();
            derived.push(self.store_inferred_fact_and_infer(&Fact::AtomicFact(
                AtomicFact::LessEqualFact(LessEqualFact {
                    fact_id: upper_id,
                    left: element.clone(),
                    right: end.clone(),
                    line_file: lf.clone(),
                }),
            ))?);
        } else {
            let upper_id = self.global_ids.allocate_fact_id();
            derived.push(self.store_inferred_fact_and_infer(&Fact::AtomicFact(
                AtomicFact::LessFact(LessFact {
                    fact_id: upper_id,
                    left: element.clone(),
                    right: end.clone(),
                    line_file: lf.clone(),
                }),
            ))?);
        }

        if let Some(singleton) =
            self.singleton_value_for_integer_interval(&start, &end, end_inclusive)
        {
            let eq_id = self.global_ids.allocate_fact_id();
            derived.push(self.store_inferred_fact_and_infer(&Fact::AtomicFact(
                AtomicFact::EqualFact(EqualFact {
                    fact_id: eq_id,
                    left: element,
                    right: singleton,
                    line_file: lf,
                }),
            ))?);
        }

        Ok(derived)
    }

    fn singleton_value_for_integer_interval(
        &self,
        start: &Obj,
        end: &Obj,
        end_inclusive: bool,
    ) -> Option<Obj> {
        let start_n = self.resolve_obj_to_normalized_number(start)?;
        let end_n = self.resolve_obj_to_normalized_number(end)?;
        let start_i = start_n.parse::<i128>().ok()?;
        let end_i = end_n.parse::<i128>().ok()?;
        if end_inclusive {
            if start_i == end_i {
                return Some(Obj::Literal(Literal::Number(Number {
                    normalized_value: start_i.to_string(),
                })));
            }
        } else if start_i.checked_add(1) == Some(end_i) {
            return Some(Obj::Literal(Literal::Number(Number {
                normalized_value: start_i.to_string(),
            })));
        }
        None
    }

    fn infer_in_fact_real_interval(
        &mut self,
        in_fact: &InFact,
    ) -> RuntimeResult<Option<InferAtomicExceptEqualityResult>> {
        let Obj::SetFormer(SetFormer::IntervalObj(interval)) = &in_fact.set else {
            return Ok(None);
        };
        let element = in_fact.element.clone();
        let lf = in_fact.line_file.clone();
        let (start, end, left_closed, right_closed) = match interval {
            IntervalObj::LeftOpenRightOpen(s) => {
                (s.start.as_ref().clone(), s.end.as_ref().clone(), false, false)
            }
            IntervalObj::LeftOpenRightClosed(s) => {
                (s.start.as_ref().clone(), s.end.as_ref().clone(), false, true)
            }
            IntervalObj::LeftClosedRightOpen(s) => {
                (s.start.as_ref().clone(), s.end.as_ref().clone(), true, false)
            }
            IntervalObj::LeftClosedRightClosed(s) => {
                (s.start.as_ref().clone(), s.end.as_ref().clone(), true, true)
            }
        };
        let mut derived = Vec::new();

        let in_r_id = self.global_ids.allocate_fact_id();
        derived.push(self.store_inferred_fact_and_infer(&Fact::AtomicFact(AtomicFact::InFact(
            InFact {
                fact_id: in_r_id,
                element: element.clone(),
                set: Obj::StandardSet(StandardSet::R),
                line_file: lf.clone(),
            },
        )))?);

        if left_closed {
            let lower_id = self.global_ids.allocate_fact_id();
            derived.push(self.store_inferred_fact_and_infer(&Fact::AtomicFact(
                AtomicFact::LessEqualFact(LessEqualFact {
                    fact_id: lower_id,
                    left: start,
                    right: element.clone(),
                    line_file: lf.clone(),
                }),
            ))?);
        } else {
            let lower_id = self.global_ids.allocate_fact_id();
            derived.push(self.store_inferred_fact_and_infer(&Fact::AtomicFact(
                AtomicFact::LessFact(LessFact {
                    fact_id: lower_id,
                    left: start,
                    right: element.clone(),
                    line_file: lf.clone(),
                }),
            ))?);
        }

        if right_closed {
            let upper_id = self.global_ids.allocate_fact_id();
            derived.push(self.store_inferred_fact_and_infer(&Fact::AtomicFact(
                AtomicFact::LessEqualFact(LessEqualFact {
                    fact_id: upper_id,
                    left: element,
                    right: end,
                    line_file: lf,
                }),
            ))?);
        } else {
            let upper_id = self.global_ids.allocate_fact_id();
            derived.push(self.store_inferred_fact_and_infer(&Fact::AtomicFact(
                AtomicFact::LessFact(LessFact {
                    fact_id: upper_id,
                    left: element,
                    right: end,
                    line_file: lf,
                }),
            ))?);
        }

        Ok(Some(
            InferAtomicExceptEqualityResult::InFactRealInterval(InferInFactRealIntervalResult {
                derived,
            }),
        ))
    }

    fn infer_in_fact_one_side_real_interval(
        &mut self,
        in_fact: &InFact,
    ) -> RuntimeResult<Option<InferAtomicExceptEqualityResult>> {
        let Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(interval)) = &in_fact.set else {
            return Ok(None);
        };
        let element = in_fact.element.clone();
        let lf = in_fact.line_file.clone();
        let mut derived = Vec::new();

        let in_r_id = self.global_ids.allocate_fact_id();
        derived.push(self.store_inferred_fact_and_infer(&Fact::AtomicFact(AtomicFact::InFact(
            InFact {
                fact_id: in_r_id,
                element: element.clone(),
                set: Obj::StandardSet(StandardSet::R),
                line_file: lf.clone(),
            },
        )))?);

        // Match display/legacy: Left* = ray (a, +∞) / [a, +∞); Right* = (−∞, a) / (−∞, a].
        let bound_id = self.global_ids.allocate_fact_id();
        let bound = match interval {
            OneSideInfinityIntervalObj::LeftOpen(s) => AtomicFact::LessFact(LessFact {
                fact_id: bound_id,
                left: s.start.as_ref().clone(),
                right: element,
                line_file: lf,
            }),
            OneSideInfinityIntervalObj::LeftClosed(s) => AtomicFact::LessEqualFact(LessEqualFact {
                fact_id: bound_id,
                left: s.start.as_ref().clone(),
                right: element,
                line_file: lf,
            }),
            OneSideInfinityIntervalObj::RightOpen(s) => AtomicFact::LessFact(LessFact {
                fact_id: bound_id,
                left: element,
                right: s.start.as_ref().clone(),
                line_file: lf,
            }),
            OneSideInfinityIntervalObj::RightClosed(s) => AtomicFact::LessEqualFact(LessEqualFact {
                fact_id: bound_id,
                left: element,
                right: s.start.as_ref().clone(),
                line_file: lf,
            }),
        };
        derived.push(self.store_inferred_fact_and_infer(&Fact::AtomicFact(bound))?);

        Ok(Some(
            InferAtomicExceptEqualityResult::InFactOneSideRealInterval(
                InferInFactOneSideRealIntervalResult { derived },
            ),
        ))
    }
}
