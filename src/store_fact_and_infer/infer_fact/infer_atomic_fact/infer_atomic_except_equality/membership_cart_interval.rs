use crate::ast::fact::{AtomicFact, EqualFact, Fact, InFact, LessEqualFact, LessFact};
use crate::ast::obj::{
    IntervalObj, Literal, Number, Obj, OneSideInfinityIntervalObj, ProductShape, SetFormer,
    StandardSet,
};
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::{
    InferAtomicExceptEqualityResult, InferInFactCartCoordinatesResult,
    InferInFactClosedRangeResult, InferInFactOneSideRealIntervalResult, InferInFactRangeResult,
    InferInFactRealIntervalResult, StoreFactAndInferResult,
};

impl Runtime {
    // When: `x $in cart` / `range` / `closed_range` / real interval / one-side interval.
    // Infers: ordinary coordinate applications; integer/real interval bounds.
    // Example: `u $in cart(R, Q)` ⇒ `u(1)$in R`, `u(2)$in Q`.
    // The stored member already certifies the complete domain I_n.
    pub(super) fn infer_in_fact_cart_interval_rules(
        &mut self,
        in_fact: &InFact,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Vec<InferAtomicExceptEqualityResult>> {
        let mut rules = Vec::new();
        if let Some(r) = self.infer_in_fact_cart(in_fact, verify_state)? {
            rules.push(r);
        }
        if let Some(r) = self.infer_in_fact_range(in_fact, verify_state)? {
            rules.push(r);
        }
        if let Some(r) = self.infer_in_fact_closed_range(in_fact, verify_state)? {
            rules.push(r);
        }
        if let Some(r) = self.infer_in_fact_real_interval(in_fact, verify_state)? {
            rules.push(r);
        }
        if let Some(r) = self.infer_in_fact_one_side_real_interval(in_fact, verify_state)? {
            rules.push(r);
        }
        Ok(rules)
    }
}

impl Runtime {
    fn infer_in_fact_cart(
        &mut self,
        in_fact: &InFact,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Option<InferAtomicExceptEqualityResult>> {
        let Obj::ProductShape(ProductShape::Cart(cart)) = &in_fact.set else {
            return Ok(None);
        };
        let mut derived = Vec::new();
        for (index, factor) in cart.args.iter().enumerate() {
            let Ok(coordinate) =
                crate::execute::execute_fact_stmt::finite_function::finite_function_coordinate(
                    &in_fact.element,
                    index,
                )
            else {
                return Ok(None);
            };
            let membership = Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: coordinate,
                set: factor.as_ref().clone(),
                line_file: in_fact.line_file.clone(),
            }));
            if let Some(stored) =
                self.try_store_inferred_fact_and_infer(&membership, verify_state)?
            {
                derived.push(stored);
            }
        }
        // The zero-coordinate case has no consequences, but remains a valid
        // exact-domain membership. No shape, dimension or old index is added.
        Ok(Some(
            InferAtomicExceptEqualityResult::InFactCartCoordinates(
                InferInFactCartCoordinatesResult { derived },
            ),
        ))
    }

    fn infer_in_fact_range(
        &mut self,
        in_fact: &InFact,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Option<InferAtomicExceptEqualityResult>> {
        let Obj::SetFormer(SetFormer::Range(r)) = &in_fact.set else {
            return Ok(None);
        };
        let derived = self.infer_integer_interval_bounds(
            in_fact,
            r.start.as_ref().clone(),
            r.end.as_ref().clone(),
            false,
            verify_state,
        )?;
        Ok(Some(InferAtomicExceptEqualityResult::InFactRange(
            InferInFactRangeResult { derived },
        )))
    }

    fn infer_in_fact_closed_range(
        &mut self,
        in_fact: &InFact,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Option<InferAtomicExceptEqualityResult>> {
        let Obj::SetFormer(SetFormer::ClosedRange(c)) = &in_fact.set else {
            return Ok(None);
        };
        let derived = self.infer_integer_interval_bounds(
            in_fact,
            c.start.as_ref().clone(),
            c.end.as_ref().clone(),
            true,
            verify_state,
        )?;
        Ok(Some(InferAtomicExceptEqualityResult::InFactClosedRange(
            InferInFactClosedRangeResult { derived },
        )))
    }

    fn infer_integer_interval_bounds(
        &mut self,
        in_fact: &InFact,
        start: Obj,
        end: Obj,
        end_inclusive: bool,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Vec<StoreFactAndInferResult>> {
        let element = in_fact.element.clone();
        let lf = in_fact.line_file.clone();
        let mut derived = Vec::new();

        let in_z_id = self.global_ids.allocate_fact_id();
        derived.push(self.store_inferred_fact_and_infer(
            &Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: in_z_id,
                element: element.clone(),
                set: Obj::StandardSet(StandardSet::Z),
                line_file: lf.clone(),
            })),
            verify_state,
        )?);

        let lower_id = self.global_ids.allocate_fact_id();
        derived.push(self.store_inferred_fact_and_infer(
            &Fact::AtomicFact(AtomicFact::LessEqualFact(LessEqualFact {
                fact_id: lower_id,
                left: start.clone(),
                right: element.clone(),
                line_file: lf.clone(),
            })),
            verify_state,
        )?);

        if end_inclusive {
            let upper_id = self.global_ids.allocate_fact_id();
            derived.push(self.store_inferred_fact_and_infer(
                &Fact::AtomicFact(AtomicFact::LessEqualFact(LessEqualFact {
                    fact_id: upper_id,
                    left: element.clone(),
                    right: end.clone(),
                    line_file: lf.clone(),
                })),
                verify_state,
            )?);
        } else {
            let upper_id = self.global_ids.allocate_fact_id();
            derived.push(self.store_inferred_fact_and_infer(
                &Fact::AtomicFact(AtomicFact::LessFact(LessFact {
                    fact_id: upper_id,
                    left: element.clone(),
                    right: end.clone(),
                    line_file: lf.clone(),
                })),
                verify_state,
            )?);
        }

        // A positive integer literal lower bound makes this integer interval
        // a subset of N+. Inspect the source literal only: this inference must
        // not silently borrow an alias equality without retaining its citation.
        let positive_start = matches!(&start,
            Obj::Literal(Literal::Number(number))
                if number.normalized_value.parse::<i128>().ok().is_some_and(|value| value > 0)
        );
        if positive_start {
            let positive_carrier_id = self.global_ids.allocate_fact_id();
            derived.push(self.store_inferred_fact_and_infer(
                &Fact::AtomicFact(AtomicFact::InFact(InFact {
                    fact_id: positive_carrier_id,
                    element: element.clone(),
                    set: Obj::StandardSet(StandardSet::NPos),
                    line_file: lf.clone(),
                })),
                verify_state,
            )?);
        }

        if let Some(singleton) =
            self.singleton_value_for_integer_interval(&start, &end, end_inclusive)
        {
            let eq_id = self.global_ids.allocate_fact_id();
            derived.push(self.store_inferred_fact_and_infer(
                &Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                    fact_id: eq_id,
                    left: element,
                    right: singleton,
                    line_file: lf,
                })),
                verify_state,
            )?);
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
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Option<InferAtomicExceptEqualityResult>> {
        let Obj::SetFormer(SetFormer::IntervalObj(interval)) = &in_fact.set else {
            return Ok(None);
        };
        let element = in_fact.element.clone();
        let lf = in_fact.line_file.clone();
        let (start, end, left_closed, right_closed) = match interval {
            IntervalObj::LeftOpenRightOpen(s) => (
                s.start.as_ref().clone(),
                s.end.as_ref().clone(),
                false,
                false,
            ),
            IntervalObj::LeftOpenRightClosed(s) => (
                s.start.as_ref().clone(),
                s.end.as_ref().clone(),
                false,
                true,
            ),
            IntervalObj::LeftClosedRightOpen(s) => (
                s.start.as_ref().clone(),
                s.end.as_ref().clone(),
                true,
                false,
            ),
            IntervalObj::LeftClosedRightClosed(s) => {
                (s.start.as_ref().clone(), s.end.as_ref().clone(), true, true)
            }
        };
        let mut derived = Vec::new();

        let in_r_id = self.global_ids.allocate_fact_id();
        derived.push(self.store_inferred_fact_and_infer(
            &Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: in_r_id,
                element: element.clone(),
                set: Obj::StandardSet(StandardSet::R),
                line_file: lf.clone(),
            })),
            verify_state,
        )?);

        if left_closed {
            let lower_id = self.global_ids.allocate_fact_id();
            derived.push(self.store_inferred_fact_and_infer(
                &Fact::AtomicFact(AtomicFact::LessEqualFact(LessEqualFact {
                    fact_id: lower_id,
                    left: start,
                    right: element.clone(),
                    line_file: lf.clone(),
                })),
                verify_state,
            )?);
        } else {
            let lower_id = self.global_ids.allocate_fact_id();
            derived.push(self.store_inferred_fact_and_infer(
                &Fact::AtomicFact(AtomicFact::LessFact(LessFact {
                    fact_id: lower_id,
                    left: start,
                    right: element.clone(),
                    line_file: lf.clone(),
                })),
                verify_state,
            )?);
        }

        if right_closed {
            let upper_id = self.global_ids.allocate_fact_id();
            derived.push(self.store_inferred_fact_and_infer(
                &Fact::AtomicFact(AtomicFact::LessEqualFact(LessEqualFact {
                    fact_id: upper_id,
                    left: element,
                    right: end,
                    line_file: lf,
                })),
                verify_state,
            )?);
        } else {
            let upper_id = self.global_ids.allocate_fact_id();
            derived.push(self.store_inferred_fact_and_infer(
                &Fact::AtomicFact(AtomicFact::LessFact(LessFact {
                    fact_id: upper_id,
                    left: element,
                    right: end,
                    line_file: lf,
                })),
                verify_state,
            )?);
        }

        Ok(Some(InferAtomicExceptEqualityResult::InFactRealInterval(
            InferInFactRealIntervalResult { derived },
        )))
    }

    fn infer_in_fact_one_side_real_interval(
        &mut self,
        in_fact: &InFact,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Option<InferAtomicExceptEqualityResult>> {
        let Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(interval)) = &in_fact.set else {
            return Ok(None);
        };
        let element = in_fact.element.clone();
        let lf = in_fact.line_file.clone();
        let mut derived = Vec::new();

        let in_r_id = self.global_ids.allocate_fact_id();
        derived.push(self.store_inferred_fact_and_infer(
            &Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: in_r_id,
                element: element.clone(),
                set: Obj::StandardSet(StandardSet::R),
                line_file: lf.clone(),
            })),
            verify_state,
        )?);

        // Lower* = ray (a, +∞) / [a, +∞); Upper* = (−∞, a) / (−∞, a].
        let bound_id = self.global_ids.allocate_fact_id();
        let bound = match interval {
            OneSideInfinityIntervalObj::LowerOpen(s) => AtomicFact::LessFact(LessFact {
                fact_id: bound_id,
                left: s.start.as_ref().clone(),
                right: element,
                line_file: lf,
            }),
            OneSideInfinityIntervalObj::LowerClosed(s) => {
                AtomicFact::LessEqualFact(LessEqualFact {
                    fact_id: bound_id,
                    left: s.start.as_ref().clone(),
                    right: element,
                    line_file: lf,
                })
            }
            OneSideInfinityIntervalObj::UpperOpen(s) => AtomicFact::LessFact(LessFact {
                fact_id: bound_id,
                left: element,
                right: s.start.as_ref().clone(),
                line_file: lf,
            }),
            OneSideInfinityIntervalObj::UpperClosed(s) => {
                AtomicFact::LessEqualFact(LessEqualFact {
                    fact_id: bound_id,
                    left: element,
                    right: s.start.as_ref().clone(),
                    line_file: lf,
                })
            }
        };
        derived.push(self.store_inferred_fact_and_infer(&Fact::AtomicFact(bound), verify_state)?);

        Ok(Some(
            InferAtomicExceptEqualityResult::InFactOneSideRealInterval(
                InferInFactOneSideRealIntervalResult { derived },
            ),
        ))
    }
}
