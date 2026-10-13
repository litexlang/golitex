use crate::ast::fact::{AtomicFact, EqualFact, Fact, InFact, LessEqualFact, LessFact};
use crate::ast::obj::{
    IntervalObj, Literal, Number, Obj, OneSideInfinityIntervalObj, ProductShape, SetFormer,
    StandardSet,
};
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::{
    InferInFactCartCoordinatesResult, InferInFactClosedRangeResult,
    InferInFactOneSideRealIntervalResult, InferInFactRangeResult, InferInFactRealIntervalResult,
    InferInFactResult,
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
    ) -> RuntimeResult<Vec<InferInFactResult>> {
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
        _verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Option<InferInFactResult>> {
        let Obj::ProductShape(ProductShape::Cart(cart)) = &in_fact.set else {
            return Ok(None);
        };
        let mut coordinates = Vec::new();
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
            {
                let stored = self.store_inferred_fact(&membership)?;
                coordinates.push(crate::store_fact_and_infer::InferCartCoordinateResult {
                    coordinate_index: index,
                    membership: stored,
                });
            }
        }
        // The zero-coordinate case has no consequences, but remains a valid
        // exact-domain membership. No shape, dimension or old index is added.
        Ok(Some(InferInFactResult::CartCoordinates(
            InferInFactCartCoordinatesResult { coordinates },
        )))
    }

    fn infer_in_fact_range(
        &mut self,
        in_fact: &InFact,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Option<InferInFactResult>> {
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
        Ok(Some(InferInFactResult::Range(InferInFactRangeResult {
            bounds: derived,
        })))
    }

    fn infer_in_fact_closed_range(
        &mut self,
        in_fact: &InFact,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Option<InferInFactResult>> {
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
        Ok(Some(InferInFactResult::ClosedRange(
            InferInFactClosedRangeResult { bounds: derived },
        )))
    }

    fn infer_integer_interval_bounds(
        &mut self,
        in_fact: &InFact,
        start: Obj,
        end: Obj,
        end_inclusive: bool,
        _verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<crate::store_fact_and_infer::InferIntegerIntervalBoundsResult> {
        let element = in_fact.element.clone();
        let lf = in_fact.line_file.clone();
        let mut derived = Vec::new();

        let in_z_id = self.global_ids.allocate_fact_id();
        derived.push(
            self.store_inferred_fact(&Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: in_z_id,
                element: element.clone(),
                set: Obj::StandardSet(StandardSet::Z),
                line_file: lf.clone(),
            })))?,
        );

        let lower_id = self.global_ids.allocate_fact_id();
        derived.push(
            self.store_inferred_fact(&Fact::AtomicFact(AtomicFact::LessEqualFact(
                LessEqualFact {
                    fact_id: lower_id,
                    left: start.clone(),
                    right: element.clone(),
                    line_file: lf.clone(),
                },
            )))?,
        );

        if end_inclusive {
            let upper_id = self.global_ids.allocate_fact_id();
            derived.push(self.store_inferred_fact(&Fact::AtomicFact(
                AtomicFact::LessEqualFact(LessEqualFact {
                    fact_id: upper_id,
                    left: element.clone(),
                    right: end.clone(),
                    line_file: lf.clone(),
                }),
            ))?);
        } else {
            let upper_id = self.global_ids.allocate_fact_id();
            derived.push(
                self.store_inferred_fact(&Fact::AtomicFact(AtomicFact::LessFact(LessFact {
                    fact_id: upper_id,
                    left: element.clone(),
                    right: end.clone(),
                    line_file: lf.clone(),
                })))?,
            );
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
            derived.push(
                self.store_inferred_fact(&Fact::AtomicFact(AtomicFact::InFact(InFact {
                    fact_id: positive_carrier_id,
                    element: element.clone(),
                    set: Obj::StandardSet(StandardSet::NPos),
                    line_file: lf.clone(),
                })))?,
            );
        }

        if let Some(singleton) =
            self.singleton_value_for_integer_interval(&start, &end, end_inclusive)
        {
            let eq_id = self.global_ids.allocate_fact_id();
            derived.push(
                self.store_inferred_fact(&Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                    fact_id: eq_id,
                    left: element,
                    right: singleton,
                    line_file: lf,
                })))?,
            );
        }

        let mut captured = derived.into_iter();
        let integer_membership = captured.next().ok_or_else(|| {
            crate::runtime::RuntimeError::InternalBug("missing integer interval membership".into())
        })?;
        let lower_bound = captured.next().ok_or_else(|| {
            crate::runtime::RuntimeError::InternalBug("missing integer interval lower bound".into())
        })?;
        let upper_bound = captured.next().ok_or_else(|| {
            crate::runtime::RuntimeError::InternalBug("missing integer interval upper bound".into())
        })?;
        let positive_membership = if positive_start {
            Some(captured.next().ok_or_else(|| {
                crate::runtime::RuntimeError::InternalBug(
                    "missing positive interval membership".into(),
                )
            })?)
        } else {
            None
        };
        let singleton_equality = captured.next();
        Ok(
            crate::store_fact_and_infer::InferIntegerIntervalBoundsResult {
                integer_membership,
                lower_bound,
                upper_bound,
                positive_membership,
                singleton_equality,
            },
        )
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
        _verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Option<InferInFactResult>> {
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
        derived.push(
            self.store_inferred_fact(&Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: in_r_id,
                element: element.clone(),
                set: Obj::StandardSet(StandardSet::R),
                line_file: lf.clone(),
            })))?,
        );

        if left_closed {
            let lower_id = self.global_ids.allocate_fact_id();
            derived.push(self.store_inferred_fact(&Fact::AtomicFact(
                AtomicFact::LessEqualFact(LessEqualFact {
                    fact_id: lower_id,
                    left: start,
                    right: element.clone(),
                    line_file: lf.clone(),
                }),
            ))?);
        } else {
            let lower_id = self.global_ids.allocate_fact_id();
            derived.push(
                self.store_inferred_fact(&Fact::AtomicFact(AtomicFact::LessFact(LessFact {
                    fact_id: lower_id,
                    left: start,
                    right: element.clone(),
                    line_file: lf.clone(),
                })))?,
            );
        }

        if right_closed {
            let upper_id = self.global_ids.allocate_fact_id();
            derived.push(self.store_inferred_fact(&Fact::AtomicFact(
                AtomicFact::LessEqualFact(LessEqualFact {
                    fact_id: upper_id,
                    left: element,
                    right: end,
                    line_file: lf,
                }),
            ))?);
        } else {
            let upper_id = self.global_ids.allocate_fact_id();
            derived.push(
                self.store_inferred_fact(&Fact::AtomicFact(AtomicFact::LessFact(LessFact {
                    fact_id: upper_id,
                    left: element,
                    right: end,
                    line_file: lf,
                })))?,
            );
        }

        let mut captured = derived.into_iter();
        Ok(Some(InferInFactResult::RealInterval(
            InferInFactRealIntervalResult {
                real_membership: captured.next().ok_or_else(|| {
                    crate::runtime::RuntimeError::InternalBug(
                        "missing recorded interval projection".into(),
                    )
                })?,
                lower_bound: captured.next().ok_or_else(|| {
                    crate::runtime::RuntimeError::InternalBug(
                        "missing recorded interval projection".into(),
                    )
                })?,
                upper_bound: captured.next().ok_or_else(|| {
                    crate::runtime::RuntimeError::InternalBug(
                        "missing recorded interval projection".into(),
                    )
                })?,
            },
        )))
    }

    fn infer_in_fact_one_side_real_interval(
        &mut self,
        in_fact: &InFact,
        _verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Option<InferInFactResult>> {
        let Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(interval)) = &in_fact.set else {
            return Ok(None);
        };
        let element = in_fact.element.clone();
        let lf = in_fact.line_file.clone();
        let mut derived = Vec::new();

        let in_r_id = self.global_ids.allocate_fact_id();
        derived.push(
            self.store_inferred_fact(&Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: in_r_id,
                element: element.clone(),
                set: Obj::StandardSet(StandardSet::R),
                line_file: lf.clone(),
            })))?,
        );

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
        derived.push(self.store_inferred_fact(&Fact::AtomicFact(bound))?);

        let mut captured = derived.into_iter();
        Ok(Some(InferInFactResult::OneSideRealInterval(
            InferInFactOneSideRealIntervalResult {
                real_membership: captured.next().ok_or_else(|| {
                    crate::runtime::RuntimeError::InternalBug(
                        "missing recorded interval projection".into(),
                    )
                })?,
                bound: captured.next().ok_or_else(|| {
                    crate::runtime::RuntimeError::InternalBug(
                        "missing recorded interval projection".into(),
                    )
                })?,
            },
        )))
    }
}
