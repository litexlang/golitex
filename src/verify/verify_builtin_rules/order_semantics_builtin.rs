use super::order_normalize::normalize_positive_order_atomic_fact;
use crate::prelude::*;
use crate::verify::verify_equality_by_builtin_rules::objs_equal_by_display_string;

fn obj_is_literal_one(obj: &Obj) -> bool {
    matches!(obj, Obj::Number(number) if number.normalized_value == "1")
}

fn obj_plus_one_base(obj: &Obj) -> Option<Obj> {
    let Obj::Add(add) = obj else {
        return None;
    };
    if obj_is_literal_one(add.right.as_ref()) {
        return Some(add.left.as_ref().clone());
    }
    if obj_is_literal_one(add.left.as_ref()) {
        return Some(add.right.as_ref().clone());
    }
    None
}

fn obj_minus_one_base(obj: &Obj) -> Option<Obj> {
    let Obj::Sub(sub) = obj else {
        return None;
    };
    if obj_is_literal_one(sub.right.as_ref()) {
        return Some(sub.left.as_ref().clone());
    }
    None
}

fn obj_plus_one(obj: &Obj) -> Obj {
    Add::new(obj.clone(), Number::new("1".to_string()).into()).into()
}

fn direct_positive_order_shape(fact: &AtomicFact) -> Option<(Obj, Obj, bool)> {
    if !matches!(
        fact,
        AtomicFact::LessFact(_)
            | AtomicFact::LessEqualFact(_)
            | AtomicFact::GreaterFact(_)
            | AtomicFact::GreaterEqualFact(_)
    ) {
        return None;
    }
    let normalized = normalize_positive_order_atomic_fact(fact)?;
    match normalized {
        AtomicFact::LessFact(f) => Some((f.left, f.right, true)),
        AtomicFact::LessEqualFact(f) => Some((f.left, f.right, false)),
        _ => None,
    }
}

fn weak_order_left_right(fact: &AtomicFact) -> Option<(Obj, Obj)> {
    match fact {
        AtomicFact::LessEqualFact(f) => Some((f.left.clone(), f.right.clone())),
        AtomicFact::GreaterEqualFact(f) => Some((f.right.clone(), f.left.clone())),
        _ => None,
    }
}

fn integer_discrete_split_subject_and_base(
    first: &AtomicFact,
    second: &AtomicFact,
) -> Option<(Obj, Obj)> {
    let (subject, base) = weak_order_left_right(first)?;
    let (successor, successor_subject) = weak_order_left_right(second)?;
    let successor_base = obj_plus_one_base(&successor)?;
    if objs_equal_by_display_string(&subject, &successor_subject)
        && objs_equal_by_display_string(&base, &successor_base)
    {
        return Some((subject, base));
    }
    None
}

fn integer_discrete_predecessor_split_subject_and_base(
    first: &AtomicFact,
    second: &AtomicFact,
) -> Option<(Obj, Obj)> {
    let (base, subject) = weak_order_left_right(first)?;
    let (predecessor_subject, predecessor) = weak_order_left_right(second)?;
    let predecessor_base = obj_minus_one_base(&predecessor)?;
    if objs_equal_by_display_string(&subject, &predecessor_subject)
        && objs_equal_by_display_string(&base, &predecessor_base)
    {
        return Some((subject, base));
    }
    None
}

impl Runtime {
    /// Direct order semantics that formerly required named source-level wrappers.
    /// They are limited to real binary order and integer discreteness, with every premise
    /// retained as a visible verification step.
    pub(crate) fn try_verify_order_semantics_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(result) = self.try_verify_order_transitivity_builtin_rule(atomic_fact)? {
            return Ok(Some(result));
        }
        if let Some(result) =
            self.try_verify_finite_set_extrema_order_builtin_rule(atomic_fact, verify_state)?
        {
            return Ok(Some(result));
        }
        self.try_verify_integer_successor_predecessor_builtin_rule(atomic_fact, verify_state)
    }

    // Combines two stored real-order facts through a shared middle term.
    // Example: `a <= b`, `b < c` => `a < c`.
    fn try_verify_order_transitivity_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some((target_left, target_right, target_is_strict)) =
            direct_positive_order_shape(atomic_fact)
        else {
            return Ok(None);
        };

        let mut known_orders = Vec::new();
        for environment in self.iter_environments_from_top() {
            for known_facts_map in environment.known_atomic_facts_with_2_args.values() {
                for known_fact in known_facts_map.values() {
                    if direct_positive_order_shape(known_fact).is_some() {
                        known_orders.push(known_fact.clone());
                    }
                }
            }
        }
        known_orders.sort_by_key(|fact| fact.to_string());
        known_orders.dedup_by(|left, right| left.to_string() == right.to_string());

        for first in known_orders.iter() {
            let Some((first_left, middle, first_is_strict)) = direct_positive_order_shape(first)
            else {
                continue;
            };
            if !objs_equal_by_display_string(&first_left, &target_left) {
                continue;
            }
            for second in known_orders.iter() {
                let Some((second_left, second_right, second_is_strict)) =
                    direct_positive_order_shape(second)
                else {
                    continue;
                };
                if !objs_equal_by_display_string(&middle, &second_left)
                    || !objs_equal_by_display_string(&second_right, &target_right)
                    || (target_is_strict && !first_is_strict && !second_is_strict)
                {
                    continue;
                }

                let line_file = atomic_fact.line_file();
                let type_verify_state = VerifyState::new(0, true);
                let type_steps = self.verify_objects_are_known_reals(
                    &[&target_left, &middle, &target_right],
                    &line_file,
                    &type_verify_state,
                )?;
                let type_steps = match type_steps {
                    Some(steps) => Some(steps),
                    None => self.verify_objects_are_known_integers(
                        &[&target_left, &middle, &target_right],
                        &line_file,
                        &type_verify_state,
                    )?,
                };
                let Some(mut steps) = type_steps else {
                    continue;
                };
                let first_result =
                    self.verify_non_equational_atomic_fact_with_known_atomic_facts(first)?;
                let second_result =
                    self.verify_non_equational_atomic_fact_with_known_atomic_facts(second)?;
                if !first_result.is_true() || !second_result.is_true() {
                    continue;
                }
                steps.push(first_result);
                steps.push(second_result);
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "order: transitivity through a shared ordered numeric middle term"
                            .to_string(),
                        steps,
                    )
                    .into(),
                ));
            }
        }
        Ok(None)
    }

    // A finite-set maximum bounds every member and a finite-set minimum is below every member.
    // Examples: `x $in S` => `x <= finite_set_max(S)` and
    // `x $in S` => `finite_set_min(S) <= x`.
    fn try_verify_finite_set_extrema_order_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(AtomicFact::LessEqualFact(fact)) =
            normalize_positive_order_atomic_fact(atomic_fact)
        else {
            return Ok(None);
        };
        if let Obj::FiniteSetMax(maximum) = &fact.right {
            let member_fact: AtomicFact = InFact::new(
                fact.left.clone(),
                maximum.set.as_ref().clone(),
                fact.line_file.clone(),
            )
            .into();
            let member_result = self
                .verify_non_equational_known_then_builtin_rules_only(&member_fact, verify_state)?;
            if member_result.is_true() {
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "finite_set_max: every member is at most the maximum".to_string(),
                        vec![member_result],
                    )
                    .into(),
                ));
            }
        }

        if let Obj::FiniteSetMin(minimum) = &fact.left {
            let member_fact: AtomicFact = InFact::new(
                fact.right.clone(),
                minimum.set.as_ref().clone(),
                fact.line_file.clone(),
            )
            .into();
            let member_result = self
                .verify_non_equational_known_then_builtin_rules_only(&member_fact, verify_state)?;
            if member_result.is_true() {
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "finite_set_min: the minimum is at most every member".to_string(),
                        vec![member_result],
                    )
                    .into(),
                ));
            }
        }

        if let Obj::FiniteSetMax(maximum) = &fact.left {
            if let Some(steps) = self.verify_finite_set_members_are_at_most(
                maximum.set.as_ref(),
                &fact.right,
                &fact.line_file,
                verify_state,
            )? {
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "finite_set_max: least upper bound of a concrete finite-set expression"
                            .to_string(),
                        steps,
                    )
                    .into(),
                ));
            }
        }

        if let Obj::FiniteSetMin(minimum) = &fact.right {
            if let Some(steps) = self.verify_finite_set_members_are_at_least(
                minimum.set.as_ref(),
                &fact.left,
                &fact.line_file,
                verify_state,
            )? {
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "finite_set_min: greatest lower bound of a concrete finite-set expression"
                            .to_string(),
                        steps,
                    )
                    .into(),
                ));
            }
        }

        Ok(None)
    }

    fn verify_finite_set_members_are_at_most(
        &mut self,
        set: &Obj,
        upper_bound: &Obj,
        line_file: &LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        match set {
            Obj::ListSet(list_set) => {
                let mut steps = Vec::new();
                for element in &list_set.list {
                    let fact: AtomicFact = LessEqualFact::new(
                        element.as_ref().clone(),
                        upper_bound.clone(),
                        line_file.clone(),
                    )
                    .into();
                    let result = self
                        .verify_non_equational_known_then_builtin_rules_only(&fact, verify_state)?;
                    if !result.is_true() {
                        return Ok(None);
                    }
                    steps.push(result);
                }
                Ok(Some(steps))
            }
            Obj::Union(union) => self.verify_two_finite_set_parts_are_at_most(
                union.left.as_ref(),
                union.right.as_ref(),
                upper_bound,
                line_file,
                verify_state,
            ),
            Obj::Intersect(intersect) => self.verify_finite_set_members_are_at_most(
                intersect.left.as_ref(),
                upper_bound,
                line_file,
                verify_state,
            ),
            Obj::SetMinus(set_minus) => self.verify_finite_set_members_are_at_most(
                set_minus.left.as_ref(),
                upper_bound,
                line_file,
                verify_state,
            ),
            Obj::SetDiff(set_diff) => self.verify_two_finite_set_parts_are_at_most(
                set_diff.left.as_ref(),
                set_diff.right.as_ref(),
                upper_bound,
                line_file,
                verify_state,
            ),
            _ => Ok(None),
        }
    }

    fn verify_two_finite_set_parts_are_at_most(
        &mut self,
        left: &Obj,
        right: &Obj,
        upper_bound: &Obj,
        line_file: &LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        let Some(mut steps) =
            self.verify_finite_set_members_are_at_most(left, upper_bound, line_file, verify_state)?
        else {
            return Ok(None);
        };
        let Some(right_steps) = self.verify_finite_set_members_are_at_most(
            right,
            upper_bound,
            line_file,
            verify_state,
        )?
        else {
            return Ok(None);
        };
        steps.extend(right_steps);
        Ok(Some(steps))
    }

    fn verify_finite_set_members_are_at_least(
        &mut self,
        set: &Obj,
        lower_bound: &Obj,
        line_file: &LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        match set {
            Obj::ListSet(list_set) => {
                let mut steps = Vec::new();
                for element in &list_set.list {
                    let fact: AtomicFact = LessEqualFact::new(
                        lower_bound.clone(),
                        element.as_ref().clone(),
                        line_file.clone(),
                    )
                    .into();
                    let result = self
                        .verify_non_equational_known_then_builtin_rules_only(&fact, verify_state)?;
                    if !result.is_true() {
                        return Ok(None);
                    }
                    steps.push(result);
                }
                Ok(Some(steps))
            }
            Obj::Union(union) => self.verify_two_finite_set_parts_are_at_least(
                union.left.as_ref(),
                union.right.as_ref(),
                lower_bound,
                line_file,
                verify_state,
            ),
            Obj::Intersect(intersect) => self.verify_finite_set_members_are_at_least(
                intersect.left.as_ref(),
                lower_bound,
                line_file,
                verify_state,
            ),
            Obj::SetMinus(set_minus) => self.verify_finite_set_members_are_at_least(
                set_minus.left.as_ref(),
                lower_bound,
                line_file,
                verify_state,
            ),
            Obj::SetDiff(set_diff) => self.verify_two_finite_set_parts_are_at_least(
                set_diff.left.as_ref(),
                set_diff.right.as_ref(),
                lower_bound,
                line_file,
                verify_state,
            ),
            _ => Ok(None),
        }
    }

    fn verify_two_finite_set_parts_are_at_least(
        &mut self,
        left: &Obj,
        right: &Obj,
        lower_bound: &Obj,
        line_file: &LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        let Some(mut steps) = self.verify_finite_set_members_are_at_least(
            left,
            lower_bound,
            line_file,
            verify_state,
        )?
        else {
            return Ok(None);
        };
        let Some(right_steps) = self.verify_finite_set_members_are_at_least(
            right,
            lower_bound,
            line_file,
            verify_state,
        )?
        else {
            return Ok(None);
        };
        steps.extend(right_steps);
        Ok(Some(steps))
    }

    // Integer discreteness at one successor/predecessor step.
    // Examples: `a < b` => `a + 1 <= b`, and `a < b` => `a <= b - 1`.
    fn try_verify_integer_successor_predecessor_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(AtomicFact::LessEqualFact(fact)) =
            normalize_positive_order_atomic_fact(atomic_fact)
        else {
            return Ok(None);
        };

        if let Some(predecessor) = obj_plus_one_base(&fact.left) {
            let Some(mut steps) = self.verify_objects_are_known_integers(
                &[&predecessor, &fact.right],
                &fact.line_file,
                verify_state,
            )?
            else {
                return Ok(None);
            };
            let strict: AtomicFact =
                LessFact::new(predecessor, fact.right.clone(), fact.line_file.clone()).into();
            let strict_result =
                self.verify_non_equational_known_then_builtin_rules_only(&strict, verify_state)?;
            if strict_result.is_true() {
                steps.push(strict_result);
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "integer successor: a < b gives a + 1 <= b".to_string(),
                        steps,
                    )
                    .into(),
                ));
            }
        }

        if let Some(successor) = obj_minus_one_base(&fact.right) {
            let Some(mut steps) = self.verify_objects_are_known_integers(
                &[&fact.left, &successor],
                &fact.line_file,
                verify_state,
            )?
            else {
                return Ok(None);
            };
            let strict: AtomicFact =
                LessFact::new(fact.left.clone(), successor, fact.line_file.clone()).into();
            let strict_result =
                self.verify_non_equational_known_then_builtin_rules_only(&strict, verify_state)?;
            if strict_result.is_true() {
                steps.push(strict_result);
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "integer predecessor: a < b gives a <= b - 1".to_string(),
                        steps,
                    )
                    .into(),
                ));
            }
        }

        Ok(None)
    }

    /// A singleton integer interval has only its endpoint.
    /// Example: `n <= x`, `x < n + 1` => `x = n`.
    pub(crate) fn try_verify_integer_singleton_interval_equality_builtin_rule(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (subject, base) in [(left, right), (right, left)] {
            let Some(mut steps) =
                self.verify_objects_are_known_integers(&[subject, base], &line_file, verify_state)?
            else {
                continue;
            };
            let lower: AtomicFact =
                LessEqualFact::new(base.clone(), subject.clone(), line_file.clone()).into();
            let upper: AtomicFact =
                LessFact::new(subject.clone(), obj_plus_one(base), line_file.clone()).into();
            let lower_result =
                self.verify_non_equational_known_then_builtin_rules_only(&lower, verify_state)?;
            if lower_result.is_unknown() {
                continue;
            }
            let upper_result =
                self.verify_non_equational_known_then_builtin_rules_only(&upper, verify_state)?;
            if upper_result.is_unknown() {
                continue;
            }
            steps.push(lower_result);
            steps.push(upper_result);
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    EqualFact::new(left.clone(), right.clone(), line_file).into(),
                    "integer singleton interval: n <= x < n + 1 gives x = n".to_string(),
                    steps,
                )
                .into(),
            ));
        }
        Ok(None)
    }

    /// Integer discreteness splits every pair at the next successor.
    /// Example: `forall x, n Z: x <= n or x >= n + 1`.
    pub(crate) fn try_verify_integer_discrete_split_or_builtin_rule(
        &mut self,
        or_fact: &OrFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if or_fact.facts.len() != 2 {
            return Ok(None);
        }
        let (AndChainAtomicFact::AtomicFact(first), AndChainAtomicFact::AtomicFact(second)) =
            (&or_fact.facts[0], &or_fact.facts[1])
        else {
            return Ok(None);
        };
        let (subject, base, reason) = if let Some((subject, base)) =
            integer_discrete_split_subject_and_base(first, second)
                .or_else(|| integer_discrete_split_subject_and_base(second, first))
        {
            (
                subject,
                base,
                "or: integer discrete split x <= n or x >= n + 1",
            )
        } else if let Some((subject, base)) =
            integer_discrete_predecessor_split_subject_and_base(first, second)
                .or_else(|| integer_discrete_predecessor_split_subject_and_base(second, first))
        {
            (
                subject,
                base,
                "or: integer discrete split x >= n or x <= n - 1",
            )
        } else {
            return Ok(None);
        };
        let Some(steps) = self.verify_objects_are_known_integers(
            &[&subject, &base],
            &or_fact.line_file,
            verify_state,
        )?
        else {
            return Ok(None);
        };
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                or_fact.clone().into(),
                reason.to_string(),
                steps,
            )
            .into(),
        ))
    }

    fn verify_objects_are_known_integers(
        &mut self,
        objs: &[&Obj],
        line_file: &LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        let mut steps = Vec::with_capacity(objs.len());
        for obj in objs {
            let in_z: AtomicFact =
                InFact::new((*obj).clone(), StandardSet::Z.into(), line_file.clone()).into();
            let result =
                self.verify_non_equational_known_then_builtin_rules_only(&in_z, verify_state)?;
            if result.is_unknown() {
                return Ok(None);
            }
            steps.push(result);
        }
        Ok(Some(steps))
    }
}
