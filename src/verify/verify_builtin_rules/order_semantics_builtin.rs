use super::order_normalize::normalize_positive_order_atomic_fact;
use crate::prelude::*;
use crate::verify::verify_equality_by_builtin_rules::objs_equal_by_display_string;

fn obj_is_literal_one(obj: &Obj) -> bool {
    matches!(obj, Obj::Number(number) if number.normalized_value == "1")
}

fn object_is_explicit_member_of_finite_set_expression(element: &Obj, set: &Obj) -> bool {
    match set {
        Obj::ListSet(list) => list.list.iter().any(|candidate| {
            objs_equal_with_nested_binder_alpha_equivalence(element, candidate.as_ref())
        }),
        Obj::Union(union) => {
            object_is_explicit_member_of_finite_set_expression(element, union.left.as_ref())
                || object_is_explicit_member_of_finite_set_expression(element, union.right.as_ref())
        }
        _ => false,
    }
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
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(result) =
            self.try_verify_positive_even_integer_greater_than_one(atomic_fact, builtin_state)?
        {
            return Ok(Some(result));
        }
        if let Some(result) =
            self.try_verify_order_transitivity_builtin_rule(atomic_fact, builtin_state)?
        {
            return Ok(Some(result));
        }
        if let Some(result) = self.try_verify_finite_set_extrema_order_builtin_rule(atomic_fact)? {
            return Ok(Some(result));
        }
        self.try_verify_integer_successor_predecessor_builtin_rule(atomic_fact, builtin_state)
    }

    // A positive even integer is at least two and therefore greater than one.
    // Example: `i $in N_pos`, `i % 2 = 0` => `i > 1`, so `i - 1 $in N_pos`.
    fn try_verify_positive_even_integer_greater_than_one(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some((left, integer, true)) = direct_positive_order_shape(atomic_fact) else {
            return Ok(None);
        };
        if !obj_is_literal_one(&left) {
            return Ok(None);
        }

        let line_file = atomic_fact.line_file();
        let in_n_pos: AtomicFact =
            InFact::new(integer.clone(), StandardSet::NPos.into(), line_file.clone()).into();
        let membership_result = self.verify_builtin_rule_premise(&in_n_pos, builtin_state)?;
        if !membership_result.is_true() {
            return Ok(None);
        }

        let two: Obj = Number::new("2".to_string()).into();
        let zero: Obj = Number::new("0".to_string()).into();
        let remainder: Obj = Mod::new(integer, two).into();
        let even_fact: AtomicFact = EqualFact::new(remainder, zero, line_file).into();
        let even_result = self.verify_builtin_rule_premise(&even_fact, builtin_state)?;
        if !even_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "positive even integer is greater than one".to_string(),
                vec![membership_result, even_result],
            )
            .into(),
        ))
    }

    // Combines two stored real-order facts through a shared middle term.
    // Example: `a <= b`, `b < c` => `a < c`.
    fn try_verify_order_transitivity_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
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
                let type_steps = self.verify_objects_are_known_reals_in_builtin(
                    &[&target_left, &middle, &target_right],
                    &line_file,
                    builtin_state,
                )?;
                let type_steps = match type_steps {
                    Some(steps) => Some(steps),
                    None => self.verify_objects_are_known_integers_in_builtin_leaf(
                        &[&target_left, &middle, &target_right],
                        &line_file,
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

    // A finite-set maximum bounds every member and a finite-set minimum is below every member,
    // including when the extremum is named by a known equality.
    // Examples: `x $in S` => `x <= finite_set_max(S)` and
    // `n = finite_set_max(S), x $in S` => `x <= n`.
    fn try_verify_finite_set_extrema_order_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
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
            let member_result =
                self.verify_known_or_concrete_finite_set_membership(&member_fact)?;
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
        for maximum in self.known_equal_finite_set_max_candidates(&fact.right) {
            let maximum_obj: Obj = maximum.clone().into();
            let equality_result = self.verify_objs_are_equal_by_known_equality(
                &fact.right,
                &maximum_obj,
                fact.line_file.clone(),
            );
            if !equality_result.is_true() {
                continue;
            }
            let member_fact: AtomicFact = InFact::new(
                fact.left.clone(),
                maximum.set.as_ref().clone(),
                fact.line_file.clone(),
            )
            .into();
            let member_result =
                self.verify_known_or_concrete_finite_set_membership(&member_fact)?;
            if member_result.is_true() {
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "finite_set_max: every member is at most a known-equal maximum".to_string(),
                        vec![equality_result, member_result],
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
            let member_result =
                self.verify_known_or_concrete_finite_set_membership(&member_fact)?;
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
        for minimum in self.known_equal_finite_set_min_candidates(&fact.left) {
            let minimum_obj: Obj = minimum.clone().into();
            let equality_result = self.verify_objs_are_equal_by_known_equality(
                &fact.left,
                &minimum_obj,
                fact.line_file.clone(),
            );
            if !equality_result.is_true() {
                continue;
            }
            let member_fact: AtomicFact = InFact::new(
                fact.right.clone(),
                minimum.set.as_ref().clone(),
                fact.line_file.clone(),
            )
            .into();
            let member_result =
                self.verify_known_or_concrete_finite_set_membership(&member_fact)?;
            if member_result.is_true() {
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "finite_set_min: a known-equal minimum is at most every member".to_string(),
                        vec![equality_result, member_result],
                    )
                    .into(),
                ));
            }
        }

        Ok(None)
    }

    fn verify_known_or_concrete_finite_set_membership(
        &mut self,
        member_fact: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        let known = self.verify_known_non_forall_atomic_fact(member_fact)?;
        if known.is_true() {
            return Ok(known);
        }
        let AtomicFact::InFact(in_fact) = member_fact else {
            return Ok(StmtUnknown::new().into());
        };
        if !object_is_explicit_member_of_finite_set_expression(&in_fact.element, &in_fact.set) {
            return Ok(StmtUnknown::new().into());
        }
        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                member_fact.clone().into(),
                "membership by concrete finite-set structure".to_string(),
                Vec::new(),
            )
            .into(),
        )
    }

    fn known_equal_finite_set_max_candidates(&self, obj: &Obj) -> Vec<FiniteSetMax> {
        let key = obj_equality_key(obj);
        let mut candidates = Vec::new();
        for environment in self.iter_environments_from_top() {
            let Some((_, equal_objs)) = environment.known_equality.get(&key) else {
                continue;
            };
            for equal_obj in equal_objs.iter() {
                let Obj::FiniteSetMax(maximum) = equal_obj else {
                    continue;
                };
                if !candidates
                    .iter()
                    .any(|seen: &FiniteSetMax| seen.to_string() == maximum.to_string())
                {
                    candidates.push(maximum.clone());
                }
            }
        }
        candidates
    }

    fn known_equal_finite_set_min_candidates(&self, obj: &Obj) -> Vec<FiniteSetMin> {
        let key = obj_equality_key(obj);
        let mut candidates = Vec::new();
        for environment in self.iter_environments_from_top() {
            let Some((_, equal_objs)) = environment.known_equality.get(&key) else {
                continue;
            };
            for equal_obj in equal_objs.iter() {
                let Obj::FiniteSetMin(minimum) = equal_obj else {
                    continue;
                };
                if !candidates
                    .iter()
                    .any(|seen: &FiniteSetMin| seen.to_string() == minimum.to_string())
                {
                    candidates.push(minimum.clone());
                }
            }
        }
        candidates
    }

    // Integer discreteness at one successor/predecessor step.
    // Examples: `a < b` => `a + 1 <= b`, and `a < b` => `a <= b - 1`.
    fn try_verify_integer_successor_predecessor_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(AtomicFact::LessEqualFact(fact)) =
            normalize_positive_order_atomic_fact(atomic_fact)
        else {
            return Ok(None);
        };

        // Integer adjacency removes one successor from a strict upper bound.
        // Example: `a < b + 1` => `a <= b` for integers `a` and `b`.
        if let Some(mut steps) = self.verify_objects_are_known_integers_in_builtin_leaf(
            &[&fact.left, &fact.right],
            &fact.line_file,
        )? {
            let strict: AtomicFact = LessFact::new(
                fact.left.clone(),
                obj_plus_one(&fact.right),
                fact.line_file.clone(),
            )
            .into();
            let strict_result = self.verify_builtin_rule_premise(&strict, builtin_state)?;
            if strict_result.is_true() {
                steps.push(strict_result);
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "integer adjacency: a < b + 1 gives a <= b".to_string(),
                        steps,
                    )
                    .into(),
                ));
            }
        }

        if let Some(predecessor) = obj_plus_one_base(&fact.left) {
            let Some(mut steps) = self.verify_objects_are_known_integers_in_builtin_leaf(
                &[&predecessor, &fact.right],
                &fact.line_file,
            )?
            else {
                return Ok(None);
            };
            let strict: AtomicFact =
                LessFact::new(predecessor, fact.right.clone(), fact.line_file.clone()).into();
            let strict_result = self.verify_builtin_rule_premise(&strict, builtin_state)?;
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
            let Some(mut steps) = self.verify_objects_are_known_integers_in_builtin_leaf(
                &[&fact.left, &successor],
                &fact.line_file,
            )?
            else {
                return Ok(None);
            };
            let strict: AtomicFact =
                LessFact::new(fact.left.clone(), successor, fact.line_file.clone()).into();
            let strict_result = self.verify_builtin_rule_premise(&strict, builtin_state)?;
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
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (subject, base) in [(left, right), (right, left)] {
            let Some(mut steps) = self
                .verify_objects_are_known_integers_in_builtin_leaf(&[subject, base], &line_file)?
            else {
                continue;
            };
            let lower: AtomicFact =
                LessEqualFact::new(base.clone(), subject.clone(), line_file.clone()).into();
            let upper: AtomicFact =
                LessFact::new(subject.clone(), obj_plus_one(base), line_file.clone()).into();
            let lower_result = self.verify_builtin_rule_premise(&lower, builtin_state)?;
            if lower_result.is_unknown() {
                continue;
            }
            let upper_result = self.verify_builtin_rule_premise(&upper, builtin_state)?;
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

        // The adjacent singleton interval has the successor as its only integer point.
        // Example: `n < x`, `x <= n + 1` => `x = n + 1`.
        for (subject, successor) in [(left, right), (right, left)] {
            let Some(base) = obj_plus_one_base(successor) else {
                continue;
            };
            let Some(mut steps) = self
                .verify_objects_are_known_integers_in_builtin_leaf(&[subject, &base], &line_file)?
            else {
                continue;
            };
            let lower: AtomicFact = LessFact::new(base, subject.clone(), line_file.clone()).into();
            let upper: AtomicFact =
                LessEqualFact::new(subject.clone(), successor.clone(), line_file.clone()).into();
            let lower_result = self.verify_builtin_rule_premise(&lower, builtin_state)?;
            if lower_result.is_unknown() {
                continue;
            }
            let upper_result = self.verify_builtin_rule_premise(&upper, builtin_state)?;
            if upper_result.is_unknown() {
                continue;
            }
            steps.push(lower_result);
            steps.push(upper_result);
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    EqualFact::new(left.clone(), right.clone(), line_file).into(),
                    "integer successor singleton interval: n < x <= n + 1 gives x = n + 1"
                        .to_string(),
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
        let Some(steps) = self.verify_objects_are_known_integers_in_builtin_leaf(
            &[&subject, &base],
            &or_fact.line_file,
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
}
