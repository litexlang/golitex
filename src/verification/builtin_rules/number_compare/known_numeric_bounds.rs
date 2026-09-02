//! Known lower and upper numeric bound reuse.

use super::*;

impl Runtime {
    /// Numeric lower-bound weakening, with the integer successor case.
    /// Examples: from `4 < x`, prove `2 <= x`; from `x $in Z` and `4 < x`, prove `5 <= x`.
    pub(in crate::verification) fn try_verify_numeric_lower_bound_from_known_lower_bound(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        match &norm {
            AtomicFact::LessEqualFact(f) => {
                let Some(target_bound) = self.resolved_integer_value_for_order_bound(&f.left)
                else {
                    return Ok(None);
                };
                let candidates = self.collect_known_lower_bound_candidates(&f.right);
                for candidate in candidates {
                    let Some((known_bound, known_strict)) =
                        self.known_lower_bound_candidate_value(&candidate, &f.right)
                    else {
                        continue;
                    };
                    let candidate_result = self.verify_atomic_fact_as_builtin_rule_premise(&candidate, builtin_state)?;
                    if !candidate_result.is_success() {
                        continue;
                    }
                    // Strict order implies weak order at the same bound.
                    // Example: from `0 < c`, prove `0 <= c`.
                    if target_bound == known_bound && known_strict {
                        return Ok(Some(ProveFactResult::from(
                            SuccessProveFactResult::
                                new_with_verified_by_builtin_rule_evidence_recording_stmt(
                                    atomic_fact.clone().into(),
                                    "less_equal_fact_from_known_strict_order".to_string(),
                                    BuiltinRuleEvidence::Arithmetic(
                                        ArithmeticBuiltinRule::LessEqualFromStrictOrder,
                                    ),
                                    vec![candidate_result],
                                ),
                        )));
                    }
                    if target_bound <= known_bound {
                        return Ok(Some(ProveFactResult::from(
                            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                                atomic_fact.clone().into(),
                                "weaken numeric lower bound from known lower bound".to_string(),
                                BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryVerifyNumericLowerBoundFromKnownLowerBound01),
                                vec![candidate_result],
                            ),
                        )));
                    }
                    if known_strict && known_bound.checked_add(1) == Some(target_bound) {
                        let in_z: AtomicFact = InFact::new(
                            f.right.clone(),
                            StandardSet::Z.into(),
                            f.line_file.clone(),
                        )
                        .into();
                        let in_z_result =
                            self.verify_atomic_fact_as_builtin_rule_premise(&in_z, builtin_state)?;
                        if !in_z_result.is_success() {
                            continue;
                        }
                        return Ok(Some(ProveFactResult::from(
                            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                                atomic_fact.clone().into(),
                                "integer weak lower bound from strict predecessor lower bound"
                                    .to_string(),
                                BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryVerifyNumericLowerBoundFromKnownLowerBound02),
                                vec![candidate_result, in_z_result],
                            ),
                        )));
                    }
                }
            }
            AtomicFact::LessFact(f) => {
                let Some(target_bound) = self.resolved_integer_value_for_order_bound(&f.left)
                else {
                    return Ok(None);
                };
                let candidates = self.collect_known_lower_bound_candidates(&f.right);
                for candidate in candidates {
                    let Some((known_bound, known_strict)) =
                        self.known_lower_bound_candidate_value(&candidate, &f.right)
                    else {
                        continue;
                    };
                    let stronger_bound_is_enough = if known_strict {
                        target_bound <= known_bound
                    } else {
                        target_bound < known_bound
                    };
                    if !stronger_bound_is_enough {
                        continue;
                    }
                    let candidate_result = self.verify_atomic_fact_as_builtin_rule_premise(&candidate, builtin_state)?;
                    if candidate_result.is_success() {
                        return Ok(Some(ProveFactResult::from(
                            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                                atomic_fact.clone().into(),
                                "weaken numeric strict lower bound from known lower bound"
                                    .to_string(),
                                BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryVerifyNumericLowerBoundFromKnownLowerBound03),
                                vec![candidate_result],
                            ),
                        )));
                    }
                }
            }
            _ => {}
        }
        Ok(None)
    }

    pub(in crate::verification) fn collect_known_lower_bound_candidates(
        &self,
        right: &Obj,
    ) -> Vec<AtomicFact> {
        let mut candidates = Vec::new();
        for environment in self.iter_environments_from_top() {
            for known_facts_map in environment.facts.atomic.by_two_args.values() {
                for known_fact in known_facts_map.values() {
                    if self
                        .known_lower_bound_candidate_value(known_fact, right)
                        .is_some()
                    {
                        candidates.push(known_fact.clone());
                    }
                }
            }
        }
        candidates
    }

    pub(in crate::verification) fn known_lower_bound_candidate_value(
        &self,
        known_fact: &AtomicFact,
        right: &Obj,
    ) -> Option<(i128, bool)> {
        let norm = normalize_positive_order_atomic_fact(known_fact)?;
        match &norm {
            AtomicFact::LessFact(f) if f.right.to_string() == right.to_string() => {
                Some((self.resolved_integer_value_for_order_bound(&f.left)?, true))
            }
            AtomicFact::LessEqualFact(f) if f.right.to_string() == right.to_string() => {
                Some((self.resolved_integer_value_for_order_bound(&f.left)?, false))
            }
            _ => None,
        }
    }

    /// Numeric upper-bound weakening.
    /// Examples: from `x < 4`, prove `x <= 6`; from `x <= 4`, prove `x < 6`.
    pub(in crate::verification) fn try_verify_numeric_upper_bound_from_known_upper_bound(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let (target_bound, target_is_strict, target_left) = match &norm {
            AtomicFact::LessEqualFact(f) => (
                self.resolved_integer_value_for_order_bound(&f.right),
                false,
                &f.left,
            ),
            AtomicFact::LessFact(f) => (
                self.resolved_integer_value_for_order_bound(&f.right),
                true,
                &f.left,
            ),
            _ => return Ok(None),
        };
        let Some(target_bound) = target_bound else {
            return Ok(None);
        };

        for candidate in self.collect_known_upper_bound_candidates(target_left) {
            let Some((known_bound, known_is_strict)) =
                self.known_upper_bound_candidate_value(&candidate, target_left)
            else {
                continue;
            };
            let candidate_is_enough = if target_is_strict {
                known_bound < target_bound || (known_is_strict && known_bound == target_bound)
            } else {
                known_bound <= target_bound
            };
            if !candidate_is_enough {
                continue;
            }

            let candidate_result = self.verify_atomic_fact_as_builtin_rule_premise(&candidate, builtin_state)?;
            if !candidate_result.is_success() {
                continue;
            }
            return Ok(Some(ProveFactResult::from(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    atomic_fact.clone().into(),
                    "weaken numeric upper bound from known upper bound".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::TryVerifyNumericUpperBoundFromKnownUpperBound,
                    ),
                    vec![candidate_result],
                ),
            )));
        }
        Ok(None)
    }

    pub(in crate::verification) fn collect_known_upper_bound_candidates(
        &self,
        left: &Obj,
    ) -> Vec<AtomicFact> {
        let mut candidates = Vec::new();
        for environment in self.iter_environments_from_top() {
            for known_facts_map in environment.facts.atomic.by_two_args.values() {
                for known_fact in known_facts_map.values() {
                    if self
                        .known_upper_bound_candidate_value(known_fact, left)
                        .is_some()
                    {
                        candidates.push(known_fact.clone());
                    }
                }
            }
        }
        candidates
    }

    pub(in crate::verification) fn known_upper_bound_candidate_value(
        &self,
        known_fact: &AtomicFact,
        left: &Obj,
    ) -> Option<(i128, bool)> {
        let norm = normalize_positive_order_atomic_fact(known_fact)?;
        match &norm {
            AtomicFact::LessFact(f) if f.left.to_string() == left.to_string() => {
                Some((self.resolved_integer_value_for_order_bound(&f.right)?, true))
            }
            AtomicFact::LessEqualFact(f) if f.left.to_string() == left.to_string() => Some((
                self.resolved_integer_value_for_order_bound(&f.right)?,
                false,
            )),
            _ => None,
        }
    }

    pub(in crate::verification) fn resolved_integer_value_for_order_bound(
        &self,
        obj: &Obj,
    ) -> Option<i128> {
        let number = self.resolve_obj_to_number(obj)?;
        if !is_number_string_literally_integer_without_dot(number.normalized_value.clone()) {
            return None;
        }
        number.normalized_value.parse::<i128>().ok()
    }
}
