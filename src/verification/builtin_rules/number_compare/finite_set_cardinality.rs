//! Finite-set cardinality order bounds.

use super::*;

impl Runtime {
    // A nonempty finite set has at least one element.
    // Example: `$is_finite_set(S)`, `$is_nonempty_set(S)` => `finite_set_size(S) >= 1`.
    pub(in crate::verification) fn try_verify_finite_nonempty_set_size_at_least_one(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (finite_set_size_obj, line_file) = match atomic_fact {
            AtomicFact::GreaterEqualFact(f) => {
                let Some(right) = self.resolve_obj_to_number(&f.right) else {
                    return Ok(None);
                };
                if !matches!(
                    compare_number_strings(&right.normalized_value, "1"),
                    NumberCompareResult::Equal
                ) {
                    return Ok(None);
                }
                (f.left.clone(), f.line_file.clone())
            }
            AtomicFact::LessEqualFact(f) => {
                let Some(left) = self.resolve_obj_to_number(&f.left) else {
                    return Ok(None);
                };
                if !matches!(
                    compare_number_strings(&left.normalized_value, "1"),
                    NumberCompareResult::Equal
                ) {
                    return Ok(None);
                }
                (f.right.clone(), f.line_file.clone())
            }
            _ => return Ok(None),
        };
        let Obj::FiniteSetSize(finite_set_size) = finite_set_size_obj else {
            return Ok(None);
        };
        let set = (*finite_set_size.set).clone();

        let finite: AtomicFact = IsFiniteSetFact::new(set.clone(), line_file.clone()).into();
        let finite_result =
            self.verify_atomic_fact_as_builtin_rule_premise(&finite, builtin_state)?;
        if !finite_result.is_success() {
            return Ok(None);
        }

        let nonempty: AtomicFact = IsNonemptySetFact::new(set, line_file).into();
        let nonempty_result =
            self.verify_atomic_fact_as_builtin_rule_premise(&nonempty, builtin_state)?;
        if !nonempty_result.is_success() {
            return Ok(None);
        }

        Ok(Some(
            SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                atomic_fact.clone().into(),
                SuccessInferResult::new(),
                "finite_nonempty_set_size_at_least_one".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyFiniteNonemptySetSizeAtLeastOne,
                ),
                vec![finite_result, nonempty_result],
            )
            .into(),
        ))
    }

    // Cardinality is nonnegative even when the finite set may be empty.
    // Keep this direct bridge separate from the nonempty lower bound so a
    // symbolic `finite_set` parameter does not need a recursive N-membership
    // round merely to prove `finite_set_size(S) >= 0`.
    pub(in crate::verification) fn try_verify_finite_set_size_nonnegative(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let is_zero =
            |obj: &Obj| matches!(obj, Obj::Number(number) if number.normalized_value == "0");
        let (size, line_file) = match atomic_fact {
            AtomicFact::GreaterEqualFact(f) if is_zero(&f.right) => (&f.left, f.line_file.clone()),
            AtomicFact::LessEqualFact(f) if is_zero(&f.left) => (&f.right, f.line_file.clone()),
            _ => return Ok(None),
        };
        let Obj::FiniteSetSize(size) = size else {
            return Ok(None);
        };
        let finite: AtomicFact = IsFiniteSetFact::new(size.set.as_ref().clone(), line_file).into();
        let result = self.verify_atomic_fact_as_builtin_rule_premise(&finite, builtin_state)?;
        if !result.is_success() {
            return Ok(None);
        }
        Ok(Some(
            SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "finite set cardinality is nonnegative".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyFiniteSetSizeNonnegative,
                ),
                vec![result],
            )
            .into(),
        ))
    }

    // The cardinality of a finite subset is at most that of its finite container.
    // Example: `A $subset B` with finite `A` and `B` gives
    // `finite_set_size(A) <= finite_set_size(B)`.
    pub(in crate::verification) fn try_verify_finite_set_size_subset_le(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (left_size, right_size, line_file) = match atomic_fact {
            AtomicFact::LessEqualFact(fact) => (&fact.left, &fact.right, fact.line_file.clone()),
            AtomicFact::GreaterEqualFact(fact) => (&fact.right, &fact.left, fact.line_file.clone()),
            _ => return Ok(None),
        };
        let Obj::FiniteSetSize(left_size) = left_size else {
            return Ok(None);
        };
        let Obj::FiniteSetSize(right_size) = right_size else {
            return Ok(None);
        };

        if let Obj::Intersect(intersection) = left_size.set.as_ref() {
            let right_matches_left =
                objs_match_for_pattern(intersection.left.as_ref(), right_size.set.as_ref());
            let right_matches_right =
                objs_match_for_pattern(intersection.right.as_ref(), right_size.set.as_ref());
            if right_matches_left || right_matches_right {
                let left_input: AtomicFact =
                    IsFiniteSetFact::new(intersection.left.as_ref().clone(), line_file.clone())
                        .into();
                let right_input: AtomicFact =
                    IsFiniteSetFact::new(intersection.right.as_ref().clone(), line_file.clone())
                        .into();
                let left_result =
                    self.verify_atomic_fact_as_builtin_rule_premise(&left_input, builtin_state)?;
                let right_result =
                    self.verify_atomic_fact_as_builtin_rule_premise(&right_input, builtin_state)?;
                if left_result.is_success() && right_result.is_success() {
                    return Ok(Some(
                        SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                            atomic_fact.clone().into(),
                            SuccessInferResult::new(),
                            "finite_set_size_subset_le".to_string(),
                            BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryVerifyFiniteSetSizeSubsetLe01),
                            vec![left_result, right_result],
                        )
                        .into(),
                    ));
                }
            }
        }

        let subset: AtomicFact = SubsetFact::new(
            left_size.set.as_ref().clone(),
            right_size.set.as_ref().clone(),
            line_file.clone(),
        )
        .into();
        let mut subset_result =
            self.verify_atomic_fact_as_builtin_rule_premise(&subset, builtin_state)?;
        if !subset_result.is_success() {
            let superset: AtomicFact = SupersetFact::new(
                right_size.set.as_ref().clone(),
                left_size.set.as_ref().clone(),
                line_file.clone(),
            )
            .into();
            subset_result =
                self.verify_non_equational_atomic_fact_with_known_atomic_facts(&superset)?;
        }
        if !subset_result.is_success() {
            return Ok(None);
        }

        let left_finite: AtomicFact =
            IsFiniteSetFact::new(left_size.set.as_ref().clone(), line_file.clone()).into();
        let left_result =
            self.verify_atomic_fact_as_builtin_rule_premise(&left_finite, builtin_state)?;
        if !left_result.is_success() {
            return Ok(None);
        }

        let right_finite: AtomicFact =
            IsFiniteSetFact::new(right_size.set.as_ref().clone(), line_file).into();
        let right_result =
            self.verify_atomic_fact_as_builtin_rule_premise(&right_finite, builtin_state)?;
        if !right_result.is_success() {
            return Ok(None);
        }

        Ok(Some(
            SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                atomic_fact.clone().into(),
                SuccessInferResult::new(),
                "finite_set_size_subset_le".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyFiniteSetSizeSubsetLe02,
                ),
                vec![subset_result, left_result, right_result],
            )
            .into(),
        ))
    }

    // A union has at most the sum of its two finite inputs.
    // Example: `finite_set_size(union(A, B)) <= finite_set_size(A) + finite_set_size(B)`.
    pub(in crate::verification) fn try_verify_finite_set_size_union_le_sum(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (smaller, larger, line_file) = match atomic_fact {
            AtomicFact::LessEqualFact(fact) => (&fact.left, &fact.right, fact.line_file.clone()),
            AtomicFact::GreaterEqualFact(fact) => (&fact.right, &fact.left, fact.line_file.clone()),
            _ => return Ok(None),
        };
        let Obj::FiniteSetSize(combined_size) = smaller else {
            return Ok(None);
        };
        let Obj::Add(sum) = larger else {
            return Ok(None);
        };
        let Obj::FiniteSetSize(left_size) = sum.left.as_ref() else {
            return Ok(None);
        };
        let Obj::FiniteSetSize(right_size) = sum.right.as_ref() else {
            return Ok(None);
        };

        let (left_set, right_set) = match combined_size.set.as_ref() {
            Obj::Union(union) => (union.left.as_ref().clone(), union.right.as_ref().clone()),
            _ => return Ok(None),
        };
        if !objs_match_for_pattern(&left_set, &left_size.set)
            || !objs_match_for_pattern(&right_set, &right_size.set)
        {
            return Ok(None);
        }

        let left_finite: AtomicFact = IsFiniteSetFact::new(left_set, line_file.clone()).into();
        let left_result =
            self.verify_atomic_fact_as_builtin_rule_premise(&left_finite, builtin_state)?;
        if !left_result.is_success() {
            return Ok(None);
        }
        let right_finite: AtomicFact = IsFiniteSetFact::new(right_set, line_file).into();
        let right_result =
            self.verify_atomic_fact_as_builtin_rule_premise(&right_finite, builtin_state)?;
        if !right_result.is_success() {
            return Ok(None);
        }

        Ok(Some(
            SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                atomic_fact.clone().into(),
                SuccessInferResult::new(),
                "finite_set_size_union_le_sum".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyFiniteSetSizeUnionLeSum,
                ),
                vec![left_result, right_result],
            )
            .into(),
        ))
    }
}
