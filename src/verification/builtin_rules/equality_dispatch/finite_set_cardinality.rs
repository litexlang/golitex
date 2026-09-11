//! Finite-set cardinality equalities.

use crate::prelude::*;
use crate::verification::verify_equality_by_builtin_rules::objs_match_for_pattern;

impl Runtime {
    pub(super) fn try_verify_cart_finite_set_size_product_equality(
        &self,
        equal_fact: &EqualFact,
    ) -> Option<ProveFactResult> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        // Cardinality of a finite Cartesian product is the product of factor cardinalities.
        // Example: `finite_set_size(cart(A, B)) = finite_set_size(A) * finite_set_size(B)`.
        if Self::cart_finite_set_size_product_shape(left, right)
            || Self::cart_finite_set_size_product_shape(right, left)
        {
            return Some(Self::set_equality_success(
                equal_fact,
                "cart_finite_set_size_product",
                None,
            ));
        }

        None
    }

    pub(super) fn try_verify_finite_set_size_set_minus_equality(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        // Removing a finite subset counts the original set minus its overlap with the removed set.
        // Example: `finite_set_size(set_minus(S, T)) = finite_set_size(S) - finite_set_size(intersect(S, T))`.
        let Some((first_set, second_set)) = Self::finite_set_size_set_minus_shape(left, right)
            .or_else(|| Self::finite_set_size_set_minus_shape(right, left))
        else {
            return Ok(None);
        };

        let first_finite: AtomicFact = self
            .new_is_finite_set_fact(first_set, line_file.clone())
            .into();
        let Some(first_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&first_finite, builtin_state)?
        else {
            return Ok(None);
        };

        let second_finite: AtomicFact = self
            .new_is_finite_set_fact(second_set, line_file.clone())
            .into();
        let Some(second_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&second_finite, builtin_state)?
        else {
            return Ok(None);
        };

        Ok(Some(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                equal_fact.clone().into(),
                "finite_set_size_set_minus".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyFiniteSetSizeSetMinusEquality,
                ),
                vec![first_result, second_result],
            )
            .into(),
        ))
    }

    // Inclusion-exclusion counts the union of two finite sets.
    // Example: `finite_set_size(union(A, B)) = finite_set_size(A) + finite_set_size(B) - finite_set_size(intersect(A, B))`.
    pub(super) fn try_verify_finite_set_size_union_equality(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let Some((first_set, second_set)) = Self::finite_set_size_union_shape(left, right)
            .or_else(|| Self::finite_set_size_union_shape(right, left))
        else {
            return Ok(None);
        };
        let Some(step_results) = self.verify_two_sets_are_finite(
            first_set,
            second_set,
            line_file.clone(),
            builtin_state,
        )?
        else {
            return Ok(None);
        };

        Ok(Some(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                equal_fact.clone().into(),
                "finite_set_size_union_inclusion_exclusion".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyFiniteSetSizeUnionEquality,
                ),
                step_results,
            )
            .into(),
        ))
    }

    // A finite set partitions into its overlap with another set and the remainder.
    // Example: `finite_set_size(A) = finite_set_size(intersect(A, B)) + finite_set_size(set_minus(A, B))`.
    pub(super) fn try_verify_finite_set_size_partition_equality(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let Some((first_set, second_set)) = Self::finite_set_size_partition_shape(left, right)
            .or_else(|| Self::finite_set_size_partition_shape(right, left))
        else {
            return Ok(None);
        };
        let Some(step_results) = self.verify_two_sets_are_finite(
            first_set,
            second_set,
            line_file.clone(),
            builtin_state,
        )?
        else {
            return Ok(None);
        };

        Ok(Some(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                equal_fact.clone().into(),
                "finite_set_size_partition_by_intersection_and_difference".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyFiniteSetSizePartitionEquality,
                ),
                step_results,
            )
            .into(),
        ))
    }

    // Removing a finite subset subtracts exactly that subset's cardinality.
    // Example: `B $subset A` gives `finite_set_size(set_minus(A, B)) = finite_set_size(A) - finite_set_size(B)`.
    pub(super) fn try_verify_finite_set_size_set_minus_of_subset_equality(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let Some((container, subset)) =
            Self::finite_set_size_set_minus_of_subset_shape(left, right)
                .or_else(|| Self::finite_set_size_set_minus_of_subset_shape(right, left))
        else {
            return Ok(None);
        };

        let subset_fact: AtomicFact = self
            .new_subset_fact(subset.clone(), container.clone(), line_file.clone())
            .into();
        let Some(subset_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&subset_fact, builtin_state)?
        else {
            return Ok(None);
        };
        let container_finite: AtomicFact = self
            .new_is_finite_set_fact(container, line_file.clone())
            .into();
        let Some(container_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&container_finite, builtin_state)?
        else {
            return Ok(None);
        };
        let subset_finite: AtomicFact = self
            .new_is_finite_set_fact(subset, line_file.clone())
            .into();
        let Some(subset_finite_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&subset_finite, builtin_state)?
        else {
            return Ok(None);
        };

        Ok(Some(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                equal_fact.clone().into(),
                "finite_set_size_set_minus_finite_subset".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyFiniteSetSizeSetMinusOfSubsetEquality,
                ),
                vec![subset_result, container_result, subset_finite_result],
            )
            .into(),
        ))
    }

    // Integer interval cardinalities are determined by their natural endpoints.
    // Examples: `finite_set_size(closed_range(a, b)) = b - a + 1` and
    // `finite_set_size(range(a, b)) = b - a` when `a <= b` and both endpoints are natural.
    pub(super) fn try_verify_finite_set_size_integer_range_equality(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let Some((start, end, closed)) = Self::finite_set_size_integer_range_shape(left, right)
            .or_else(|| Self::finite_set_size_integer_range_shape(right, left))
        else {
            return Ok(None);
        };

        let start_in_n: AtomicFact = self
            .new_in_fact(start.clone(), StandardSet::N.into(), line_file.clone())
            .into();
        let Some(start_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&start_in_n, builtin_state)?
        else {
            return Ok(None);
        };

        let end_in_n: AtomicFact = self
            .new_in_fact(end.clone(), StandardSet::N.into(), line_file.clone())
            .into();
        let Some(end_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&end_in_n, builtin_state)?
        else {
            return Ok(None);
        };

        let endpoints_ordered: AtomicFact = self
            .new_less_equal_fact(start, end, line_file.clone())
            .into();
        let Some(order_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&endpoints_ordered, builtin_state)?
        else {
            return Ok(None);
        };

        let rule = if closed {
            "finite_set_size_closed_range"
        } else {
            "finite_set_size_range"
        };
        Ok(Some(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                equal_fact.clone().into(),
                rule.to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyFiniteSetSizeIntegerRangeEquality,
                ),
                vec![start_result, end_result, order_result],
            )
            .into(),
        ))
    }

    pub(super) fn try_verify_power_set_finite_set_size_equality(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        // Cardinality of a finite power set is `2` to the cardinality of the base set.
        // Example: from `$is_finite_set(S)`, prove `finite_set_size(power_set(S)) = 2^finite_set_size(S)`.
        let Some(base_set) = Self::power_set_finite_set_size_shape(left, right)
            .or_else(|| Self::power_set_finite_set_size_shape(right, left))
        else {
            return Ok(None);
        };

        let base_finite: AtomicFact = self
            .new_is_finite_set_fact(base_set, line_file.clone())
            .into();
        let Some(base_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&base_finite, builtin_state)?
        else {
            return Ok(None);
        };

        Ok(Some(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                equal_fact.clone().into(),
                "power_set_finite_set_size_two_pow_finite_set_size_base".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyPowerSetFiniteSetSizeEquality,
                ),
                vec![base_result],
            )
            .into(),
        ))
    }

    pub(super) fn cart_finite_set_size_product_shape(
        finite_set_size_side: &Obj,
        product_side: &Obj,
    ) -> bool {
        let Obj::FiniteSetSize(finite_set_size) = finite_set_size_side else {
            return false;
        };
        let Obj::Cart(cart) = finite_set_size.set.as_ref() else {
            return false;
        };
        let Some(expected_product) = Self::count_product_for_cart_args(&cart.args) else {
            return false;
        };
        objs_match_for_pattern(&expected_product, product_side)
    }

    pub(super) fn finite_set_size_set_minus_shape(
        finite_set_size_side: &Obj,
        subtraction_side: &Obj,
    ) -> Option<(Obj, Obj)> {
        let Obj::FiniteSetSize(set_minus_size) = finite_set_size_side else {
            return None;
        };
        let Obj::SetMinus(set_minus) = set_minus_size.set.as_ref() else {
            return None;
        };
        let Obj::Sub(subtraction) = subtraction_side else {
            return None;
        };
        let Obj::FiniteSetSize(first_size) = subtraction.left.as_ref() else {
            return None;
        };
        let Obj::FiniteSetSize(intersection_size) = subtraction.right.as_ref() else {
            return None;
        };
        let Obj::Intersect(intersection) = intersection_size.set.as_ref() else {
            return None;
        };

        if objs_match_for_pattern(&set_minus.left, &first_size.set)
            && objs_match_for_pattern(&set_minus.left, &intersection.left)
            && objs_match_for_pattern(&set_minus.right, &intersection.right)
        {
            Some((
                set_minus.left.as_ref().clone(),
                set_minus.right.as_ref().clone(),
            ))
        } else {
            None
        }
    }

    pub(super) fn finite_set_size_union_shape(
        finite_set_size_side: &Obj,
        inclusion_exclusion_side: &Obj,
    ) -> Option<(Obj, Obj)> {
        let Obj::FiniteSetSize(union_size) = finite_set_size_side else {
            return None;
        };
        let Obj::Union(union) = union_size.set.as_ref() else {
            return None;
        };
        let Obj::Sub(subtraction) = inclusion_exclusion_side else {
            return None;
        };
        let Obj::Add(sum) = subtraction.left.as_ref() else {
            return None;
        };
        let Obj::FiniteSetSize(first_size) = sum.left.as_ref() else {
            return None;
        };
        let Obj::FiniteSetSize(second_size) = sum.right.as_ref() else {
            return None;
        };
        let Obj::FiniteSetSize(intersection_size) = subtraction.right.as_ref() else {
            return None;
        };
        let Obj::Intersect(intersection) = intersection_size.set.as_ref() else {
            return None;
        };

        if objs_match_for_pattern(&union.left, &first_size.set)
            && objs_match_for_pattern(&union.right, &second_size.set)
            && objs_match_for_pattern(&union.left, &intersection.left)
            && objs_match_for_pattern(&union.right, &intersection.right)
        {
            Some((union.left.as_ref().clone(), union.right.as_ref().clone()))
        } else {
            None
        }
    }

    pub(super) fn finite_set_size_partition_shape(
        finite_set_size_side: &Obj,
        partition_side: &Obj,
    ) -> Option<(Obj, Obj)> {
        let Obj::FiniteSetSize(main_size) = finite_set_size_side else {
            return None;
        };
        let Obj::Add(sum) = partition_side else {
            return None;
        };
        let Obj::FiniteSetSize(intersection_size) = sum.left.as_ref() else {
            return None;
        };
        let Obj::Intersect(intersection) = intersection_size.set.as_ref() else {
            return None;
        };
        let Obj::FiniteSetSize(remainder_size) = sum.right.as_ref() else {
            return None;
        };
        let Obj::SetMinus(remainder) = remainder_size.set.as_ref() else {
            return None;
        };

        if objs_match_for_pattern(&main_size.set, &intersection.left)
            && objs_match_for_pattern(&main_size.set, &remainder.left)
            && objs_match_for_pattern(&intersection.right, &remainder.right)
        {
            Some((
                main_size.set.as_ref().clone(),
                intersection.right.as_ref().clone(),
            ))
        } else if objs_match_for_pattern(&main_size.set, &intersection.right)
            && objs_match_for_pattern(&main_size.set, &remainder.left)
            && objs_match_for_pattern(&intersection.left, &remainder.right)
        {
            Some((
                main_size.set.as_ref().clone(),
                intersection.left.as_ref().clone(),
            ))
        } else {
            None
        }
    }

    pub(super) fn finite_set_size_set_minus_of_subset_shape(
        finite_set_size_side: &Obj,
        subtraction_side: &Obj,
    ) -> Option<(Obj, Obj)> {
        let Obj::FiniteSetSize(remainder_size) = finite_set_size_side else {
            return None;
        };
        let Obj::SetMinus(remainder) = remainder_size.set.as_ref() else {
            return None;
        };
        let Obj::Sub(subtraction) = subtraction_side else {
            return None;
        };
        let Obj::FiniteSetSize(container_size) = subtraction.left.as_ref() else {
            return None;
        };
        let Obj::FiniteSetSize(subset_size) = subtraction.right.as_ref() else {
            return None;
        };

        if objs_match_for_pattern(&remainder.left, &container_size.set)
            && objs_match_for_pattern(&remainder.right, &subset_size.set)
        {
            Some((
                remainder.left.as_ref().clone(),
                remainder.right.as_ref().clone(),
            ))
        } else {
            None
        }
    }

    pub(super) fn verify_two_sets_are_finite(
        &mut self,
        first_set: Obj,
        second_set: Obj,
        line_file: LineFile,
        _builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        let type_state = VerifyState::initial();
        let first_finite: AtomicFact = self
            .new_is_finite_set_fact(first_set, line_file.clone())
            .into();
        let first_result = self.verify_atomic_fact(&first_finite, &type_state)?;
        if !first_result.is_success() {
            return Ok(None);
        }
        let second_finite: AtomicFact = self.new_is_finite_set_fact(second_set, line_file).into();
        let second_result = self.verify_atomic_fact(&second_finite, &type_state)?;
        if !second_result.is_success() {
            return Ok(None);
        }
        Ok(Some(vec![first_result, second_result]))
    }

    pub(super) fn finite_set_size_integer_range_shape(
        finite_set_size_side: &Obj,
        cardinality_side: &Obj,
    ) -> Option<(Obj, Obj, bool)> {
        let Obj::FiniteSetSize(finite_set_size) = finite_set_size_side else {
            return None;
        };
        let (start, end, closed) = match finite_set_size.set.as_ref() {
            Obj::ClosedRange(range) => (range.start.as_ref(), range.end.as_ref(), true),
            Obj::Range(range) => (range.start.as_ref(), range.end.as_ref(), false),
            _ => return None,
        };
        let difference: Obj = Sub::new(end.clone(), start.clone()).into();
        let expected_cardinality: Obj = if closed {
            Add::new(difference, Number::new("1".to_string()).into()).into()
        } else {
            difference
        };
        if !objs_match_for_pattern(&expected_cardinality, cardinality_side) {
            return None;
        }
        Some((start.clone(), end.clone(), closed))
    }

    pub(super) fn power_set_finite_set_size_shape(
        finite_set_size_side: &Obj,
        pow_side: &Obj,
    ) -> Option<Obj> {
        let Obj::FiniteSetSize(finite_set_size) = finite_set_size_side else {
            return None;
        };
        let Obj::PowerSet(power_set) = finite_set_size.set.as_ref() else {
            return None;
        };
        let two: Obj = Number::new("2".to_string()).into();
        let base_finite_set_size: Obj = FiniteSetSize::new(power_set.set.as_ref().clone()).into();
        let expected_pow: Obj = Pow::new(two, base_finite_set_size).into();
        if objs_match_for_pattern(&expected_pow, pow_side) {
            Some(power_set.set.as_ref().clone())
        } else {
            None
        }
    }

    pub(super) fn count_product_for_cart_args(args: &[Box<Obj>]) -> Option<Obj> {
        let mut iter = args.iter();
        let first = iter.next()?;
        let mut product: Obj = FiniteSetSize::new(first.as_ref().clone()).into();
        for arg in iter {
            let factor_finite_set_size: Obj = FiniteSetSize::new(arg.as_ref().clone()).into();
            product = Mul::new(product, factor_finite_set_size).into();
        }
        Some(product)
    }
}
