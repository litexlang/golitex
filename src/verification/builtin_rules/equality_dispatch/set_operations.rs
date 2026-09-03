//! Union, intersection, and set-minus equalities.

use crate::prelude::*;
use crate::verification::verify_equality_by_builtin_rules::objs_match_for_pattern;

impl Runtime {
    pub(super) fn try_verify_union_set_equalities(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        // Union commutativity for sets.
        // Example: `union(A, B) = union(B, A)`.
        if Self::union_commutative_shape(left, right) {
            return Ok(Some(Self::set_equality_success(
                equal_fact,
                "union_commutative",
                Some(SetBuiltinRule::UnionCommutative),
            )));
        }

        // Union associativity for sets, accepted in either equality direction.
        // Example: `union(union(A, B), C) = union(A, union(B, C))`.
        if Self::union_associative_shape(left, right) || Self::union_associative_shape(right, left)
        {
            return Ok(Some(Self::set_equality_success(
                equal_fact,
                "union_associative",
                Some(SetBuiltinRule::UnionAssociative),
            )));
        }

        // Union idempotence for sets, accepted in either equality direction.
        // Example: `union(A, A) = A`.
        if Self::union_idempotent_shape(left, right) || Self::union_idempotent_shape(right, left) {
            return Ok(Some(Self::set_equality_success(
                equal_fact,
                "union_idempotent",
                Some(SetBuiltinRule::UnionIdempotent),
            )));
        }

        // Empty set is a two-sided identity for union, accepted in either equality direction.
        // Example: `union(A, {}) = A` and `union({}, A) = A`.
        if let Some(rule) = Self::union_empty_identity_rule(left, right)
            .or_else(|| Self::union_empty_identity_rule(right, left))
        {
            return Ok(Some(Self::set_equality_success(
                equal_fact,
                "union_empty_identity",
                Some(rule),
            )));
        }

        // A set together with the part of another set outside it has the same
        // union as the two original sets. Natural operand orders and equality
        // directions are the same mathematical leaf.
        // Example: `union(A, set_minus(B, A)) = union(A, B)`.
        if Self::union_set_minus_decomposition_shape(left, right)
            || Self::union_set_minus_decomposition_shape(right, left)
        {
            return Ok(Some(Self::set_equality_success(
                equal_fact,
                "union_set_minus_decomposition",
                Some(SetBuiltinRule::UnionSetMinusDecomposition),
            )));
        }

        // A union with a known subset retains the containing operand.
        // Example: `A subset B` gives `union(A, B) = B`.
        if let Some((subset, container)) = Self::union_absorption_shape(left, right)
            .or_else(|| Self::union_absorption_shape(right, left))
        {
            let premise: AtomicFact =
                SubsetFact::new(subset, container, equal_fact.line_file.clone()).into();
            let result =
                self.try_verify_atomic_fact_as_builtin_rule_premise(&premise, builtin_state)?;
            if let Some(result) = result {
                return Ok(Some(Self::set_equality_success_with_subgoals(
                    equal_fact,
                    "union_absorption_from_subset",
                    SetBuiltinRule::UnionEqRightOfSubset,
                    vec![result],
                )));
            }
        }

        Ok(None)
    }

    pub(super) fn try_verify_intersection_set_equalities(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        // Intersection commutativity for sets.
        // Example: `intersect(A, B) = intersect(B, A)`.
        if Self::intersect_commutative_shape(left, right) {
            return Ok(Some(Self::set_equality_success(
                equal_fact,
                "intersect_commutative",
                Some(SetBuiltinRule::IntersectCommutative),
            )));
        }

        // Intersection associativity for sets, accepted in either equality direction.
        // Example: `intersect(intersect(A, B), C) = intersect(A, intersect(B, C))`.
        if Self::intersect_associative_shape(left, right)
            || Self::intersect_associative_shape(right, left)
        {
            return Ok(Some(Self::set_equality_success(
                equal_fact,
                "intersect_associative",
                Some(SetBuiltinRule::IntersectAssociative),
            )));
        }

        // Intersection distributes over union for sets, accepted in either equality direction.
        // Example: `intersect(A, union(B, C)) = union(intersect(A, B), intersect(A, C))`.
        if Self::intersect_union_distributive_shape(left, right)
            || Self::intersect_union_distributive_shape(right, left)
        {
            return Ok(Some(Self::set_equality_success(
                equal_fact,
                "intersect_union_distributive",
                Some(SetBuiltinRule::IntersectUnionDistributive),
            )));
        }

        // Intersection is idempotent.
        // Example: `intersect(A, A) = A`.
        if Self::intersect_idempotent_shape(left, right)
            || Self::intersect_idempotent_shape(right, left)
        {
            return Ok(Some(Self::set_equality_success(
                equal_fact,
                "intersect_idempotent",
                Some(SetBuiltinRule::IntersectIdempotent),
            )));
        }

        // A removed set is disjoint from the corresponding difference.
        // Example: `intersect(A, set_minus(B, A)) = {}`.
        if Self::intersect_set_minus_self_empty_shape(left, right)
            || Self::intersect_set_minus_self_empty_shape(right, left)
        {
            return Ok(Some(Self::set_equality_success(
                equal_fact,
                "intersect_set_minus_self_empty",
                Some(SetBuiltinRule::IntersectSetMinusSelfEmpty),
            )));
        }

        // Any subset of the removed set is disjoint from the difference.
        // Example: `A subset C` gives `intersect(A, set_minus(B, C)) = {}`.
        if let Some((subset, removed)) = Self::intersect_set_minus_subset_empty_shape(left, right)
            .or_else(|| Self::intersect_set_minus_subset_empty_shape(right, left))
        {
            let premise: AtomicFact =
                SubsetFact::new(subset, removed, equal_fact.line_file.clone()).into();
            let result =
                self.try_verify_atomic_fact_as_builtin_rule_premise(&premise, builtin_state)?;
            if let Some(result) = result {
                return Ok(Some(Self::set_equality_success_with_subgoals(
                    equal_fact,
                    "intersect_set_minus_disjoint_from_subset",
                    SetBuiltinRule::IntersectSetMinusDisjointFromSubset,
                    vec![result],
                )));
            }
        }

        Ok(None)
    }

    pub(super) fn try_verify_set_minus_equalities(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        // Removing a set from itself leaves the empty set.
        // Example: `set_minus(A, A) = {}`.
        if Self::set_minus_self_empty_shape(left, right)
            || Self::set_minus_self_empty_shape(right, left)
        {
            return Ok(Some(Self::set_equality_success(
                equal_fact,
                "set_minus_self_empty",
                Some(SetBuiltinRule::SetMinusSelfEmpty),
            )));
        }

        // Empty set is a right identity for set-minus.
        // Example: `set_minus(A, {}) = A`.
        if Self::set_minus_empty_right_shape(left, right)
            || Self::set_minus_empty_right_shape(right, left)
        {
            return Ok(Some(Self::set_equality_success(
                equal_fact,
                "set_minus_empty_right",
                Some(SetBuiltinRule::SetMinusEmptyRight),
            )));
        }

        // Removing anything from the empty set leaves it empty.
        // Example: `set_minus({}, A) = {}`.
        if Self::set_minus_empty_left_shape(left, right)
            || Self::set_minus_empty_left_shape(right, left)
        {
            return Ok(Some(Self::set_equality_success(
                equal_fact,
                "set_minus_empty_left",
                Some(SetBuiltinRule::SetMinusEmptyLeft),
            )));
        }

        // Restricting the removed set to the minuend does not change the
        // difference. The inner intersection may use either operand order.
        // Example: `set_minus(B, intersect(A, B)) = set_minus(B, A)`.
        if Self::set_minus_intersect_self_shape(left, right)
            || Self::set_minus_intersect_self_shape(right, left)
        {
            return Ok(Some(Self::set_equality_success(
                equal_fact,
                "set_minus_intersect_self",
                Some(SetBuiltinRule::SetMinusIntersectSelf),
            )));
        }

        // Set-minus distributes over union by De Morgan's law, accepted in either direction.
        // Example: `set_minus(A, union(B, C)) = intersect(set_minus(A, B), set_minus(A, C))`.
        if Self::set_minus_union_de_morgan_shape(left, right)
            || Self::set_minus_union_de_morgan_shape(right, left)
        {
            return Ok(Some(Self::set_equality_success(
                equal_fact,
                "set_minus_union_de_morgan",
                Some(SetBuiltinRule::SetMinusUnionDeMorgan),
            )));
        }

        // Set-minus distributes over intersection by De Morgan's law, accepted in either direction.
        // Example: `set_minus(A, intersect(B, C)) = union(set_minus(A, B), set_minus(A, C))`.
        if Self::set_minus_intersect_de_morgan_shape(left, right)
            || Self::set_minus_intersect_de_morgan_shape(right, left)
        {
            return Ok(Some(Self::set_equality_success(
                equal_fact,
                "set_minus_intersect_de_morgan",
                Some(SetBuiltinRule::SetMinusIntersectDeMorgan),
            )));
        }

        // A subset is recovered by removing its relative complement from the container.
        // Example: `B $subset A` gives `B = set_minus(A, set_minus(A, B))`.
        if let Some((container, subset, rule)) = Self::set_minus_recovers_subset_shape(left, right)
            .map(|(container, subset)| {
                (container, subset, SetBuiltinRule::SubsetEqSetMinusRecovery)
            })
            .or_else(|| {
                Self::set_minus_recovers_subset_shape(right, left).map(|(container, subset)| {
                    (container, subset, SetBuiltinRule::SetMinusRecoverSubset)
                })
            })
        {
            let subset_fact: AtomicFact =
                SubsetFact::new(subset, container, line_file.clone()).into();
            let subset_result =
                self.try_verify_atomic_fact_as_builtin_rule_premise(&subset_fact, builtin_state)?;
            if let Some(subset_result) = subset_result {
                return Ok(Some(Self::set_equality_success_with_subgoals(
                    equal_fact,
                    "set_minus_recovers_subset_from_relative_complement",
                    rule,
                    vec![subset_result],
                )));
            }
        }

        Ok(None)
    }

    pub(super) fn set_equality_success(
        equal_fact: &EqualFact,
        reason: &str,
        evidence: Option<SetBuiltinRule>,
    ) -> ProveFactResult {
        let fact = equal_fact.clone().into();
        match evidence {
            Some(rule) => {
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    fact,
                    reason.to_string(),
                    BuiltinRuleEvidence::Set(rule),
                    Vec::new(),
                )
            }
            None => {
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    fact,
                    reason.to_string(),
                    BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::SetEqualitySuccess),
                    Vec::new(),
                )
            }
        }
        .into()
    }

    pub(super) fn set_equality_success_with_subgoals(
        equal_fact: &EqualFact,
        reason: &str,
        rule: SetBuiltinRule,
        subgoals: Vec<VerifyFactResult>,
    ) -> ProveFactResult {
        SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
            equal_fact.clone().into(),
            reason.to_string(),
            BuiltinRuleEvidence::Set(rule),
            subgoals,
        )
        .into()
    }

    pub(super) fn union_commutative_shape(left: &Obj, right: &Obj) -> bool {
        let (Obj::Union(left_union), Obj::Union(right_union)) = (left, right) else {
            return false;
        };
        objs_match_for_pattern(&left_union.left, &right_union.right)
            && objs_match_for_pattern(&left_union.right, &right_union.left)
    }

    pub(super) fn union_associative_shape(left: &Obj, right: &Obj) -> bool {
        let Obj::Union(left_outer) = left else {
            return false;
        };
        let Obj::Union(left_inner) = left_outer.left.as_ref() else {
            return false;
        };
        let Obj::Union(right_outer) = right else {
            return false;
        };
        let Obj::Union(right_inner) = right_outer.right.as_ref() else {
            return false;
        };
        objs_match_for_pattern(&left_inner.left, &right_outer.left)
            && objs_match_for_pattern(&left_inner.right, &right_inner.left)
            && objs_match_for_pattern(&left_outer.right, &right_inner.right)
    }

    pub(super) fn intersect_commutative_shape(left: &Obj, right: &Obj) -> bool {
        let (Obj::Intersect(left_intersect), Obj::Intersect(right_intersect)) = (left, right)
        else {
            return false;
        };
        objs_match_for_pattern(&left_intersect.left, &right_intersect.right)
            && objs_match_for_pattern(&left_intersect.right, &right_intersect.left)
    }

    pub(super) fn intersect_idempotent_shape(intersection_side: &Obj, retained_side: &Obj) -> bool {
        let Obj::Intersect(intersection) = intersection_side else {
            return false;
        };
        objs_match_for_pattern(&intersection.left, &intersection.right)
            && objs_match_for_pattern(&intersection.left, retained_side)
    }

    pub(super) fn intersect_set_minus_self_empty_shape(
        intersection_side: &Obj,
        empty_side: &Obj,
    ) -> bool {
        let Obj::Intersect(intersection) = intersection_side else {
            return false;
        };
        if !Self::is_empty_list_set(empty_side) {
            return false;
        }
        for (plain, difference) in [
            (intersection.left.as_ref(), intersection.right.as_ref()),
            (intersection.right.as_ref(), intersection.left.as_ref()),
        ] {
            let Obj::SetMinus(difference) = difference else {
                continue;
            };
            if objs_match_for_pattern(plain, difference.right.as_ref()) {
                return true;
            }
        }
        false
    }

    pub(super) fn intersect_set_minus_subset_empty_shape(
        intersection_side: &Obj,
        empty_side: &Obj,
    ) -> Option<(Obj, Obj)> {
        let Obj::Intersect(intersection) = intersection_side else {
            return None;
        };
        if !Self::is_empty_list_set(empty_side) {
            return None;
        }
        for (subset, difference) in [
            (intersection.left.as_ref(), intersection.right.as_ref()),
            (intersection.right.as_ref(), intersection.left.as_ref()),
        ] {
            let Obj::SetMinus(difference) = difference else {
                continue;
            };
            return Some((subset.clone(), difference.right.as_ref().clone()));
        }
        None
    }

    pub(super) fn intersect_associative_shape(left: &Obj, right: &Obj) -> bool {
        let Obj::Intersect(left_outer) = left else {
            return false;
        };
        let Obj::Intersect(left_inner) = left_outer.left.as_ref() else {
            return false;
        };
        let Obj::Intersect(right_outer) = right else {
            return false;
        };
        let Obj::Intersect(right_inner) = right_outer.right.as_ref() else {
            return false;
        };
        objs_match_for_pattern(&left_inner.left, &right_outer.left)
            && objs_match_for_pattern(&left_inner.right, &right_inner.left)
            && objs_match_for_pattern(&left_outer.right, &right_inner.right)
    }

    pub(super) fn intersect_union_distributive_shape(left: &Obj, right: &Obj) -> bool {
        let Obj::Intersect(left_intersect) = left else {
            return false;
        };
        let Obj::Union(left_union) = left_intersect.right.as_ref() else {
            return false;
        };
        let Obj::Union(right_union) = right else {
            return false;
        };
        let Obj::Intersect(right_left_intersect) = right_union.left.as_ref() else {
            return false;
        };
        let Obj::Intersect(right_right_intersect) = right_union.right.as_ref() else {
            return false;
        };
        objs_match_for_pattern(&left_intersect.left, &right_left_intersect.left)
            && objs_match_for_pattern(&left_intersect.left, &right_right_intersect.left)
            && objs_match_for_pattern(&left_union.left, &right_left_intersect.right)
            && objs_match_for_pattern(&left_union.right, &right_right_intersect.right)
    }

    pub(super) fn set_minus_union_de_morgan_shape(left: &Obj, right: &Obj) -> bool {
        let Obj::SetMinus(left_set_minus) = left else {
            return false;
        };
        let Obj::Union(left_union) = left_set_minus.right.as_ref() else {
            return false;
        };
        let Obj::Intersect(right_intersect) = right else {
            return false;
        };
        let Obj::SetMinus(right_left_set_minus) = right_intersect.left.as_ref() else {
            return false;
        };
        let Obj::SetMinus(right_right_set_minus) = right_intersect.right.as_ref() else {
            return false;
        };
        Self::set_minus_de_morgan_args_match(
            left_set_minus,
            left_union.left.as_ref(),
            left_union.right.as_ref(),
            right_left_set_minus,
            right_right_set_minus,
        )
    }

    pub(super) fn set_minus_intersect_de_morgan_shape(left: &Obj, right: &Obj) -> bool {
        let Obj::SetMinus(left_set_minus) = left else {
            return false;
        };
        let Obj::Intersect(left_intersect) = left_set_minus.right.as_ref() else {
            return false;
        };
        let Obj::Union(right_union) = right else {
            return false;
        };
        let Obj::SetMinus(right_left_set_minus) = right_union.left.as_ref() else {
            return false;
        };
        let Obj::SetMinus(right_right_set_minus) = right_union.right.as_ref() else {
            return false;
        };
        Self::set_minus_de_morgan_args_match(
            left_set_minus,
            left_intersect.left.as_ref(),
            left_intersect.right.as_ref(),
            right_left_set_minus,
            right_right_set_minus,
        )
    }

    pub(super) fn set_minus_recovers_subset_shape(
        subset_side: &Obj,
        double_difference_side: &Obj,
    ) -> Option<(Obj, Obj)> {
        let Obj::SetMinus(outer_difference) = double_difference_side else {
            return None;
        };
        let Obj::SetMinus(inner_difference) = outer_difference.right.as_ref() else {
            return None;
        };
        if objs_match_for_pattern(&outer_difference.left, &inner_difference.left)
            && objs_match_for_pattern(subset_side, &inner_difference.right)
        {
            Some((outer_difference.left.as_ref().clone(), subset_side.clone()))
        } else {
            None
        }
    }

    pub(super) fn set_minus_self_empty_shape(difference_side: &Obj, empty_side: &Obj) -> bool {
        let Obj::SetMinus(difference) = difference_side else {
            return false;
        };
        Self::is_empty_list_set(empty_side)
            && objs_match_for_pattern(&difference.left, &difference.right)
    }

    pub(super) fn set_minus_empty_right_shape(difference_side: &Obj, retained_side: &Obj) -> bool {
        let Obj::SetMinus(difference) = difference_side else {
            return false;
        };
        Self::is_empty_list_set(&difference.right)
            && objs_match_for_pattern(&difference.left, retained_side)
    }

    pub(super) fn set_minus_empty_left_shape(difference_side: &Obj, empty_side: &Obj) -> bool {
        let Obj::SetMinus(difference) = difference_side else {
            return false;
        };
        Self::is_empty_list_set(&difference.left) && Self::is_empty_list_set(empty_side)
    }

    pub(super) fn set_minus_intersect_self_shape(restricted_side: &Obj, plain_side: &Obj) -> bool {
        let Obj::SetMinus(restricted) = restricted_side else {
            return false;
        };
        let Obj::Intersect(removed_intersection) = restricted.right.as_ref() else {
            return false;
        };
        let Obj::SetMinus(plain) = plain_side else {
            return false;
        };
        if !objs_match_for_pattern(&restricted.left, &plain.left) {
            return false;
        }
        let retained = restricted.left.as_ref();
        (objs_match_for_pattern(&removed_intersection.left, retained)
            && objs_match_for_pattern(&removed_intersection.right, &plain.right))
            || (objs_match_for_pattern(&removed_intersection.right, retained)
                && objs_match_for_pattern(&removed_intersection.left, &plain.right))
    }

    pub(super) fn set_minus_de_morgan_args_match(
        left_set_minus: &SetMinus,
        first_removed_set: &Obj,
        second_removed_set: &Obj,
        right_left_set_minus: &SetMinus,
        right_right_set_minus: &SetMinus,
    ) -> bool {
        objs_match_for_pattern(&left_set_minus.left, &right_left_set_minus.left)
            && objs_match_for_pattern(&left_set_minus.left, &right_right_set_minus.left)
            && objs_match_for_pattern(first_removed_set, &right_left_set_minus.right)
            && objs_match_for_pattern(second_removed_set, &right_right_set_minus.right)
    }

    pub(super) fn union_idempotent_shape(union_side: &Obj, other_side: &Obj) -> bool {
        let Obj::Union(union) = union_side else {
            return false;
        };
        objs_match_for_pattern(&union.left, &union.right)
            && objs_match_for_pattern(&union.left, other_side)
    }

    pub(super) fn union_set_minus_decomposition_shape(
        decomposed_side: &Obj,
        original_union_side: &Obj,
    ) -> bool {
        let (Obj::Union(decomposed), Obj::Union(original)) = (decomposed_side, original_union_side)
        else {
            return false;
        };
        for (plain, difference) in [
            (decomposed.left.as_ref(), decomposed.right.as_ref()),
            (decomposed.right.as_ref(), decomposed.left.as_ref()),
        ] {
            let Obj::SetMinus(difference) = difference else {
                continue;
            };
            if !objs_match_for_pattern(plain, difference.right.as_ref()) {
                continue;
            }
            let original_matches = (objs_match_for_pattern(&original.left, plain)
                && objs_match_for_pattern(&original.right, difference.left.as_ref()))
                || (objs_match_for_pattern(&original.right, plain)
                    && objs_match_for_pattern(&original.left, difference.left.as_ref()));
            if original_matches {
                return true;
            }
        }
        false
    }

    pub(super) fn union_absorption_shape(
        union_side: &Obj,
        retained_side: &Obj,
    ) -> Option<(Obj, Obj)> {
        let Obj::Union(union) = union_side else {
            return None;
        };
        if objs_match_for_pattern(&union.left, retained_side) {
            return Some((union.right.as_ref().clone(), retained_side.clone()));
        }
        if objs_match_for_pattern(&union.right, retained_side) {
            return Some((union.left.as_ref().clone(), retained_side.clone()));
        }
        None
    }

    pub(super) fn union_empty_identity_rule(
        union_side: &Obj,
        other_side: &Obj,
    ) -> Option<SetBuiltinRule> {
        let Obj::Union(union) = union_side else {
            return None;
        };
        if Self::is_empty_list_set(&union.left) && objs_match_for_pattern(&union.right, other_side)
        {
            Some(SetBuiltinRule::UnionEmptyLeft)
        } else if Self::is_empty_list_set(&union.right)
            && objs_match_for_pattern(&union.left, other_side)
        {
            Some(SetBuiltinRule::UnionEmptyRight)
        } else {
            None
        }
    }

    pub(super) fn is_empty_list_set(obj: &Obj) -> bool {
        matches!(obj, Obj::ListSet(list_set) if list_set.list.is_empty())
    }
}
