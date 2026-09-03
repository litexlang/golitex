//! Subset and literal-set intersection equalities.

use crate::prelude::*;
use crate::verification::verify_equality_by_builtin_rules::objs_match_for_pattern;

impl Runtime {
    pub(super) fn intersection_has_literal_set_operand(obj: &Obj) -> bool {
        let Obj::Intersect(intersection) = obj else {
            return false;
        };
        matches!(intersection.left.as_ref(), Obj::ListSet(_))
            || matches!(intersection.right.as_ref(), Obj::ListSet(_))
    }

    // Proves intersection absorption from a known subset fact.
    // Example: from `B $subset A`, prove `intersect(A, B) = B`.
    pub(super) fn try_verify_intersection_from_subset(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        for (intersection_side, target_side) in [
            (&equal_fact.left, &equal_fact.right),
            (&equal_fact.right, &equal_fact.left),
        ] {
            let Obj::Intersect(intersection) = intersection_side else {
                continue;
            };

            let (subset, superset, rule) =
                if objs_match_for_pattern(target_side, &intersection.right) {
                    (
                        &intersection.right,
                        &intersection.left,
                        SetBuiltinRule::IntersectEqRightOfSubset,
                    )
                } else if objs_match_for_pattern(target_side, &intersection.left) {
                    (
                        &intersection.left,
                        &intersection.right,
                        SetBuiltinRule::IntersectEqLeftOfSubset,
                    )
                } else {
                    continue;
                };

            let subset_fact: AtomicFact = SubsetFact::new(
                subset.as_ref().clone(),
                superset.as_ref().clone(),
                equal_fact.line_file.clone(),
            )
            .into();
            let Some(subset_result) =
                self.try_verify_atomic_fact_as_builtin_rule_premise(&subset_fact, builtin_state)?
            else {
                continue;
            };

            return Ok(Some(Self::set_equality_success_with_subgoals(
                equal_fact,
                "intersect_from_subset",
                rule,
                vec![subset_result],
            )));
        }

        Ok(None)
    }

    // Filters a literal set through an intersection using known membership facts.
    // Example: from `x $in S` and `not y $in S`, prove `intersect(S, {x, y}) = {x}`.
    pub(super) fn try_verify_literal_set_intersection_filter(
        &mut self,
        equal_fact: &EqualFact,
        intersection_is_left: bool,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let (intersection_side, target_side) = if intersection_is_left {
            (&equal_fact.left, &equal_fact.right)
        } else {
            (&equal_fact.right, &equal_fact.left)
        };
        let line_file = &equal_fact.line_file;
        let Obj::Intersect(intersection) = intersection_side else {
            return Ok(None);
        };

        let (set, literal_set) = match (intersection.left.as_ref(), intersection.right.as_ref()) {
            (set, Obj::ListSet(literal_set)) => (set, literal_set),
            (Obj::ListSet(literal_set), set) => (set, literal_set),
            _ => return Ok(None),
        };

        let mut kept = Vec::new();
        let mut steps = Vec::new();
        for element in literal_set.list.iter() {
            let element_obj = element.as_ref().clone();
            let in_set: AtomicFact =
                InFact::new(element_obj.clone(), set.clone(), line_file.clone()).into();
            let in_result =
                self.try_verify_atomic_fact_as_builtin_rule_premise(&in_set, builtin_state)?;
            if let Some(in_result) = in_result {
                kept.push(element_obj);
                steps.push(in_result);
                continue;
            }

            let not_in_set: AtomicFact =
                NotInFact::new(element_obj, set.clone(), line_file.clone()).into();
            let not_in_result =
                self.try_verify_atomic_fact_as_builtin_rule_premise(&not_in_set, builtin_state)?;
            if let Some(not_in_result) = not_in_result {
                steps.push(not_in_result);
                continue;
            }

            return Ok(None);
        }

        let filtered_set: Obj = ListSet::new(kept).into();
        if !objs_match_for_pattern(&filtered_set, target_side) {
            return Ok(None);
        }

        Ok(Some(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                equal_fact.clone().into(),
                "intersect_literal_set_filter".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyLiteralSetIntersectionFilter,
                ),
                steps,
            )
            .into(),
        ))
    }
}
