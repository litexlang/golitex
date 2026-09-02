//! Indexed union and intersection equalities.

use crate::prelude::*;
use crate::verification::verify_equality_by_builtin_rules::{
    factual_equal_success_by_builtin_reason_with_subgoals, objs_match_for_pattern,
};

impl Runtime {
    pub(super) fn try_verify_indexed_set_family_equalities(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        for (indexed_side, other_side) in [
            (&equal_fact.left, &equal_fact.right),
            (&equal_fact.right, &equal_fact.left),
        ] {
            match indexed_side {
                Obj::IndexUnion(index_union) => {
                    if Self::is_empty_list_set(index_union.index_set.as_ref())
                        && Self::is_empty_list_set(other_side)
                    {
                        return Ok(Some(Self::set_equality_success(
                            equal_fact,
                            "index_union_empty_index_is_empty",
                            None,
                        )));
                    }
                    if Self::index_union_domain_union_decomposition_shape(index_union, other_side) {
                        return Ok(Some(Self::set_equality_success(
                            equal_fact,
                            "index_union over a union index domain decomposes into a union",
                            None,
                        )));
                    }
                    if let Obj::BigUnion(big_union) = other_side {
                        if let Obj::FnRange(fn_range) = big_union.left.as_ref() {
                            if objs_match_for_pattern(
                                index_union.family_fn.as_ref(),
                                fn_range.function.as_ref(),
                            ) {
                                return Ok(Some(Self::set_equality_success(
                                    equal_fact,
                                    "index_union agrees with big_union of the family range",
                                    None,
                                )));
                            }
                        }
                    }
                }
                Obj::IndexIntersect(index_intersect) => {
                    if Self::is_empty_list_set(index_intersect.index_set.as_ref())
                        && objs_match_for_pattern(index_intersect.ambient_set.as_ref(), other_side)
                    {
                        return Ok(Some(Self::set_equality_success(
                            equal_fact,
                            "index_intersect_empty_index_is_ambient_set",
                            None,
                        )));
                    }
                    if Self::index_intersect_domain_union_decomposition_shape(
                        index_intersect,
                        other_side,
                    ) {
                        return Ok(Some(Self::set_equality_success(
                            equal_fact,
                            "index_intersect over a union index domain decomposes into an intersection",
                            None,
                        )));
                    }
                    if let Obj::BigIntersect(big_intersect) = other_side {
                        if let Obj::FnRange(fn_range) = big_intersect.left.as_ref() {
                            if !objs_match_for_pattern(
                                index_intersect.family_fn.as_ref(),
                                fn_range.function.as_ref(),
                            ) {
                                continue;
                            }
                            let nonempty_index: AtomicFact = IsNonemptySetFact::new(
                                index_intersect.index_set.as_ref().clone(),
                                equal_fact.line_file.clone(),
                            )
                            .into();
                            let nonempty_result = match index_intersect.index_set.as_ref() {
                                Obj::ListSet(list) if !list.list.is_empty() => {
                                    let proof: ProveFactResult = SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                                        nonempty_index.clone().into(),
                                        "nonempty literal index set".to_string(),
                                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryVerifyIndexedSetFamilyEqualities),
                                        Vec::new(),
                                    )
                                    .into();
                                    self.complete_atomic_fact_proof_result(
                                        &nonempty_index,
                                        proof,
                                        builtin_state.verify_state(),
                                    )?
                                }
                                _ => self.verify_atomic_fact_as_builtin_rule_premise(
                                    &nonempty_index,
                                    builtin_state,
                                )?,
                            };
                            if nonempty_result.is_success() {
                                return Ok(Some(
                                    factual_equal_success_by_builtin_reason_with_subgoals(
                                        equal_fact,
                                        "index_intersect agrees with big_intersect of the family range for a nonempty index set",
                                        vec![nonempty_result],
                                    ),
                                ));
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        Ok(None)
    }

    // Splitting an index domain `I union J` splits the indexed union into the
    // union of the two literal family restrictions. The two result branches
    // may appear in either order because binary union is commutative.
    pub(super) fn index_union_domain_union_decomposition_shape(
        whole: &IndexUnion,
        other_side: &Obj,
    ) -> bool {
        let Obj::Union(index_domain) = whole.index_set.as_ref() else {
            return false;
        };
        let Obj::Union(result_union) = other_side else {
            return false;
        };
        let (Obj::IndexUnion(first_branch), Obj::IndexUnion(second_branch)) =
            (result_union.left.as_ref(), result_union.right.as_ref())
        else {
            return false;
        };

        (Self::index_union_restriction_branch_matches(
            whole,
            index_domain.left.as_ref(),
            first_branch,
        ) && Self::index_union_restriction_branch_matches(
            whole,
            index_domain.right.as_ref(),
            second_branch,
        )) || (Self::index_union_restriction_branch_matches(
            whole,
            index_domain.left.as_ref(),
            second_branch,
        ) && Self::index_union_restriction_branch_matches(
            whole,
            index_domain.right.as_ref(),
            first_branch,
        ))
    }

    pub(super) fn index_union_restriction_branch_matches(
        whole: &IndexUnion,
        expected_index_set: &Obj,
        branch: &IndexUnion,
    ) -> bool {
        objs_match_for_pattern(branch.index_set.as_ref(), expected_index_set)
            && objs_match_for_pattern(branch.ambient_set.as_ref(), whole.ambient_set.as_ref())
            && Self::anonymous_indexed_family_restriction_matches(
                whole.family_fn.as_ref(),
                expected_index_set,
                whole.ambient_set.as_ref(),
                branch.family_fn.as_ref(),
            )
    }

    // The dual law uses intersection on the result side. It is valid without
    // a nonempty premise because `index_intersect` carries an explicit ambient
    // set, including for empty restricted domains.
    pub(super) fn index_intersect_domain_union_decomposition_shape(
        whole: &IndexIntersect,
        other_side: &Obj,
    ) -> bool {
        let Obj::Union(index_domain) = whole.index_set.as_ref() else {
            return false;
        };
        let Obj::Intersect(result_intersection) = other_side else {
            return false;
        };
        let (Obj::IndexIntersect(first_branch), Obj::IndexIntersect(second_branch)) = (
            result_intersection.left.as_ref(),
            result_intersection.right.as_ref(),
        ) else {
            return false;
        };

        (Self::index_intersect_restriction_branch_matches(
            whole,
            index_domain.left.as_ref(),
            first_branch,
        ) && Self::index_intersect_restriction_branch_matches(
            whole,
            index_domain.right.as_ref(),
            second_branch,
        )) || (Self::index_intersect_restriction_branch_matches(
            whole,
            index_domain.left.as_ref(),
            second_branch,
        ) && Self::index_intersect_restriction_branch_matches(
            whole,
            index_domain.right.as_ref(),
            first_branch,
        ))
    }

    pub(super) fn index_intersect_restriction_branch_matches(
        whole: &IndexIntersect,
        expected_index_set: &Obj,
        branch: &IndexIntersect,
    ) -> bool {
        objs_match_for_pattern(branch.index_set.as_ref(), expected_index_set)
            && objs_match_for_pattern(branch.ambient_set.as_ref(), whole.ambient_set.as_ref())
            && Self::anonymous_indexed_family_restriction_matches(
                whole.family_fn.as_ref(),
                expected_index_set,
                whole.ambient_set.as_ref(),
                branch.family_fn.as_ref(),
            )
    }

    // Match exactly `fn(i I) power_set(X) {family(i)}` up to alpha-renaming.
    // In particular, a merely well-typed function with a different body is
    // not accepted as the restriction of `family`.
    pub(in super::super) fn anonymous_indexed_family_restriction_matches(
        original_family: &Obj,
        expected_index_set: &Obj,
        expected_ambient_set: &Obj,
        candidate: &Obj,
    ) -> bool {
        let anonymous = match candidate {
            Obj::AnonymousFn(anonymous) => anonymous,
            Obj::FnObj(function) if function.body.is_empty() => match function.head.as_ref() {
                FnObjHead::AnonymousFnLiteral(anonymous) => anonymous.as_ref(),
                _ => return false,
            },
            _ => return false,
        };
        if !anonymous.body.dom_facts.is_empty()
            || anonymous.body.set_bound_parameters.number_of_params() != 1
            || anonymous.body.set_bound_parameters.len() != 1
        {
            return false;
        }
        let param_group = &anonymous.body.set_bound_parameters.as_slice()[0];
        if !objs_match_for_pattern(param_group.set_obj(), expected_index_set) {
            return false;
        }
        let Obj::PowerSet(return_power_set) = anonymous.body.ret_set.as_ref() else {
            return false;
        };
        if !objs_match_for_pattern(return_power_set.set.as_ref(), expected_ambient_set) {
            return false;
        }

        let Obj::FnObj(application) = anonymous.equal_to.as_ref() else {
            return false;
        };
        if application.body.len() != 1 || application.body[0].len() != 1 {
            return false;
        }
        let application_head: Obj = application.head.as_ref().clone().into();
        if !objs_match_for_pattern(&application_head, original_family) {
            return false;
        }
        let param_bindings = anonymous.body.get_param_bindings();
        let Some(param_binding) = param_bindings.first() else {
            return false;
        };
        let expected_argument = obj_for_bound_param_in_scope(param_binding);
        objs_match_for_pattern(application.body[0][0].as_ref(), &expected_argument)
    }
}
