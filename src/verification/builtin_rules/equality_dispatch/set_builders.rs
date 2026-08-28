//! General Cartesian, integer-range, and indexed-function set-builder equalities.

use crate::prelude::*;
use crate::verification::verify_equality_by_builtin_rules::{
    factual_equal_success_by_builtin_reason, factual_equal_success_by_builtin_reason_with_subgoals,
    objs_match_for_pattern,
};

impl Runtime {
    pub(super) fn verify_user_prop_subgoal(
        &mut self,
        prop_name: &str,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<StmtResult, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let fact: AtomicFact = NormalAtomicFact::new(
            AtomicName::WithoutMod(prop_name.to_string()),
            vec![left.clone(), right.clone()],
            line_file,
        )
        .into();
        self.verify_atomic_fact_as_builtin_rule_premise(&fact, builtin_state)
    }

    // General Cartesian product definition with a named quantified condition.
    // Example: `general_cart(I, S, g) =
    // {f fn(alpha I)big_union(S): $is_choice_function_for(I, S, g, f)}`.
    pub(super) fn try_verify_general_cart_set_builder_equality(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        for (general_cart_side, set_builder_side) in [(left, right), (right, left)] {
            let Obj::GeneralCart(general_cart) = general_cart_side else {
                continue;
            };
            let Obj::SetBuilder(set_builder) = set_builder_side else {
                continue;
            };
            let Some(steps) = self.general_cart_named_set_builder_canonical_steps(
                general_cart,
                set_builder,
                line_file.clone(),
                builtin_state,
            )?
            else {
                continue;
            };
            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                equal_fact,
                "general_cart equals its named-property set-builder definition",
                steps,
            )));
        }
        Ok(None)
    }

    pub(super) fn general_cart_named_set_builder_canonical_steps(
        &mut self,
        general_cart: &GeneralCart,
        set_builder: &SetBuilder,
        line_file: LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        let Obj::FnSet(fn_set) = set_builder.param_set.as_ref() else {
            return Ok(None);
        };
        if SetBoundParameterGroup::number_of_params(&fn_set.body.set_bound_parameters) != 1
            || !fn_set.body.dom_facts.is_empty()
            || set_builder.facts.len() != 1
        {
            return Ok(None);
        }

        let domain_result = self.verify_equal_fact_as_builtin_premise(
            &EqualFact::new_from_refs(
                fn_set.body.set_bound_parameters[0].set_obj(),
                general_cart.index_set.as_ref(),
                line_file.clone(),
            ),
            builtin_state,
        )?;
        if !domain_result.is_success() {
            return Ok(None);
        }
        let expected_ret_set: Obj = BigUnion::new(general_cart.family_set.as_ref().clone()).into();
        let ret_result = self.verify_equal_fact_as_builtin_premise(
            &EqualFact::new_from_refs(
                fn_set.body.ret_set.as_ref(),
                &expected_ret_set,
                line_file.clone(),
            ),
            builtin_state,
        )?;
        if !ret_result.is_success() {
            return Ok(None);
        }

        let QuantifierFreeFact::AtomicFact(AtomicFact::NormalAtomicFact(choice_fact)) =
            &set_builder.facts[0]
        else {
            return Ok(None);
        };
        if !matches!(
            &choice_fact.predicate,
            AtomicName::WithoutMod(name)
                if name == crate::syntax::keywords::IS_CHOICE_FUNCTION_FOR
        ) {
            return Ok(None);
        }
        let [choice_index, choice_family_set, choice_family_fn, choice_member] =
            choice_fact.body.as_slice()
        else {
            return Ok(None);
        };
        let expected_member = obj_for_bound_param_in_scope(&set_builder.param_binding);
        if !objs_match_for_pattern(choice_member, &expected_member) {
            return Ok(None);
        }

        let mut steps = vec![domain_result, ret_result];
        for (actual, expected) in [
            (choice_index, general_cart.index_set.as_ref()),
            (choice_family_set, general_cart.family_set.as_ref()),
            (choice_family_fn, general_cart.family_fn.as_ref()),
        ] {
            let result = self.verify_equal_fact_as_builtin_premise(
                &EqualFact::new_from_refs(actual, expected, line_file.clone()),
                builtin_state,
            )?;
            if !result.is_success() {
                return Ok(None);
            }
            steps.push(result);
        }
        Ok(Some(steps))
    }

    // Integer ranges are the canonical sets of integer points between their endpoints.
    // Examples: `closed_range(a, b) = {x Z: a <= x <= b}` and
    // `range(a, b) = {x Z: a <= x < b}`.
    pub(super) fn try_verify_integer_range_set_builder_equality(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        for (range_side, set_builder_side) in [(left, right), (right, left)] {
            let (start, end, right_closed) = match range_side {
                Obj::ClosedRange(range) => (range.start.as_ref(), range.end.as_ref(), true),
                Obj::Range(range) => (range.start.as_ref(), range.end.as_ref(), false),
                _ => continue,
            };
            let Obj::SetBuilder(set_builder) = set_builder_side else {
                continue;
            };
            if !matches!(
                set_builder.param_set.as_ref(),
                Obj::StandardSet(StandardSet::Z)
            ) || set_builder.facts.len() != 1
            {
                continue;
            }
            let QuantifierFreeFact::ChainFact(chain) = &set_builder.facts[0] else {
                continue;
            };
            let Ok(chain_facts) = chain.facts() else {
                continue;
            };
            let [AtomicFact::LessEqualFact(lower), upper] = chain_facts.as_slice() else {
                continue;
            };
            let bound_param = obj_for_bound_param_in_scope(&set_builder.param_binding);
            let (upper_left_matches, upper_right_matches) = match (right_closed, upper) {
                (true, AtomicFact::LessEqualFact(fact)) => (
                    objs_match_for_pattern(&fact.left, &bound_param),
                    objs_match_for_pattern(&fact.right, end),
                ),
                (false, AtomicFact::LessFact(fact)) => (
                    objs_match_for_pattern(&fact.left, &bound_param),
                    objs_match_for_pattern(&fact.right, end),
                ),
                _ => (false, false),
            };
            if !objs_match_for_pattern(&lower.left, start)
                || !objs_match_for_pattern(&lower.right, &bound_param)
                || !upper_left_matches
                || !upper_right_matches
            {
                continue;
            }
            let rule = if right_closed {
                "equality: closed_range is its integer set-builder definition"
            } else {
                "equality: range is its integer set-builder definition"
            };
            return Ok(Some(factual_equal_success_by_builtin_reason(
                equal_fact, rule,
            )));
        }
        Ok(None)
    }

    // Sequence-shaped spaces are exactly their corresponding function spaces.
    // Example: `matrix(R, 2, 3) = fn(i, j N+: i <= 2, j <= 3) R`.
    pub(super) fn try_verify_indexed_fn_set_definition_equality(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        for (indexed_set_side, fn_set_side) in [(left, right), (right, left)] {
            let Obj::FnSet(fn_set) = fn_set_side else {
                continue;
            };

            let (expanded, rule) = match indexed_set_side {
                Obj::FiniteSeqSet(finite_seq) => (
                    self.finite_seq_set_to_fn_set(finite_seq, line_file.clone()),
                    "equality: finite_seq is its bounded positive-index function space",
                ),
                Obj::SeqSet(seq) => (
                    self.seq_set_to_fn_set(seq, line_file.clone()),
                    "equality: seq is its positive-index function space",
                ),
                Obj::MatrixSet(matrix) => (
                    self.matrix_set_to_fn_set(matrix, line_file.clone()),
                    "equality: matrix is its bounded positive-index function space",
                ),
                _ => continue,
            };
            let param_count =
                SetBoundParameterGroup::number_of_params(&expanded.body.set_bound_parameters);
            if param_count
                != SetBoundParameterGroup::number_of_params(&fn_set.body.set_bound_parameters)
            {
                continue;
            }
            let alpha_names = (0..param_count)
                .map(|index| format!("#indexed_fn_set_alpha_{index}"))
                .collect::<Vec<_>>();
            let expanded_obj =
                self.fn_set_alpha_renamed_for_display_compare(&expanded.body, &alpha_names)?;
            let explicit_obj =
                self.fn_set_alpha_renamed_for_display_compare(&fn_set.body, &alpha_names)?;
            if objs_match_for_pattern(&expanded_obj, &explicit_obj) {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    equal_fact, rule,
                )));
            }
        }

        Ok(None)
    }
}
