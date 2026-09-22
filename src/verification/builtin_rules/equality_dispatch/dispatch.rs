//! Top-level equality builtin dispatch.

use crate::prelude::*;
use crate::verification::verify_equality_by_builtin_rules::{
    factual_equal_success_by_builtin_reason, objs_match_for_pattern,
};

impl Runtime {
    pub fn verify_equal_fact_by_builtin_rules(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        // A gcd divides each input.
        // Example: `a % gcd(a, b) = 0`.
        if gcd_divides_its_argument_shape(left, right)
            || gcd_divides_its_argument_shape(right, left)
        {
            return Ok(factual_equal_success_by_builtin_reason(
                equal_fact,
                "gcd divides each argument",
            ));
        }
        // A product is divisible by either of its factors.
        // Well-definedness has already established integer operands and a
        // nonzero modulus for the surrounding `%` expression.
        if product_mod_factor_is_zero_shape(left, right)
            || product_mod_factor_is_zero_shape(right, left)
        {
            return Ok(factual_equal_success_by_builtin_reason(
                equal_fact,
                "a product modulo either factor is zero",
            ));
        }
        if let Some(result) = self.try_verify_native_min_max_lattice_equality(equal_fact) {
            return Ok(result);
        }
        if let Some(result) = self.try_verify_native_min_max_equality(equal_fact, builtin_state)? {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_native_rounding_integer_equality(equal_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_native_rounding_algebra_equality(equal_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) = self.try_verify_native_lcm_gcd_product_equality(equal_fact) {
            return Ok(result);
        }
        if let Some(result) = self.try_verify_native_lcm_basic_equality(equal_fact) {
            return Ok(result);
        }
        // Absolute-value identities retain their direct premise certificates.
        // Check them before the broad exp/ln injectivity route can repackage
        // the same equality through an unrelated intermediate equality.
        if let Some(done) = self.try_verify_abs_equalities(equal_fact, builtin_state)? {
            return Ok(done);
        }
        if let Some(result) = self.try_verify_native_exp_ln_identity(equal_fact) {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_native_exp_ln_injectivity(equal_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_native_sign_zero_reflection(equal_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) = self.try_verify_native_exp_ln_algebra(equal_fact) {
            return Ok(result);
        }
        if let Some(result) = self.try_verify_native_sign_value(equal_fact, builtin_state)? {
            return Ok(result);
        }
        if let Some(result) = self.try_verify_native_sign_abs_identity(equal_fact) {
            return Ok(result);
        }
        if let Some(result) = self.try_verify_native_sign_algebra(equal_fact) {
            return Ok(result);
        }
        if let Some(result) = self.try_verify_native_factorial_recurrence(equal_fact) {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_native_factorial_divisibility(equal_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_minus_one_odd_natural_power(equal_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) = self.try_verify_indexed_fn_set_definition_equality(equal_fact)? {
            return Ok(result);
        }
        if let Some(result) = self
            .try_verify_tuple_reconstruction_from_known_cart_membership(equal_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_cart_equality_from_dim_and_projections(equal_fact, builtin_state)?
        {
            return Ok(result);
        }

        // Prefer exact modulo shapes before generic equality rewrites.
        if let Some(done) =
            self.try_verify_mod_nested_same_modulus_absorption(equal_fact, builtin_state)?
        {
            return Ok(done);
        }
        if let Some(done) =
            self.try_verify_mod_nested_divisible_modulus_absorption(equal_fact, builtin_state)?
        {
            return Ok(done);
        }
        if let Some(done) =
            self.try_verify_mod_peel_nested_same_modulus(equal_fact, builtin_state)?
        {
            return Ok(done);
        }
        if let Some(done) =
            self.try_verify_mod_congruence_from_inner_binary(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_native_complex_equality(equal_fact, builtin_state)? {
            return Ok(done);
        }
        if let Some(done) = self.try_verify_trigonometric_equality(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_matrix_power_definition(equal_fact) {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_index_cart_set_builder_equality(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_indexed_set_family_equalities(equal_fact, builtin_state)?
        {
            return Ok(done);
        }
        if let Some(done) =
            self.try_verify_indexed_set_family_algebra_equalities(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_integer_range_set_builder_equality(equal_fact)? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_size_integer_range_equality(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self
            .try_verify_finite_set_size_fn_range_from_known_injection(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_size_from_known_bijection(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self
            .try_verify_zero_equals_subtraction_implies_equal_operands(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self
            .try_verify_zero_equals_product_implies_other_factor_zero(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_square_sum_zero_from_zero_components(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self
            .try_verify_square_sum_component_zero_from_known_sum_zero(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_union_set_equalities(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_intersection_set_equalities(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if Self::intersection_has_literal_set_operand(left) {
            if let Some(done) =
                self.try_verify_literal_set_intersection_filter(equal_fact, true, builtin_state)?
            {
                return Ok(done);
            }
        }
        if Self::intersection_has_literal_set_operand(right) {
            if let Some(done) =
                self.try_verify_literal_set_intersection_filter(equal_fact, false, builtin_state)?
            {
                return Ok(done);
            }
        }

        if let Some(done) = self.try_verify_intersection_from_subset(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_set_minus_equalities(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_size_set_minus_equality(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_size_union_equality(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_size_partition_equality(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_size_set_minus_of_subset_equality(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_cart_finite_set_size_product_equality(equal_fact) {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_power_set_finite_set_size_equality(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_subtraction_from_known_addition(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_equality_from_two_sided_weak_order(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_integer_singleton_interval_equality_builtin_rule(
            equal_fact,
            builtin_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_positive_base_equal_from_equal_nonzero_integer_power(
            equal_fact,
            builtin_state,
        )? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_division_product_conversion(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_zero_equals_pow_from_base_zero(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_pow_one_identity(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_pow_zero_identity(equal_fact)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_one_pow_identity(equal_fact)? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_zero_pow_positive_exponent_identity(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_sqrt_equalities(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_power_addition_exponent_rule(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_power_of_power_rule(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_power_product_rule(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_base_zero_from_known_positive_power_zero(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_abs_power_rule(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_power_inverse_rule(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_pow_reciprocal_exponent_equals_root_by_power(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_log_identity_equalities(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_log_algebra_identities(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_log_reciprocal_rule(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_log_change_of_base_rule(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_log_equals_by_pow_inverse(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_pow_equals_by_known_log_inverse(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_reduce_specialized_aggregate_bridge(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self
            .try_verify_finite_set_reduce_specialized_aggregate_bridge(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_reduce_pointwise_congruence(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_reduce_order_preserving_translation(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_reduce_first_step(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_reduce_adjacent_partition(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_reduce_disjoint_union(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_reduce_bijective_reindexing(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_reduce_empty(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_reduce_literal_expansion(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_reduce_step(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_reduce_empty(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_reduce_list_expansion(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_reduce_closed_range_bridge(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_reduce_fresh_insertion(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_literal_zero_range_sum_is_zero(equal_fact)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_sum_pointwise_congruence(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_sum_additivity(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_sum_subtraction(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_sum_merge_adjacent_ranges(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_sum_single_term(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_sum_split_last_term(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_product_single_term(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_product_split_last_term(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_sum_partition_adjacent_ranges(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_product_partition_adjacent_ranges(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_sum_reindex_shift(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_sum_constant_summand(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_sum_scalar_mul(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_sum_empty(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_sum_list_expansion(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_sum_closed_range_bridge(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_sum_constant_summand(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_sum_pointwise_equality(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_sum_substitution(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_sum_disjoint_union(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_sum_add(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_sum_scalar_mul(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_sum_over_cartesian_product(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_sum_fubini(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_sum_over_bijective_finite_set_enumerations(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_product_empty(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_product_list_expansion(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_product_fresh_insertion(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_product_remove_member(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_product_closed_range_bridge(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_product_constant_factor(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_product_pointwise_equality(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_product_mul(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_product_substitution(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        // A finite set with zero cardinality is empty.
        if let Some(done) = self
            .try_verify_empty_finite_set_from_size_zero(equal_fact, builtin_state.verify_state())?
        {
            return Ok(done);
        }

        // Empty set rule: `S = {}` follows from `not $is_nonempty_set(S)`.
        // This replaces the old common fact `S = {} <=> not $is_nonempty_set(S)`.
        // Example: after `not $is_nonempty_set(S)`, prove `S = {}`.
        if let Some(done) =
            self.try_verify_empty_set_equality_from_not_nonempty(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_zero_mod_equals_zero(equal_fact)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_mod_one_equals_zero(equal_fact)? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_one_mod_equals_one_for_modulus_at_least_two(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_mod_dividend_minus_remainder_equals_zero(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_quot_euclidean_decomposition(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_mod_eq_remainder_from_euclidean_division(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_integer_mod_negation_rule(equal_fact, builtin_state)? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_integer_mod_natural_power_rule(equal_fact, builtin_state)?
        {
            return Ok(done);
        }

        Ok((UnknownGenericStmtResult::new()).into())
    }
}
fn gcd_divides_its_argument_shape(remainder: &Obj, zero: &Obj) -> bool {
    if zero
        .evaluate_to_normalized_decimal_number()
        .is_none_or(|number| number.normalized_value != "0")
    {
        return false;
    }
    let Obj::Mod(modulo) = remainder else {
        return false;
    };
    let Obj::Gcd(gcd) = modulo.right.as_ref() else {
        return false;
    };
    objs_match_for_pattern(&modulo.left, &gcd.left)
        || objs_match_for_pattern(&modulo.left, &gcd.right)
}

fn product_mod_factor_is_zero_shape(remainder: &Obj, zero: &Obj) -> bool {
    if zero
        .evaluate_to_normalized_decimal_number()
        .is_none_or(|number| number.normalized_value != "0")
    {
        return false;
    }
    let Obj::Mod(modulo) = remainder else {
        return false;
    };
    let Obj::Mul(product) = modulo.left.as_ref() else {
        return false;
    };
    objs_match_for_pattern(&modulo.right, &product.left)
        || objs_match_for_pattern(&modulo.right, &product.right)
}
