use crate::prelude::*;
use crate::verify::verify_equality_by_builtin_rules::{
    factual_equal_success_by_builtin_reason, factual_equal_success_by_builtin_reason_with_subgoals,
    objs_match_for_pattern,
};
use std::rc::Rc;

impl Runtime {
    pub fn verify_equal_fact_by_builtin_rules(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
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
        if let Some(result) = self.try_verify_native_min_max_equality(equal_fact, builtin_state)? {
            return Ok(result);
        }
        if let Some(result) = self.try_verify_native_min_max_lattice_equality(equal_fact) {
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
        if let Some(result) =
            self.try_verify_tuple_reconstruction_from_known_cart_membership(equal_fact)?
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
        if let Some(done) = self.try_verify_trigonometric_equality(equal_fact)? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_matrix_power_definition(equal_fact) {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_general_cart_set_builder_equality(equal_fact, builtin_state)?
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

        if let Some(done) = self.try_verify_union_set_equalities(equal_fact) {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_intersection_set_equalities(equal_fact) {
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

        if let Some(done) =
            self.try_verify_equality_from_known_antisymmetric_props(equal_fact, builtin_state)?
        {
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
        if let Some(done) = self.try_verify_empty_finite_set_from_size_zero(equal_fact)? {
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

        Ok((StmtUnknown::new()).into())
    }

    // A member of a literal Cartesian product is the tuple of its own
    // coordinates. This is intentionally narrower than general tuple
    // extensionality: it uses one exact known cart-membership fact and only
    // accepts the canonical projection list `(p[1], ..., p[n])`.
    fn try_verify_tuple_reconstruction_from_known_cart_membership(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let (target, tuple) = match (left, right) {
            (target, Obj::Tuple(tuple)) if !matches!(target, Obj::Tuple(_)) => (target, tuple),
            (Obj::Tuple(tuple), target) if !matches!(target, Obj::Tuple(_)) => (target, tuple),
            _ => return Ok(None),
        };

        for (index, component) in tuple.args.iter().enumerate() {
            let expected: Obj =
                ObjAtIndex::new(target.clone(), Number::new((index + 1).to_string()).into()).into();
            if !objs_match_for_pattern(component.as_ref(), &expected) {
                return Ok(None);
            }
        }

        for owner_set in self.known_sets_containing_obj(target) {
            let Obj::Cart(cart) = &owner_set else {
                continue;
            };
            if cart.args.len() != tuple.args.len() {
                continue;
            }
            let membership: AtomicFact =
                InFact::new(target.clone(), owner_set, line_file.clone()).into();
            let membership_result =
                self.verify_non_equational_atomic_fact_with_known_atomic_facts(&membership)?;
            if !membership_result.is_true() {
                continue;
            }
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    equal_fact.clone().into(),
                    "tuple reconstruction from known Cartesian-product membership".to_string(),
                    vec![membership_result],
                )
                .into(),
            ));
        }

        Ok(None)
    }

    fn try_verify_union_set_equalities(&self, equal_fact: &EqualFact) -> Option<StmtResult> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        // Union commutativity for sets.
        // Example: `union(A, B) = union(B, A)`.
        if Self::union_commutative_shape(left, right) {
            return Some(Self::set_equality_success(
                equal_fact,
                "union_commutative",
                Some(SetBuiltinRule::UnionCommutative),
            ));
        }

        // Union associativity for sets, accepted in either equality direction.
        // Example: `union(union(A, B), C) = union(A, union(B, C))`.
        if Self::union_associative_shape(left, right) || Self::union_associative_shape(right, left)
        {
            return Some(Self::set_equality_success(
                equal_fact,
                "union_associative",
                Some(SetBuiltinRule::UnionAssociative),
            ));
        }

        // Union idempotence for sets, accepted in either equality direction.
        // Example: `union(A, A) = A`.
        if Self::union_idempotent_shape(left, right) || Self::union_idempotent_shape(right, left) {
            return Some(Self::set_equality_success(
                equal_fact,
                "union_idempotent",
                Some(SetBuiltinRule::UnionIdempotent),
            ));
        }

        // Empty set is a two-sided identity for union, accepted in either equality direction.
        // Example: `union(A, {}) = A` and `union({}, A) = A`.
        if Self::union_empty_identity_shape(left, right)
            || Self::union_empty_identity_shape(right, left)
        {
            return Some(Self::set_equality_success(
                equal_fact,
                "union_empty_identity",
                Some(SetBuiltinRule::UnionEmptyIdentity),
            ));
        }

        None
    }

    fn try_verify_intersection_set_equalities(&self, equal_fact: &EqualFact) -> Option<StmtResult> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        // Intersection commutativity for sets.
        // Example: `intersect(A, B) = intersect(B, A)`.
        if Self::intersect_commutative_shape(left, right) {
            return Some(Self::set_equality_success(
                equal_fact,
                "intersect_commutative",
                Some(SetBuiltinRule::IntersectCommutative),
            ));
        }

        // Intersection associativity for sets, accepted in either equality direction.
        // Example: `intersect(intersect(A, B), C) = intersect(A, intersect(B, C))`.
        if Self::intersect_associative_shape(left, right)
            || Self::intersect_associative_shape(right, left)
        {
            return Some(Self::set_equality_success(
                equal_fact,
                "intersect_associative",
                Some(SetBuiltinRule::IntersectAssociative),
            ));
        }

        // Intersection distributes over union for sets, accepted in either equality direction.
        // Example: `intersect(A, union(B, C)) = union(intersect(A, B), intersect(A, C))`.
        if Self::intersect_union_distributive_shape(left, right)
            || Self::intersect_union_distributive_shape(right, left)
        {
            return Some(Self::set_equality_success(
                equal_fact,
                "intersect_union_distributive",
                None,
            ));
        }

        None
    }

    fn try_verify_set_minus_equalities(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        // Set-minus distributes over union by De Morgan's law, accepted in either direction.
        // Example: `set_minus(A, union(B, C)) = intersect(set_minus(A, B), set_minus(A, C))`.
        if Self::set_minus_union_de_morgan_shape(left, right)
            || Self::set_minus_union_de_morgan_shape(right, left)
        {
            return Ok(Some(Self::set_equality_success(
                equal_fact,
                "set_minus_union_de_morgan",
                None,
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
                None,
            )));
        }

        // A subset is recovered by removing its relative complement from the container.
        // Example: `B $subset A` gives `B = set_minus(A, set_minus(A, B))`.
        if let Some((container, subset)) = Self::set_minus_recovers_subset_shape(left, right)
            .or_else(|| Self::set_minus_recovers_subset_shape(right, left))
        {
            let subset_fact: AtomicFact =
                SubsetFact::new(subset, container, line_file.clone()).into();
            let subset_result =
                self.verify_atomic_fact_as_builtin_rule_premise(&subset_fact, builtin_state)?;
            if subset_result.is_true() {
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        equal_fact.clone().into(),
                        "set_minus_recovers_subset_from_relative_complement".to_string(),
                        vec![subset_result],
                    )
                    .into(),
                ));
            }
        }

        Ok(None)
    }

    fn try_verify_cart_finite_set_size_product_equality(
        &self,
        equal_fact: &EqualFact,
    ) -> Option<StmtResult> {
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

    fn try_verify_finite_set_size_set_minus_equality(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
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

        let first_finite: AtomicFact = IsFiniteSetFact::new(first_set, line_file.clone()).into();
        let first_result =
            self.verify_atomic_fact_as_builtin_rule_premise(&first_finite, builtin_state)?;
        if !first_result.is_true() {
            return Ok(None);
        }

        let second_finite: AtomicFact = IsFiniteSetFact::new(second_set, line_file.clone()).into();
        let second_result =
            self.verify_atomic_fact_as_builtin_rule_premise(&second_finite, builtin_state)?;
        if !second_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                equal_fact.clone().into(),
                "finite_set_size_set_minus".to_string(),
                vec![first_result, second_result],
            )
            .into(),
        ))
    }

    // Inclusion-exclusion counts the union of two finite sets.
    // Example: `finite_set_size(union(A, B)) = finite_set_size(A) + finite_set_size(B) - finite_set_size(intersect(A, B))`.
    fn try_verify_finite_set_size_union_equality(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
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
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                equal_fact.clone().into(),
                "finite_set_size_union_inclusion_exclusion".to_string(),
                step_results,
            )
            .into(),
        ))
    }

    // A finite set partitions into its overlap with another set and the remainder.
    // Example: `finite_set_size(A) = finite_set_size(intersect(A, B)) + finite_set_size(set_minus(A, B))`.
    fn try_verify_finite_set_size_partition_equality(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
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
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                equal_fact.clone().into(),
                "finite_set_size_partition_by_intersection_and_difference".to_string(),
                step_results,
            )
            .into(),
        ))
    }

    // Removing a finite subset subtracts exactly that subset's cardinality.
    // Example: `B $subset A` gives `finite_set_size(set_minus(A, B)) = finite_set_size(A) - finite_set_size(B)`.
    fn try_verify_finite_set_size_set_minus_of_subset_equality(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let Some((container, subset)) =
            Self::finite_set_size_set_minus_of_subset_shape(left, right)
                .or_else(|| Self::finite_set_size_set_minus_of_subset_shape(right, left))
        else {
            return Ok(None);
        };

        let subset_fact: AtomicFact =
            SubsetFact::new(subset.clone(), container.clone(), line_file.clone()).into();
        let subset_result =
            self.verify_atomic_fact_as_builtin_rule_premise(&subset_fact, builtin_state)?;
        if !subset_result.is_true() {
            return Ok(None);
        }
        let container_finite: AtomicFact =
            IsFiniteSetFact::new(container, line_file.clone()).into();
        let container_result =
            self.verify_atomic_fact_as_builtin_rule_premise(&container_finite, builtin_state)?;
        if !container_result.is_true() {
            return Ok(None);
        }
        let subset_finite: AtomicFact = IsFiniteSetFact::new(subset, line_file.clone()).into();
        let subset_finite_result =
            self.verify_atomic_fact_as_builtin_rule_premise(&subset_finite, builtin_state)?;
        if !subset_finite_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                equal_fact.clone().into(),
                "finite_set_size_set_minus_finite_subset".to_string(),
                vec![subset_result, container_result, subset_finite_result],
            )
            .into(),
        ))
    }

    // Integer interval cardinalities are determined by their natural endpoints.
    // Examples: `finite_set_size(closed_range(a, b)) = b - a + 1` and
    // `finite_set_size(range(a, b)) = b - a` when `a <= b` and both endpoints are natural.
    fn try_verify_finite_set_size_integer_range_equality(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let Some((start, end, closed)) = Self::finite_set_size_integer_range_shape(left, right)
            .or_else(|| Self::finite_set_size_integer_range_shape(right, left))
        else {
            return Ok(None);
        };

        let start_in_n: AtomicFact =
            InFact::new(start.clone(), StandardSet::N.into(), line_file.clone()).into();
        let start_result =
            self.verify_atomic_fact_as_builtin_rule_premise(&start_in_n, builtin_state)?;
        if !start_result.is_true() {
            return Ok(None);
        }

        let end_in_n: AtomicFact =
            InFact::new(end.clone(), StandardSet::N.into(), line_file.clone()).into();
        let end_result =
            self.verify_atomic_fact_as_builtin_rule_premise(&end_in_n, builtin_state)?;
        if !end_result.is_true() {
            return Ok(None);
        }

        let endpoints_ordered: AtomicFact =
            LessEqualFact::new(start, end, line_file.clone()).into();
        let order_result =
            self.verify_atomic_fact_as_builtin_rule_premise(&endpoints_ordered, builtin_state)?;
        if !order_result.is_true() {
            return Ok(None);
        }

        let rule = if closed {
            "finite_set_size_closed_range"
        } else {
            "finite_set_size_range"
        };
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                equal_fact.clone().into(),
                rule.to_string(),
                vec![start_result, end_result, order_result],
            )
            .into(),
        ))
    }

    fn try_verify_power_set_finite_set_size_equality(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
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

        let base_finite: AtomicFact = IsFiniteSetFact::new(base_set, line_file.clone()).into();
        let base_result =
            self.verify_atomic_fact_as_builtin_rule_premise(&base_finite, builtin_state)?;
        if !base_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                equal_fact.clone().into(),
                "power_set_finite_set_size_two_pow_finite_set_size_base".to_string(),
                vec![base_result],
            )
            .into(),
        ))
    }

    fn set_equality_success(
        equal_fact: &EqualFact,
        reason: &str,
        evidence: Option<SetBuiltinRule>,
    ) -> StmtResult {
        let fact = equal_fact.clone().into();
        match evidence {
            Some(rule) => {
                FactualStmtSuccess::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    fact,
                    reason.to_string(),
                    BuiltinRuleEvidence::Set(rule),
                    Vec::new(),
                )
            }
            None => FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                fact,
                reason.to_string(),
                Vec::new(),
            ),
        }
        .into()
    }

    fn union_commutative_shape(left: &Obj, right: &Obj) -> bool {
        let (Obj::Union(left_union), Obj::Union(right_union)) = (left, right) else {
            return false;
        };
        objs_match_for_pattern(&left_union.left, &right_union.right)
            && objs_match_for_pattern(&left_union.right, &right_union.left)
    }

    fn union_associative_shape(left: &Obj, right: &Obj) -> bool {
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

    fn intersect_commutative_shape(left: &Obj, right: &Obj) -> bool {
        let (Obj::Intersect(left_intersect), Obj::Intersect(right_intersect)) = (left, right)
        else {
            return false;
        };
        objs_match_for_pattern(&left_intersect.left, &right_intersect.right)
            && objs_match_for_pattern(&left_intersect.right, &right_intersect.left)
    }

    fn intersect_associative_shape(left: &Obj, right: &Obj) -> bool {
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

    fn intersect_union_distributive_shape(left: &Obj, right: &Obj) -> bool {
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

    fn set_minus_union_de_morgan_shape(left: &Obj, right: &Obj) -> bool {
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

    fn set_minus_intersect_de_morgan_shape(left: &Obj, right: &Obj) -> bool {
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

    fn set_minus_recovers_subset_shape(
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

    fn set_minus_de_morgan_args_match(
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

    fn cart_finite_set_size_product_shape(finite_set_size_side: &Obj, product_side: &Obj) -> bool {
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

    fn finite_set_size_set_minus_shape(
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

    fn finite_set_size_union_shape(
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

    fn finite_set_size_partition_shape(
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

    fn finite_set_size_set_minus_of_subset_shape(
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

    fn verify_two_sets_are_finite(
        &mut self,
        first_set: Obj,
        second_set: Obj,
        line_file: LineFile,
        _builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        let type_state = UseContextVerifyState::new(0, true);
        let first_finite: AtomicFact = IsFiniteSetFact::new(first_set, line_file.clone()).into();
        let first_result = self.verify_atomic_fact(&first_finite, &type_state)?;
        if !first_result.is_true() {
            return Ok(None);
        }
        let second_finite: AtomicFact = IsFiniteSetFact::new(second_set, line_file).into();
        let second_result = self.verify_atomic_fact(&second_finite, &type_state)?;
        if !second_result.is_true() {
            return Ok(None);
        }
        Ok(Some(vec![first_result, second_result]))
    }

    fn finite_set_size_integer_range_shape(
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

    fn power_set_finite_set_size_shape(finite_set_size_side: &Obj, pow_side: &Obj) -> Option<Obj> {
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

    fn count_product_for_cart_args(args: &[Box<Obj>]) -> Option<Obj> {
        let mut iter = args.iter();
        let first = iter.next()?;
        let mut product: Obj = FiniteSetSize::new(first.as_ref().clone()).into();
        for arg in iter {
            let factor_finite_set_size: Obj = FiniteSetSize::new(arg.as_ref().clone()).into();
            product = Mul::new(product, factor_finite_set_size).into();
        }
        Some(product)
    }

    fn union_idempotent_shape(union_side: &Obj, other_side: &Obj) -> bool {
        let Obj::Union(union) = union_side else {
            return false;
        };
        objs_match_for_pattern(&union.left, &union.right)
            && objs_match_for_pattern(&union.left, other_side)
    }

    fn union_empty_identity_shape(union_side: &Obj, other_side: &Obj) -> bool {
        let Obj::Union(union) = union_side else {
            return false;
        };
        (Self::is_empty_list_set(&union.left) && objs_match_for_pattern(&union.right, other_side))
            || (Self::is_empty_list_set(&union.right)
                && objs_match_for_pattern(&union.left, other_side))
    }

    fn is_empty_list_set(obj: &Obj) -> bool {
        matches!(obj, Obj::ListSet(list_set) if list_set.list.is_empty())
    }

    fn intersection_has_literal_set_operand(obj: &Obj) -> bool {
        let Obj::Intersect(intersection) = obj else {
            return false;
        };
        matches!(intersection.left.as_ref(), Obj::ListSet(_))
            || matches!(intersection.right.as_ref(), Obj::ListSet(_))
    }

    // Proves intersection absorption from a known subset fact.
    // Example: from `B $subset A`, prove `intersect(A, B) = B`.
    fn try_verify_intersection_from_subset(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (intersection_side, target_side) in [
            (&equal_fact.left, &equal_fact.right),
            (&equal_fact.right, &equal_fact.left),
        ] {
            let Obj::Intersect(intersection) = intersection_side else {
                continue;
            };

            let (subset, superset) = if objs_match_for_pattern(target_side, &intersection.right) {
                (&intersection.right, &intersection.left)
            } else if objs_match_for_pattern(target_side, &intersection.left) {
                (&intersection.left, &intersection.right)
            } else {
                continue;
            };

            let subset_fact: AtomicFact = SubsetFact::new(
                subset.as_ref().clone(),
                superset.as_ref().clone(),
                equal_fact.line_file.clone(),
            )
            .into();
            let subset_result =
                self.verify_atomic_fact_as_builtin_rule_premise(&subset_fact, builtin_state)?;
            if !subset_result.is_true() {
                continue;
            }

            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    equal_fact.clone().into(),
                    "intersect_from_subset".to_string(),
                    vec![subset_result],
                )
                .into(),
            ));
        }

        Ok(None)
    }

    // Filters a literal set through an intersection using known membership facts.
    // Example: from `x $in S` and `not y $in S`, prove `intersect(S, {x, y}) = {x}`.
    fn try_verify_literal_set_intersection_filter(
        &mut self,
        equal_fact: &EqualFact,
        intersection_is_left: bool,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
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
                self.verify_atomic_fact_as_builtin_rule_premise(&in_set, builtin_state)?;
            if in_result.is_true() {
                kept.push(element_obj);
                steps.push(in_result);
                continue;
            }

            let not_in_set: AtomicFact =
                NotInFact::new(element_obj, set.clone(), line_file.clone()).into();
            let not_in_result =
                self.verify_atomic_fact_as_builtin_rule_premise(&not_in_set, builtin_state)?;
            if not_in_result.is_true() {
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
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                equal_fact.clone().into(),
                "intersect_literal_set_filter".to_string(),
                steps,
            )
            .into(),
        ))
    }

    fn try_verify_subtraction_from_known_addition(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(done) =
            self.try_verify_one_subtraction_from_known_addition(equal_fact, true, builtin_state)?
        {
            return Ok(Some(done));
        }
        self.try_verify_one_subtraction_from_known_addition(equal_fact, false, builtin_state)
    }

    // Moves one addend across a known sum equality.
    // Example: from a known `a + b = c` or `b + a = c`, prove `a = c - b`.
    fn try_verify_one_subtraction_from_known_addition(
        &mut self,
        equal_fact: &EqualFact,
        target_is_left: bool,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (target_a, subtraction_side) = if target_is_left {
            (&equal_fact.left, &equal_fact.right)
        } else {
            (&equal_fact.right, &equal_fact.left)
        };
        let line_file = &equal_fact.line_file;
        let Obj::Sub(subtraction) = subtraction_side else {
            return Ok(None);
        };

        let candidate_sum_1: Obj =
            Add::new(target_a.clone(), subtraction.right.as_ref().clone()).into();
        let sum_fact_1 = EqualFact::new_from_refs(
            &candidate_sum_1,
            subtraction.left.as_ref(),
            line_file.clone(),
        );
        let known_sum_1 = self.verify_equal_fact_by_known_equality(&sum_fact_1);
        if known_sum_1.is_true() {
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    equal_fact.clone().into(),
                    "equality: a = c - b from known a + b = c".to_string(),
                    vec![known_sum_1],
                )
                .into(),
            ));
        }

        let candidate_sum_2: Obj =
            Add::new(subtraction.right.as_ref().clone(), target_a.clone()).into();
        let sum_fact_2 = EqualFact::new_from_refs(
            &candidate_sum_2,
            subtraction.left.as_ref(),
            line_file.clone(),
        );
        let known_sum_2 = self.verify_equal_fact_by_known_equality(&sum_fact_2);
        if known_sum_2.is_true() {
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    equal_fact.clone().into(),
                    "equality: a = c - b from known b + a = c".to_string(),
                    vec![known_sum_2],
                )
                .into(),
            ));
        }

        let premise_result = self.verify_builtin_rule_premise_alternatives(
            vec![vec![sum_fact_1.into()], vec![sum_fact_2.into()]],
            line_file.clone(),
            builtin_state,
        )?;
        if premise_result.is_true() {
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    equal_fact.clone().into(),
                    "equality: subtraction from complete addition-order disjunction".to_string(),
                    vec![premise_result],
                )
                .into(),
            ));
        }

        Ok(None)
    }

    // Tuple extensionality: a tuple is equal to `(a, b, ...)` when its dimension matches
    // and each projection matches the corresponding component.
    // Example: from `tuple_dim(t) = 2`, `t[1] = a`, and `t[2] = b`, prove `t = (a, b)`.
    pub(crate) fn try_verify_tuple_equality_from_dim_and_projections(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let (tuple_obj, target_obj) = match (left, right) {
            (target_obj, Obj::Tuple(tuple_obj)) => (tuple_obj, target_obj),
            (Obj::Tuple(tuple_obj), target_obj) => (tuple_obj, target_obj),
            _ => return Ok(None),
        };

        if matches!(target_obj, Obj::Tuple(_)) {
            return Ok(None);
        }

        let is_tuple_fact: AtomicFact =
            IsTupleFact::new(target_obj.clone(), line_file.clone()).into();
        let is_tuple_result = self.verify_atomic_fact(&is_tuple_fact, verify_state)?;
        if !is_tuple_result.is_true() {
            return Ok(None);
        }

        let tuple_dim_obj: Obj = TupleDim::new(target_obj.clone()).into();
        let tuple_dim_value_obj: Obj = Number::new(tuple_obj.args.len().to_string()).into();
        let tuple_dim_fact: AtomicFact =
            EqualFact::new(tuple_dim_obj, tuple_dim_value_obj, line_file.clone()).into();
        let tuple_dim_result = self.verify_atomic_fact(&tuple_dim_fact, verify_state)?;
        if !tuple_dim_result.is_true() {
            return Ok(None);
        }

        let mut steps = vec![is_tuple_result, tuple_dim_result];
        for (index, arg) in tuple_obj.args.iter().enumerate() {
            let index_obj: Obj = Number::new((index + 1).to_string()).into();
            let projected_obj: Obj = ObjAtIndex::new(target_obj.clone(), index_obj).into();
            let component_fact: AtomicFact =
                EqualFact::new(projected_obj, arg.as_ref().clone(), line_file.clone()).into();
            let component_result = self.verify_atomic_fact(&component_fact, verify_state)?;
            if !component_result.is_true() {
                return Ok(None);
            }
            steps.push(component_result);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                equal_fact.clone().into(),
                "tuple equality from dimension and projections".to_string(),
                steps,
            )
            .into(),
        ))
    }

    // Tuple extensionality for symbolic dimensions: equal tuples have equal
    // coordinates on their common index range. Example: `tuple_dim(p) = n`,
    // `tuple_dim(q) = n`, and `forall i closed_range(1, n): p[i] = q[i]`
    // prove `p = q`.
    pub(crate) fn try_verify_symbolic_tuple_equality_from_coordinates(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let left_is_direct_symbol = matches!(
            left,
            Obj::Atom(
                AtomObj::Identifier(_)
                    | AtomObj::IdentifierWithMod(_)
                    | AtomObj::Forall(_)
                    | AtomObj::Exist(_)
                    | AtomObj::Def(_)
                    | AtomObj::SetBuilder(_)
                    | AtomObj::FnSet(_)
                    | AtomObj::Induc(_)
                    | AtomObj::DefAlgo(_)
            )
        );
        let right_is_direct_symbol = matches!(
            right,
            Obj::Atom(
                AtomObj::Identifier(_)
                    | AtomObj::IdentifierWithMod(_)
                    | AtomObj::Forall(_)
                    | AtomObj::Exist(_)
                    | AtomObj::Def(_)
                    | AtomObj::SetBuilder(_)
                    | AtomObj::FnSet(_)
                    | AtomObj::Induc(_)
                    | AtomObj::DefAlgo(_)
            )
        );
        if !left_is_direct_symbol || !right_is_direct_symbol {
            return Ok(None);
        }

        let left_is_tuple: AtomicFact = IsTupleFact::new(left.clone(), line_file.clone()).into();
        let left_is_tuple_result = self.verify_atomic_fact(&left_is_tuple, verify_state)?;
        if !left_is_tuple_result.is_true() {
            return Ok(None);
        }

        let right_is_tuple: AtomicFact = IsTupleFact::new(right.clone(), line_file.clone()).into();
        let right_is_tuple_result = self.verify_atomic_fact(&right_is_tuple, verify_state)?;
        if !right_is_tuple_result.is_true() {
            return Ok(None);
        }

        let left_dim: Obj = TupleDim::new(left.clone()).into();
        let right_dim: Obj = TupleDim::new(right.clone()).into();
        let same_dim: AtomicFact =
            EqualFact::new(left_dim.clone(), right_dim, line_file.clone()).into();
        let same_dim_result = self.verify_atomic_fact(&same_dim, verify_state)?;
        if !same_dim_result.is_true() {
            return Ok(None);
        }

        let dimension_is_positive: AtomicFact = LessEqualFact::new(
            Number::new("1".to_string()).into(),
            left_dim.clone(),
            line_file.clone(),
        )
        .into();
        let dimension_is_positive_result =
            self.verify_atomic_fact(&dimension_is_positive, verify_state)?;
        if !dimension_is_positive_result.is_true() {
            return Ok(None);
        }

        let index_name = self.generate_random_unused_name();
        let coordinate_group = self.fresh_param_group_with_type(
            vec![index_name],
            ParamType::Obj(ClosedRange::new(Number::new("1".to_string()).into(), left_dim).into()),
        )?;
        let index_obj =
            obj_for_bound_param_in_scope(&coordinate_group.params[0], ParamObjType::Forall);
        let coordinate_equality: AtomicFact = EqualFact::new(
            ObjAtIndex::new(left.clone(), index_obj.clone()).into(),
            ObjAtIndex::new(right.clone(), index_obj).into(),
            line_file.clone(),
        )
        .into();
        let coordinate_params = ParamDefWithType::new(vec![coordinate_group]);
        let coordinate_result = self.run_in_local_env(|rt| {
            rt.define_params_with_type(&coordinate_params, false, ParamObjType::Forall)?;
            rt.verify_atomic_fact_with_known_forall(&coordinate_equality, verify_state)
        })?;
        if !coordinate_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                equal_fact.clone().into(),
                "tuple equality from symbolic dimension and coordinates".to_string(),
                vec![
                    left_is_tuple_result,
                    right_is_tuple_result,
                    same_dim_result,
                    dimension_is_positive_result,
                    coordinate_result,
                ],
            )
            .into(),
        ))
    }

    // Cart extensionality: a cart object is equal to `cart(A, B, ...)` when it is a cart,
    // its dimension matches, and each factor projection matches the corresponding literal cart
    // factor.
    // Example: from `$is_cart(c)`, `cart_dim(c) = 3`, and `proj(c, i) = R`, prove
    // `c = cart(R, R, R)`.
    fn try_verify_cart_equality_from_dim_and_projections(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let (cart_obj, target_obj) = match (left, right) {
            (target_obj, Obj::Cart(cart_obj)) => (cart_obj, target_obj),
            (Obj::Cart(cart_obj), target_obj) => (cart_obj, target_obj),
            _ => return Ok(None),
        };

        if matches!(target_obj, Obj::Cart(_)) {
            return Ok(None);
        }

        let is_cart_fact: AtomicFact =
            IsCartFact::new(target_obj.clone(), line_file.clone()).into();
        let cart_dim_obj: Obj = CartDim::new(target_obj.clone()).into();
        let cart_dim_value_obj: Obj = Number::new(cart_obj.args.len().to_string()).into();
        let cart_dim_fact: AtomicFact =
            EqualFact::new(cart_dim_obj, cart_dim_value_obj, line_file.clone()).into();
        let mut complete_premises = vec![is_cart_fact.clone(), cart_dim_fact.clone()];
        for (index, arg) in cart_obj.args.iter().enumerate() {
            let index_obj: Obj = Number::new((index + 1).to_string()).into();
            complete_premises.push(
                EqualFact::new(
                    Proj::new(target_obj.clone(), index_obj).into(),
                    arg.as_ref().clone(),
                    line_file.clone(),
                )
                .into(),
            );
        }
        if let Some(steps) = self.verify_builtin_rule_premises(&complete_premises, builtin_state)? {
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    equal_fact.clone().into(),
                    "cart equality from dimension and projections".to_string(),
                    steps,
                )
                .into(),
            ));
        }

        let is_cart_result =
            self.verify_atomic_fact_as_builtin_rule_premise(&is_cart_fact, builtin_state)?;
        if !is_cart_result.is_true() {
            return Ok(None);
        }

        let cart_dim_result =
            self.verify_atomic_fact_as_builtin_rule_premise(&cart_dim_fact, builtin_state)?;
        if !cart_dim_result.is_true() {
            return Ok(None);
        }

        let mut steps = vec![is_cart_result, cart_dim_result];
        for (index, arg) in cart_obj.args.iter().enumerate() {
            let index_obj: Obj = Number::new((index + 1).to_string()).into();
            let projected_target: Obj = Proj::new(target_obj.clone(), index_obj).into();
            let projection_fact: AtomicFact =
                EqualFact::new(projected_target, arg.as_ref().clone(), line_file.clone()).into();
            let mut projection_result =
                self.verify_atomic_fact_as_builtin_rule_premise(&projection_fact, builtin_state)?;
            if !projection_result.is_true() {
                if let Some(known_forall_result) =
                    self.verify_exact_cart_projection_from_known_forall(&projection_fact)?
                {
                    projection_result = known_forall_result;
                }
            }
            if !projection_result.is_true() {
                return Ok(None);
            }
            steps.push(projection_result);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                equal_fact.clone().into(),
                "cart equality from dimension and projections".to_string(),
                steps,
            )
            .into(),
        ))
    }

    fn verify_exact_cart_projection_from_known_forall(
        &mut self,
        goal: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let lookup_key = (goal.key(), goal.is_true());
        let candidates: Vec<(AtomicFact, Rc<KnownForallFactParamsAndDom>)> = self
            .iter_environments_from_top()
            .flat_map(|environment| {
                environment
                    .known_atomic_facts_in_forall_facts
                    .get(&lookup_key)
                    .into_iter()
                    .flat_map(|facts| facts.iter())
                    .chain(
                        environment
                            .known_atomic_facts_in_forall_facts_by_arg_shape
                            .get(&lookup_key)
                            .into_iter()
                            .flat_map(|shape_map| shape_map.values())
                            .flat_map(|facts| facts.iter()),
                    )
            })
            .cloned()
            .collect();
        // We have already selected the exact stored forall that can prove this
        // projection. Its domain requirements may use known facts and builtin
        // computation, but must not start another equality/forall search and
        // recursively re-enter cart extensionality.
        let verify_state = UseContextVerifyState::new(0, true).without_known_forall_for_equality();
        for (pattern, forall_context) in candidates {
            let Some(arg_map) = self.match_atomic_fact_args_against_known_forall_ordered_args(
                &pattern,
                goal,
                &forall_context.params_def,
            )?
            else {
                continue;
            };
            if let Some(success) = self.verify_args_satisfy_forall_requirements(
                &pattern,
                &forall_context,
                arg_map,
                goal,
                &verify_state,
            )? {
                return Ok(Some(success.into()));
            }
        }
        Ok(None)
    }

    fn try_verify_empty_set_equality_from_not_nonempty(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let set = match (left, right) {
            (Obj::ListSet(list), set) if list.list.is_empty() => set.clone(),
            (set, Obj::ListSet(list)) if list.list.is_empty() => set.clone(),
            _ => return Ok(None),
        };

        let not_nonempty: AtomicFact =
            NotIsNonemptySetFact::new(set.clone(), line_file.clone()).into();
        let mut sub =
            self.verify_atomic_fact_as_builtin_rule_premise(&not_nonempty, builtin_state)?;
        if !sub.is_true() {
            let empty_order: Option<AtomicFact> = match &set {
                Obj::Range(range) => Some(
                    LessEqualFact::new(
                        range.end.as_ref().clone(),
                        range.start.as_ref().clone(),
                        line_file.clone(),
                    )
                    .into(),
                ),
                Obj::ClosedRange(range) => Some(
                    LessFact::new(
                        range.end.as_ref().clone(),
                        range.start.as_ref().clone(),
                        line_file.clone(),
                    )
                    .into(),
                ),
                _ => None,
            };
            if let Some(empty_order) = empty_order {
                let comparison = self
                    .verify_non_equational_atomic_fact_with_zero_premise_verification(
                        &empty_order,
                    )?;
                if comparison.is_true() {
                    sub = FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        not_nonempty.clone().into(),
                        "integer interval emptiness by number comparison".to_string(),
                        vec![comparison],
                    )
                    .into();
                }
            }
        }
        if !sub.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                equal_fact.clone().into(),
                InferResult::new(),
                "empty_set_equality_from_not_nonempty".to_string(),
                vec![sub],
            )
            .into(),
        ))
    }

    fn try_verify_empty_finite_set_from_size_zero(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let set = match (left, right) {
            (Obj::ListSet(list), set) if list.list.is_empty() => set.clone(),
            (set, Obj::ListSet(list)) if list.list.is_empty() => set.clone(),
            _ => return Ok(None),
        };
        let size: Obj = FiniteSetSize::new(set).into();
        let zero: Obj = Number::new("0".to_string()).into();
        let size_zero = self.verify_equal_fact_by_known_equality(&EqualFact::new_from_refs(
            &size,
            &zero,
            line_file.clone(),
        ));
        if !size_zero.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                equal_fact.clone().into(),
                InferResult::new(),
                "finite_set_size_zero_implies_empty_set".to_string(),
                vec![size_zero],
            )
            .into(),
        ))
    }

    fn verify_weak_order_subgoal(
        &mut self,
        greater_or_equal: &Obj,
        less_or_equal: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let greater_equal: AtomicFact = GreaterEqualFact::new(
            greater_or_equal.clone(),
            less_or_equal.clone(),
            line_file.clone(),
        )
        .into();
        let result =
            self.verify_atomic_fact_as_builtin_rule_premise(&greater_equal, builtin_state)?;
        if result.is_true() {
            return Ok(Some(result));
        }

        let less_equal: AtomicFact =
            LessEqualFact::new(less_or_equal.clone(), greater_or_equal.clone(), line_file).into();
        let result = self.verify_atomic_fact_as_builtin_rule_premise(&less_equal, builtin_state)?;
        if result.is_true() {
            return Ok(Some(result));
        }

        Ok(None)
    }

    // Equality follows from antisymmetry of the standard weak order.
    // Example: from `a >= b` and `b >= a`, prove `a = b`.
    // Membership premises in selected order builtins restrict list-set equality
    // search so that this fallback cannot recursively reopen the same goals.
    fn try_verify_equality_from_two_sided_weak_order(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let left_in_r: AtomicFact =
            InFact::new(left.clone(), StandardSet::R.into(), line_file.clone()).into();
        let right_in_r: AtomicFact =
            InFact::new(right.clone(), StandardSet::R.into(), line_file.clone()).into();
        let left_ge_right: AtomicFact =
            GreaterEqualFact::new(left.clone(), right.clone(), line_file.clone()).into();
        let right_le_left: AtomicFact =
            LessEqualFact::new(right.clone(), left.clone(), line_file.clone()).into();
        let right_ge_left: AtomicFact =
            GreaterEqualFact::new(right.clone(), left.clone(), line_file.clone()).into();
        let left_le_right: AtomicFact =
            LessEqualFact::new(left.clone(), right.clone(), line_file.clone()).into();
        let complete_result = self.verify_builtin_rule_premise_alternatives(
            vec![
                vec![
                    left_in_r.clone(),
                    right_in_r.clone(),
                    left_ge_right.clone(),
                    right_ge_left.clone(),
                ],
                vec![
                    left_in_r.clone(),
                    right_in_r.clone(),
                    left_ge_right,
                    left_le_right.clone(),
                ],
                vec![
                    left_in_r.clone(),
                    right_in_r.clone(),
                    right_le_left.clone(),
                    right_ge_left,
                ],
                vec![left_in_r, right_in_r, right_le_left, left_le_right],
            ],
            line_file.clone(),
            builtin_state,
        )?;
        if complete_result.is_true() {
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    equal_fact.clone().into(),
                    "equality from a >= b and b >= a".to_string(),
                    vec![complete_result],
                )
                .into(),
            ));
        }

        let Some(mut steps) = self.verify_objects_are_known_reals_in_builtin(
            &[left, right],
            &line_file,
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        let Some(left_ge_right) =
            self.verify_weak_order_subgoal(left, right, line_file.clone(), builtin_state)?
        else {
            return Ok(None);
        };
        let Some(right_ge_left) =
            self.verify_weak_order_subgoal(right, left, line_file.clone(), builtin_state)?
        else {
            return Ok(None);
        };
        steps.push(left_ge_right);
        steps.push(right_ge_left);

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                equal_fact.clone().into(),
                "equality from a >= b and b >= a".to_string(),
                steps,
            )
            .into(),
        ))
    }

    fn literal_zero_obj_for_division_builtin() -> Obj {
        Obj::Number(Number::new("0".to_string()))
    }

    fn equal_fact_sides_are_the_same_or_known_equal(&self, equal_fact: &EqualFact) -> bool {
        objs_match_for_pattern(&equal_fact.left, &equal_fact.right)
            || self.equal_fact_sides_have_same_known_equality_in_some_env(equal_fact)
    }

    fn verify_division_denominator_nonzero_subgoal(
        &mut self,
        denominator: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let not_zero: AtomicFact = NotEqualFact::new(
            denominator.clone(),
            Self::literal_zero_obj_for_division_builtin(),
            line_file,
        )
        .into();
        let result = self.verify_atomic_fact_as_builtin_rule_premise(&not_zero, builtin_state)?;
        if result.is_true() {
            return Ok(Some(result));
        }
        Ok(None)
    }

    fn try_verify_product_from_known_division_candidate(
        &mut self,
        equal_fact: &EqualFact,
        dividend: &Obj,
        quotient: &Obj,
        denominator: &Obj,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let line_file = &equal_fact.line_file;
        let division_obj: Obj = Div::new(dividend.clone(), denominator.clone()).into();
        if !self.equal_fact_sides_are_the_same_or_known_equal(&EqualFact::new_from_refs(
            &division_obj,
            quotient,
            line_file.clone(),
        )) {
            return Ok(None);
        }
        let Some(nonzero_result) = self.verify_division_denominator_nonzero_subgoal(
            denominator,
            line_file.clone(),
            builtin_state,
        )?
        else {
            return Ok(None);
        };

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                equal_fact.clone().into(),
                "division elimination: from a / b = c and b != 0, prove a = c * b".to_string(),
                vec![nonzero_result],
            )
            .into(),
        ))
    }

    fn try_verify_product_from_known_division(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let (dividend, product) = match (left, right) {
            (dividend, Obj::Mul(product)) => (dividend, product),
            (Obj::Mul(product), dividend) => (dividend, product),
            _ => return Ok(None),
        };

        if let Some(done) = self.try_verify_product_from_known_division_candidate(
            equal_fact,
            dividend,
            product.left.as_ref(),
            product.right.as_ref(),
            builtin_state,
        )? {
            return Ok(Some(done));
        }

        self.try_verify_product_from_known_division_candidate(
            equal_fact,
            dividend,
            product.right.as_ref(),
            product.left.as_ref(),
            builtin_state,
        )
    }

    fn try_verify_division_from_known_product(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let (division, quotient) = match (left, right) {
            (Obj::Div(division), quotient) => (division, quotient),
            (quotient, Obj::Div(division)) => (division, quotient),
            _ => return Ok(None),
        };

        let product_1: Obj = Mul::new(division.right.as_ref().clone(), quotient.clone()).into();
        let product_2: Obj = Mul::new(quotient.clone(), division.right.as_ref().clone()).into();
        if !self.equal_fact_sides_are_the_same_or_known_equal(&EqualFact::new_from_refs(
            division.left.as_ref(),
            &product_1,
            line_file.clone(),
        )) && !self.equal_fact_sides_are_the_same_or_known_equal(&EqualFact::new_from_refs(
            division.left.as_ref(),
            &product_2,
            line_file.clone(),
        )) {
            return Ok(None);
        }

        let Some(nonzero_result) = self.verify_division_denominator_nonzero_subgoal(
            division.right.as_ref(),
            line_file.clone(),
            builtin_state,
        )?
        else {
            return Ok(None);
        };

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                equal_fact.clone().into(),
                "division introduction: from a = b * c and b != 0, prove a / b = c".to_string(),
                vec![nonzero_result],
            )
            .into(),
        ))
    }

    // Division can be eliminated into multiplication, and multiplication can be
    // introduced into division when the divisor is nonzero.
    // Example: from `a / b = c`, prove `a = c * b`; from `a = b * c`, prove `a / b = c`.
    fn try_verify_division_product_conversion(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(done) =
            self.try_verify_product_from_known_division(equal_fact, builtin_state)?
        {
            return Ok(Some(done));
        }

        self.try_verify_division_from_known_product(equal_fact, builtin_state)
    }

    fn verify_user_prop_subgoal(
        &mut self,
        prop_name: &str,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
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
    fn try_verify_general_cart_set_builder_equality(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
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

    fn general_cart_named_set_builder_canonical_steps(
        &mut self,
        general_cart: &GeneralCart,
        set_builder: &SetBuilder,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        let Obj::FnSet(fn_set) = set_builder.param_set.as_ref() else {
            return Ok(None);
        };
        if ParamGroupWithSet::number_of_params(&fn_set.body.params_def_with_set) != 1
            || !fn_set.body.dom_facts.is_empty()
            || set_builder.facts.len() != 1
        {
            return Ok(None);
        }

        let domain_result = self.verify_equal_fact_as_builtin_premise(
            &EqualFact::new_from_refs(
                fn_set.body.params_def_with_set[0].set_obj(),
                general_cart.index_set.as_ref(),
                line_file.clone(),
            ),
            builtin_state,
        )?;
        if !domain_result.is_true() {
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
        if !ret_result.is_true() {
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
                if name == crate::common::keywords::IS_CHOICE_FUNCTION_FOR
        ) {
            return Ok(None);
        }
        let [choice_index, choice_family_set, choice_family_fn, choice_member] =
            choice_fact.body.as_slice()
        else {
            return Ok(None);
        };
        let expected_member =
            obj_for_bound_param_in_scope(&set_builder.param_binding, ParamObjType::SetBuilder);
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
            if !result.is_true() {
                return Ok(None);
            }
            steps.push(result);
        }
        Ok(Some(steps))
    }

    // Integer ranges are the canonical sets of integer points between their endpoints.
    // Examples: `closed_range(a, b) = {x Z: a <= x <= b}` and
    // `range(a, b) = {x Z: a <= x < b}`.
    fn try_verify_integer_range_set_builder_equality(
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
            let bound_param =
                obj_for_bound_param_in_scope(&set_builder.param_binding, ParamObjType::SetBuilder);
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
    fn try_verify_indexed_fn_set_definition_equality(
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
                ParamGroupWithSet::number_of_params(&expanded.body.params_def_with_set);
            if param_count != ParamGroupWithSet::number_of_params(&fn_set.body.params_def_with_set)
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

    // Antisymmetry rule for registered user-defined props.
    // Example: from `$p(a, b)` and `$p(b, a)`, prove `a = b`.
    fn try_verify_equality_from_known_antisymmetric_props(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let mut prop_names: Vec<String> = Vec::new();
        for env in self.iter_environments_from_top() {
            for prop_name in env.known_antisymmetric_props.keys() {
                if !prop_names.iter().any(|name| name == prop_name) {
                    prop_names.push(prop_name.clone());
                }
            }
        }

        for prop_name in prop_names {
            let left_to_right =
                self.verify_user_prop_subgoal(&prop_name, equal_fact, builtin_state)?;
            if !left_to_right.is_true() {
                continue;
            }
            let right_to_left = self.verify_user_prop_subgoal(
                &prop_name,
                &EqualFact::new_from_refs(right, left, line_file.clone()),
                builtin_state,
            )?;
            if !right_to_left.is_true() {
                continue;
            }
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    equal_fact.clone().into(),
                    format!(
                        "equality from registered antisymmetric prop `{}`",
                        prop_name
                    ),
                    vec![left_to_right, right_to_left],
                )
                .into(),
            ));
        }

        Ok(None)
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
