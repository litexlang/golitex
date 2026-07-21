use crate::prelude::*;
use crate::verify::verify_equality_by_builtin_rules::{
    factual_equal_success_by_builtin_reason, factual_equal_success_by_builtin_reason_with_subgoals,
    verify_equality_by_they_are_the_same,
};

impl Runtime {
    pub fn verify_equality_by_builtin_rules(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if verify_equality_by_they_are_the_same(left, right) {
            return Ok(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "they are the same",
            )
            .into());
        }

        if let Some(done) =
            self.try_verify_matrix_power_definition(left, right, left, right, line_file.clone())
        {
            return Ok(done);
        }
        if let Some(done) =
            self.try_verify_matrix_power_definition(left, right, right, left, line_file.clone())
        {
            return Ok(done);
        }

        if let Obj::ObjAsStructInstanceWithFieldAccess(field_access) = left {
            let projected = self.struct_field_access_projection(field_access)?;
            let projected_result = self.verify_equality_by_builtin_rules(
                &projected,
                right,
                line_file.clone(),
                verify_state,
            )?;
            if projected_result.is_true() {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        EqualFact::new(left.clone(), right.clone(), line_file).into(),
                        "struct field access is the corresponding tuple projection".to_string(),
                        vec![projected_result],
                    )
                    .into(),
                );
            }
        }
        if let Obj::ObjAsStructInstanceWithFieldAccess(field_access) = right {
            let projected = self.struct_field_access_projection(field_access)?;
            let projected_result = self.verify_equality_by_builtin_rules(
                left,
                &projected,
                line_file.clone(),
                verify_state,
            )?;
            if projected_result.is_true() {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        EqualFact::new(left.clone(), right.clone(), line_file).into(),
                        "struct field access is the corresponding tuple projection".to_string(),
                        vec![projected_result],
                    )
                    .into(),
                );
            }
        }

        if let Some(done) = self.try_verify_instantiated_template_obj_equality_by_resolved_values(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_general_cart_set_builder_equality(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_integer_range_set_builder_equality(left, right, line_file.clone())?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_size_integer_range_equality(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_size_fn_range_from_known_injection(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_size_from_known_bijection(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_abs_equalities(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_zero_equals_subtraction_implies_equal_operands(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_zero_equals_product_implies_other_factor_zero(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_square_sum_zero_from_zero_components(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_square_sum_component_zero_from_known_sum_zero(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        // Direct calculation: if both sides normalize to the same computed value, close the
        // equality before falling back to two-sided order. Example: `(-1 * sqrt(2)) ^ 2 = 2`.
        let (result, calculated_left, calculated_right) = self
            .verify_equality_by_they_are_the_same_and_calculation(
                left,
                right,
                line_file.clone(),
                verify_state,
            )?;
        if result.is_true() {
            return Ok(result);
        }

        if objs_equal_by_rational_expression_evaluation(&left, &right) {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    EqualFact::new(left.clone(), right.clone(), line_file).into(),
                    "calculation and rational expression simplification".to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }

        if objs_equal_by_rational_expression_evaluation(&calculated_left, &calculated_right) {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    EqualFact::new(left.clone(), right.clone(), line_file).into(),
                    "calculation and rational expression simplification".to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }

        if let Some(done) = self.try_verify_union_set_equalities(left, right, line_file.clone()) {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_intersection_set_equalities(left, right, line_file.clone())
        {
            return Ok(done);
        }

        if Self::intersection_has_literal_set_operand(left) {
            if let Some(done) = self.try_verify_literal_set_intersection_filter(
                left,
                right,
                left,
                right,
                line_file.clone(),
                verify_state,
            )? {
                return Ok(done);
            }
        }
        if Self::intersection_has_literal_set_operand(right) {
            if let Some(done) = self.try_verify_literal_set_intersection_filter(
                left,
                right,
                right,
                left,
                line_file.clone(),
                verify_state,
            )? {
                return Ok(done);
            }
        }

        if let Some(done) =
            self.try_verify_intersection_from_subset(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_set_minus_equalities(left, right, line_file.clone()) {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_size_set_minus_equality(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_size_union_equality(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_size_partition_equality(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_size_set_diff_equality(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_size_set_minus_of_subset_equality(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_cart_finite_set_size_product_equality(left, right, line_file.clone())
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_power_set_finite_set_size_equality(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_subtraction_from_known_addition(left, right, line_file.clone())?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_equality_from_two_sided_weak_order(left, right, line_file.clone())?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_integer_singleton_interval_equality_builtin_rule(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_equality_from_known_antisymmetric_props(left, right, line_file.clone())?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_positive_base_equal_from_equal_nonzero_integer_power(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_division_product_conversion(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_zero_equals_pow_from_base_zero(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_pow_one_identity(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_pow_zero_identity(left, right, line_file.clone())? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_one_pow_identity(left, right, line_file.clone())? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_zero_pow_positive_exponent_identity(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_sqrt_equalities(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_power_addition_exponent_rule(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_power_of_power_rule(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_power_product_rule(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_base_zero_from_known_positive_power_zero(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_abs_power_rule(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_power_inverse_rule(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_pow_reciprocal_exponent_equals_root_by_power(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_same_algebra_context_by_equal_args(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_log_identity_equalities(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_log_algebra_identities(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_log_reciprocal_rule(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_log_change_of_base_rule(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_log_equals_by_pow_inverse(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_pow_equals_by_known_log_inverse(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_sum_additivity(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_sum_merge_adjacent_ranges(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_sum_single_term(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_sum_split_last_term(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_product_single_term(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_product_split_last_term(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_sum_partition_adjacent_ranges(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_product_partition_adjacent_ranges(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_sum_reindex_shift(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_sum_constant_summand(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_sum_scalar_mul(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_sum_empty(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_sum_list_expansion(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_sum_closed_range_bridge(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_sum_constant_summand(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_sum_pointwise_equality(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_sum_substitution(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_sum_disjoint_union(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_sum_add(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_sum_scalar_mul(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_sum_over_cartesian_product(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_sum_fubini(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_sum_over_bijective_finite_set_enumerations(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_finite_set_product_empty(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_product_list_expansion(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_product_fresh_insertion(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_product_remove_member(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_product_closed_range_bridge(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_product_constant_factor(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_finite_set_product_pointwise_equality(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        // Empty set rule: `S = {}` follows from `not $is_nonempty_set(S)`.
        // This replaces the old common fact `S = {} <=> not $is_nonempty_set(S)`.
        // Example: after `not $is_nonempty_set(S)`, prove `S = {}`.
        if let Some(done) = self.try_verify_empty_set_equality_from_not_nonempty(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_mod_nested_same_modulus_absorption(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_zero_mod_equals_zero(left, right, line_file.clone())? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_mod_one_equals_zero(left, right, line_file.clone())? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_one_mod_equals_one_for_modulus_at_least_two(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_mod_dividend_minus_remainder_equals_zero(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_integer_quotient_defining_equation(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_mod_eq_remainder_from_euclidean_division(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_mod_peel_nested_same_modulus(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_mod_congruence_from_inner_binary(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_integer_mod_negation_rule(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_integer_mod_natural_power_rule(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_tuple_equality_from_dim_and_projections(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_symbolic_tuple_equality_from_coordinates(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_cart_equality_from_dim_and_projections(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_projection_from_known_tuple_equality(left, right, line_file.clone())?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_anonymous_fn_application_equals_other_side(
            left,
            right,
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }
        if let Some(done) = self.try_verify_anonymous_fn_application_equals_other_side(
            left,
            right,
            right,
            left,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_matrix_product_entry_equals_sum(
            left,
            right,
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }
        if let Some(done) = self.try_verify_matrix_product_entry_equals_sum(
            left,
            right,
            right,
            left,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_indexed_fn_set_definition_equality(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let (Obj::FnSet(left_fn_set), Obj::FnSet(right_fn_set)) = (left, right) {
            return self.verify_fn_set_with_params_equality_by_builtin_rules(
                left_fn_set,
                right_fn_set,
                line_file,
                verify_state,
            );
        }

        if let (Obj::AnonymousFn(l), Obj::AnonymousFn(r)) = (left, right) {
            if l.to_string() == r.to_string() {
                return Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        EqualFact::new(left.clone(), right.clone(), line_file).into(),
                        "anonymous fn: identical surface syntax (params, dom, ret, body)"
                            .to_string(),
                        Vec::new(),
                    ))
                    .into(),
                );
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    fn try_verify_projection_from_known_tuple_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(done) = self.try_verify_one_projection_from_known_tuple_equality(
            left,
            right,
            line_file.clone(),
        )? {
            return Ok(Some(done));
        }
        self.try_verify_one_projection_from_known_tuple_equality(right, left, line_file)
    }

    fn try_verify_one_projection_from_known_tuple_equality(
        &mut self,
        projection_side: &Obj,
        other_side: &Obj,
        line_file: LineFile,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Obj::ObjAtIndex(obj_at_index) = projection_side else {
            return Ok(None);
        };
        let Some(index) = self.obj_at_index_literal_positive_usize(obj_at_index.index.as_ref())
        else {
            return Ok(None);
        };
        let target_key = obj_at_index.obj.to_string();
        for env in self.iter_environments_from_top() {
            let Some((_, equal_objs)) = env.known_equality.get(&target_key) else {
                continue;
            };
            for equal_obj in equal_objs.iter() {
                if let Some(component) = Self::component_at_index(equal_obj, index) {
                    if self
                        .verify_objs_are_equal_known_only(&component, other_side, line_file.clone())
                        .is_true()
                    {
                        return Ok(Some(
                            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                                EqualFact::new(
                                    projection_side.clone(),
                                    other_side.clone(),
                                    line_file,
                                )
                                .into(),
                                "projection from known tuple equality".to_string(),
                                Vec::new(),
                            )
                            .into(),
                        ));
                    }
                }
            }
        }
        Ok(None)
    }

    fn obj_at_index_literal_positive_usize(&self, index_obj: &Obj) -> Option<usize> {
        let number = self.resolve_obj_to_number(index_obj)?;
        let parsed = number.normalized_value.parse::<usize>().ok()?;
        if parsed == 0 {
            None
        } else {
            Some(parsed)
        }
    }

    fn component_at_index(obj: &Obj, index: usize) -> Option<Obj> {
        match obj {
            Obj::Tuple(tuple) => tuple.args.get(index - 1).map(|x| x.as_ref().clone()),
            Obj::ListSet(list_set) => list_set.list.get(index - 1).map(|x| x.as_ref().clone()),
            _ => None,
        }
    }

    fn try_verify_union_set_equalities(
        &self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Option<StmtResult> {
        // Union commutativity for sets.
        // Example: `union(A, B) = union(B, A)`.
        if Self::union_commutative_shape(left, right) {
            return Some(Self::set_equality_success(
                left,
                right,
                line_file,
                "union_commutative",
            ));
        }

        // Union associativity for sets, accepted in either equality direction.
        // Example: `union(union(A, B), C) = union(A, union(B, C))`.
        if Self::union_associative_shape(left, right) || Self::union_associative_shape(right, left)
        {
            return Some(Self::set_equality_success(
                left,
                right,
                line_file,
                "union_associative",
            ));
        }

        // Union idempotence for sets, accepted in either equality direction.
        // Example: `union(A, A) = A`.
        if Self::union_idempotent_shape(left, right) || Self::union_idempotent_shape(right, left) {
            return Some(Self::set_equality_success(
                left,
                right,
                line_file,
                "union_idempotent",
            ));
        }

        // Empty set is a two-sided identity for union, accepted in either equality direction.
        // Example: `union(A, {}) = A` and `union({}, A) = A`.
        if Self::union_empty_identity_shape(left, right)
            || Self::union_empty_identity_shape(right, left)
        {
            return Some(Self::set_equality_success(
                left,
                right,
                line_file,
                "union_empty_identity",
            ));
        }

        None
    }

    fn try_verify_intersection_set_equalities(
        &self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Option<StmtResult> {
        // Intersection commutativity for sets.
        // Example: `intersect(A, B) = intersect(B, A)`.
        if Self::intersect_commutative_shape(left, right) {
            return Some(Self::set_equality_success(
                left,
                right,
                line_file,
                "intersect_commutative",
            ));
        }

        // Intersection associativity for sets, accepted in either equality direction.
        // Example: `intersect(intersect(A, B), C) = intersect(A, intersect(B, C))`.
        if Self::intersect_associative_shape(left, right)
            || Self::intersect_associative_shape(right, left)
        {
            return Some(Self::set_equality_success(
                left,
                right,
                line_file,
                "intersect_associative",
            ));
        }

        // Intersection distributes over union for sets, accepted in either equality direction.
        // Example: `intersect(A, union(B, C)) = union(intersect(A, B), intersect(A, C))`.
        if Self::intersect_union_distributive_shape(left, right)
            || Self::intersect_union_distributive_shape(right, left)
        {
            return Some(Self::set_equality_success(
                left,
                right,
                line_file,
                "intersect_union_distributive",
            ));
        }

        None
    }

    fn try_verify_set_minus_equalities(
        &self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Option<StmtResult> {
        // A symmetric difference is the union of its two asymmetric differences.
        // Example: `set_diff(A, B) = union(set_minus(A, B), set_minus(B, A))`.
        if Self::set_diff_as_union_of_asymmetric_differences_shape(left, right)
            || Self::set_diff_as_union_of_asymmetric_differences_shape(right, left)
        {
            return Some(Self::set_equality_success(
                left,
                right,
                line_file,
                "set_diff_as_union_of_asymmetric_differences",
            ));
        }

        // Set-minus distributes over union by De Morgan's law, accepted in either direction.
        // Example: `set_minus(A, union(B, C)) = intersect(set_minus(A, B), set_minus(A, C))`.
        if Self::set_minus_union_de_morgan_shape(left, right)
            || Self::set_minus_union_de_morgan_shape(right, left)
        {
            return Some(Self::set_equality_success(
                left,
                right,
                line_file,
                "set_minus_union_de_morgan",
            ));
        }

        // Set-minus distributes over intersection by De Morgan's law, accepted in either direction.
        // Example: `set_minus(A, intersect(B, C)) = union(set_minus(A, B), set_minus(A, C))`.
        if Self::set_minus_intersect_de_morgan_shape(left, right)
            || Self::set_minus_intersect_de_morgan_shape(right, left)
        {
            return Some(Self::set_equality_success(
                left,
                right,
                line_file,
                "set_minus_intersect_de_morgan",
            ));
        }

        None
    }

    fn try_verify_cart_finite_set_size_product_equality(
        &self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Option<StmtResult> {
        // Cardinality of a finite Cartesian product is the product of factor cardinalities.
        // Example: `finite_set_size(cart(A, B)) = finite_set_size(A) * finite_set_size(B)`.
        if Self::cart_finite_set_size_product_shape(left, right)
            || Self::cart_finite_set_size_product_shape(right, left)
        {
            return Some(Self::set_equality_success(
                left,
                right,
                line_file,
                "cart_finite_set_size_product",
            ));
        }

        None
    }

    fn try_verify_finite_set_size_set_minus_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        // Removing a finite subset counts the original set minus its overlap with the removed set.
        // Example: `finite_set_size(set_minus(S, T)) = finite_set_size(S) - finite_set_size(intersect(S, T))`.
        let Some((first_set, second_set)) = Self::finite_set_size_set_minus_shape(left, right)
            .or_else(|| Self::finite_set_size_set_minus_shape(right, left))
        else {
            return Ok(None);
        };

        let first_finite: AtomicFact = IsFiniteSetFact::new(first_set, line_file.clone()).into();
        let first_result =
            self.verify_non_equational_known_then_builtin_rules_only(&first_finite, verify_state)?;
        if !first_result.is_true() {
            return Ok(None);
        }

        let second_finite: AtomicFact = IsFiniteSetFact::new(second_set, line_file.clone()).into();
        let second_result =
            self.verify_non_equational_known_then_builtin_rules_only(&second_finite, verify_state)?;
        if !second_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
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
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some((first_set, second_set)) = Self::finite_set_size_union_shape(left, right)
            .or_else(|| Self::finite_set_size_union_shape(right, left))
        else {
            return Ok(None);
        };
        let Some(step_results) = self.verify_two_sets_are_finite(
            first_set,
            second_set,
            line_file.clone(),
            verify_state,
        )?
        else {
            return Ok(None);
        };

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
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
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some((first_set, second_set)) = Self::finite_set_size_partition_shape(left, right)
            .or_else(|| Self::finite_set_size_partition_shape(right, left))
        else {
            return Ok(None);
        };
        let Some(step_results) = self.verify_two_sets_are_finite(
            first_set,
            second_set,
            line_file.clone(),
            verify_state,
        )?
        else {
            return Ok(None);
        };

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "finite_set_size_partition_by_intersection_and_difference".to_string(),
                step_results,
            )
            .into(),
        ))
    }

    // The symmetric difference is the sum of the two disjoint directed differences.
    // Example: `finite_set_size(set_diff(A, B)) = finite_set_size(set_minus(A, B)) + finite_set_size(set_minus(B, A))`.
    fn try_verify_finite_set_size_set_diff_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some((first_set, second_set)) = Self::finite_set_size_set_diff_shape(left, right)
            .or_else(|| Self::finite_set_size_set_diff_shape(right, left))
        else {
            return Ok(None);
        };
        let Some(step_results) = self.verify_two_sets_are_finite(
            first_set,
            second_set,
            line_file.clone(),
            verify_state,
        )?
        else {
            return Ok(None);
        };

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "finite_set_size_symmetric_difference".to_string(),
                step_results,
            )
            .into(),
        ))
    }

    // Removing a finite subset subtracts exactly that subset's cardinality.
    // Example: `B $subset A` gives `finite_set_size(set_minus(A, B)) = finite_set_size(A) - finite_set_size(B)`.
    fn try_verify_finite_set_size_set_minus_of_subset_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some((container, subset)) =
            Self::finite_set_size_set_minus_of_subset_shape(left, right)
                .or_else(|| Self::finite_set_size_set_minus_of_subset_shape(right, left))
        else {
            return Ok(None);
        };

        let subset_fact: AtomicFact =
            SubsetFact::new(subset.clone(), container.clone(), line_file.clone()).into();
        let subset_result =
            self.verify_non_equational_known_then_builtin_rules_only(&subset_fact, verify_state)?;
        if !subset_result.is_true() {
            return Ok(None);
        }
        let container_finite: AtomicFact =
            IsFiniteSetFact::new(container, line_file.clone()).into();
        let container_result = self
            .verify_non_equational_known_then_builtin_rules_only(&container_finite, verify_state)?;
        if !container_result.is_true() {
            return Ok(None);
        }
        let subset_finite: AtomicFact = IsFiniteSetFact::new(subset, line_file.clone()).into();
        let subset_finite_result =
            self.verify_non_equational_known_then_builtin_rules_only(&subset_finite, verify_state)?;
        if !subset_finite_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
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
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some((start, end, closed)) = Self::finite_set_size_integer_range_shape(left, right)
            .or_else(|| Self::finite_set_size_integer_range_shape(right, left))
        else {
            return Ok(None);
        };

        let start_in_n: AtomicFact =
            InFact::new(start.clone(), StandardSet::N.into(), line_file.clone()).into();
        let start_result =
            self.verify_non_equational_known_then_builtin_rules_only(&start_in_n, verify_state)?;
        if !start_result.is_true() {
            return Ok(None);
        }

        let end_in_n: AtomicFact =
            InFact::new(end.clone(), StandardSet::N.into(), line_file.clone()).into();
        let end_result =
            self.verify_non_equational_known_then_builtin_rules_only(&end_in_n, verify_state)?;
        if !end_result.is_true() {
            return Ok(None);
        }

        let endpoints_ordered: AtomicFact =
            LessEqualFact::new(start, end, line_file.clone()).into();
        let order_result = self.verify_non_equational_known_then_builtin_rules_only(
            &endpoints_ordered,
            verify_state,
        )?;
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
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                rule.to_string(),
                vec![start_result, end_result, order_result],
            )
            .into(),
        ))
    }

    fn try_verify_power_set_finite_set_size_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        // Cardinality of a finite power set is `2` to the cardinality of the base set.
        // Example: from `$is_finite_set(S)`, prove `finite_set_size(power_set(S)) = 2^finite_set_size(S)`.
        let Some(base_set) = Self::power_set_finite_set_size_shape(left, right)
            .or_else(|| Self::power_set_finite_set_size_shape(right, left))
        else {
            return Ok(None);
        };

        let base_finite: AtomicFact = IsFiniteSetFact::new(base_set, line_file.clone()).into();
        let base_result =
            self.verify_non_equational_known_then_builtin_rules_only(&base_finite, verify_state)?;
        if !base_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "power_set_finite_set_size_two_pow_finite_set_size_base".to_string(),
                vec![base_result],
            )
            .into(),
        ))
    }

    fn set_equality_success(
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        reason: &str,
    ) -> StmtResult {
        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            EqualFact::new(left.clone(), right.clone(), line_file).into(),
            reason.to_string(),
            Vec::new(),
        )
        .into()
    }

    fn union_commutative_shape(left: &Obj, right: &Obj) -> bool {
        let (Obj::Union(left_union), Obj::Union(right_union)) = (left, right) else {
            return false;
        };
        verify_equality_by_they_are_the_same(&left_union.left, &right_union.right)
            && verify_equality_by_they_are_the_same(&left_union.right, &right_union.left)
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
        verify_equality_by_they_are_the_same(&left_inner.left, &right_outer.left)
            && verify_equality_by_they_are_the_same(&left_inner.right, &right_inner.left)
            && verify_equality_by_they_are_the_same(&left_outer.right, &right_inner.right)
    }

    fn intersect_commutative_shape(left: &Obj, right: &Obj) -> bool {
        let (Obj::Intersect(left_intersect), Obj::Intersect(right_intersect)) = (left, right)
        else {
            return false;
        };
        verify_equality_by_they_are_the_same(&left_intersect.left, &right_intersect.right)
            && verify_equality_by_they_are_the_same(&left_intersect.right, &right_intersect.left)
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
        verify_equality_by_they_are_the_same(&left_inner.left, &right_outer.left)
            && verify_equality_by_they_are_the_same(&left_inner.right, &right_inner.left)
            && verify_equality_by_they_are_the_same(&left_outer.right, &right_inner.right)
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
        verify_equality_by_they_are_the_same(&left_intersect.left, &right_left_intersect.left)
            && verify_equality_by_they_are_the_same(
                &left_intersect.left,
                &right_right_intersect.left,
            )
            && verify_equality_by_they_are_the_same(&left_union.left, &right_left_intersect.right)
            && verify_equality_by_they_are_the_same(&left_union.right, &right_right_intersect.right)
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

    fn set_diff_as_union_of_asymmetric_differences_shape(left: &Obj, right: &Obj) -> bool {
        let Obj::SetDiff(set_diff) = left else {
            return false;
        };
        let Obj::Union(union) = right else {
            return false;
        };
        let Obj::SetMinus(left_set_minus) = union.left.as_ref() else {
            return false;
        };
        let Obj::SetMinus(right_set_minus) = union.right.as_ref() else {
            return false;
        };
        verify_equality_by_they_are_the_same(&set_diff.left, &left_set_minus.left)
            && verify_equality_by_they_are_the_same(&set_diff.right, &left_set_minus.right)
            && verify_equality_by_they_are_the_same(&set_diff.right, &right_set_minus.left)
            && verify_equality_by_they_are_the_same(&set_diff.left, &right_set_minus.right)
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

    fn set_minus_de_morgan_args_match(
        left_set_minus: &SetMinus,
        first_removed_set: &Obj,
        second_removed_set: &Obj,
        right_left_set_minus: &SetMinus,
        right_right_set_minus: &SetMinus,
    ) -> bool {
        verify_equality_by_they_are_the_same(&left_set_minus.left, &right_left_set_minus.left)
            && verify_equality_by_they_are_the_same(
                &left_set_minus.left,
                &right_right_set_minus.left,
            )
            && verify_equality_by_they_are_the_same(first_removed_set, &right_left_set_minus.right)
            && verify_equality_by_they_are_the_same(
                second_removed_set,
                &right_right_set_minus.right,
            )
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
        verify_equality_by_they_are_the_same(&expected_product, product_side)
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

        if verify_equality_by_they_are_the_same(&set_minus.left, &first_size.set)
            && verify_equality_by_they_are_the_same(&set_minus.left, &intersection.left)
            && verify_equality_by_they_are_the_same(&set_minus.right, &intersection.right)
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

        if verify_equality_by_they_are_the_same(&union.left, &first_size.set)
            && verify_equality_by_they_are_the_same(&union.right, &second_size.set)
            && verify_equality_by_they_are_the_same(&union.left, &intersection.left)
            && verify_equality_by_they_are_the_same(&union.right, &intersection.right)
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

        if verify_equality_by_they_are_the_same(&main_size.set, &intersection.left)
            && verify_equality_by_they_are_the_same(&main_size.set, &remainder.left)
            && verify_equality_by_they_are_the_same(&intersection.right, &remainder.right)
        {
            Some((
                main_size.set.as_ref().clone(),
                intersection.right.as_ref().clone(),
            ))
        } else if verify_equality_by_they_are_the_same(&main_size.set, &intersection.right)
            && verify_equality_by_they_are_the_same(&main_size.set, &remainder.left)
            && verify_equality_by_they_are_the_same(&intersection.left, &remainder.right)
        {
            Some((
                main_size.set.as_ref().clone(),
                intersection.left.as_ref().clone(),
            ))
        } else {
            None
        }
    }

    fn finite_set_size_set_diff_shape(
        finite_set_size_side: &Obj,
        directed_differences_side: &Obj,
    ) -> Option<(Obj, Obj)> {
        let Obj::FiniteSetSize(set_diff_size) = finite_set_size_side else {
            return None;
        };
        let Obj::SetDiff(set_diff) = set_diff_size.set.as_ref() else {
            return None;
        };
        let Obj::Add(sum) = directed_differences_side else {
            return None;
        };
        let Obj::FiniteSetSize(first_difference_size) = sum.left.as_ref() else {
            return None;
        };
        let Obj::SetMinus(first_difference) = first_difference_size.set.as_ref() else {
            return None;
        };
        let Obj::FiniteSetSize(second_difference_size) = sum.right.as_ref() else {
            return None;
        };
        let Obj::SetMinus(second_difference) = second_difference_size.set.as_ref() else {
            return None;
        };

        if verify_equality_by_they_are_the_same(&set_diff.left, &first_difference.left)
            && verify_equality_by_they_are_the_same(&set_diff.right, &first_difference.right)
            && verify_equality_by_they_are_the_same(&set_diff.right, &second_difference.left)
            && verify_equality_by_they_are_the_same(&set_diff.left, &second_difference.right)
        {
            Some((
                set_diff.left.as_ref().clone(),
                set_diff.right.as_ref().clone(),
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

        if verify_equality_by_they_are_the_same(&remainder.left, &container_size.set)
            && verify_equality_by_they_are_the_same(&remainder.right, &subset_size.set)
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
        verify_state: &VerifyState,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        let first_finite: AtomicFact = IsFiniteSetFact::new(first_set, line_file.clone()).into();
        let first_result =
            self.verify_non_equational_known_then_builtin_rules_only(&first_finite, verify_state)?;
        if !first_result.is_true() {
            return Ok(None);
        }
        let second_finite: AtomicFact = IsFiniteSetFact::new(second_set, line_file).into();
        let second_result =
            self.verify_non_equational_known_then_builtin_rules_only(&second_finite, verify_state)?;
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
        if !verify_equality_by_they_are_the_same(&expected_cardinality, cardinality_side) {
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
        if verify_equality_by_they_are_the_same(&expected_pow, pow_side) {
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
        verify_equality_by_they_are_the_same(&union.left, &union.right)
            && verify_equality_by_they_are_the_same(&union.left, other_side)
    }

    fn union_empty_identity_shape(union_side: &Obj, other_side: &Obj) -> bool {
        let Obj::Union(union) = union_side else {
            return false;
        };
        (Self::is_empty_list_set(&union.left)
            && verify_equality_by_they_are_the_same(&union.right, other_side))
            || (Self::is_empty_list_set(&union.right)
                && verify_equality_by_they_are_the_same(&union.left, other_side))
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
        statement_left: &Obj,
        statement_right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (intersection_side, target_side) in [
            (statement_left, statement_right),
            (statement_right, statement_left),
        ] {
            let Obj::Intersect(intersection) = intersection_side else {
                continue;
            };

            let (subset, superset) =
                if verify_equality_by_they_are_the_same(target_side, &intersection.right) {
                    (&intersection.right, &intersection.left)
                } else if verify_equality_by_they_are_the_same(target_side, &intersection.left) {
                    (&intersection.left, &intersection.right)
                } else {
                    continue;
                };

            let subset_fact: AtomicFact = SubsetFact::new(
                subset.as_ref().clone(),
                superset.as_ref().clone(),
                line_file.clone(),
            )
            .into();
            let subset_result = self
                .verify_non_equational_known_then_builtin_rules_only(&subset_fact, verify_state)?;
            if !subset_result.is_true() {
                continue;
            }

            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    EqualFact::new(statement_left.clone(), statement_right.clone(), line_file)
                        .into(),
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
        statement_left: &Obj,
        statement_right: &Obj,
        intersection_side: &Obj,
        target_side: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
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
                self.verify_non_equational_known_then_builtin_rules_only(&in_set, verify_state)?;
            if in_result.is_true() {
                kept.push(element_obj);
                steps.push(in_result);
                continue;
            }

            let not_in_set: AtomicFact =
                NotInFact::new(element_obj, set.clone(), line_file.clone()).into();
            let not_in_result = self
                .verify_non_equational_known_then_builtin_rules_only(&not_in_set, verify_state)?;
            if not_in_result.is_true() {
                steps.push(not_in_result);
                continue;
            }

            return Ok(None);
        }

        let filtered_set: Obj = ListSet::new(kept).into();
        if !verify_equality_by_they_are_the_same(&filtered_set, target_side) {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(statement_left.clone(), statement_right.clone(), line_file).into(),
                "intersect_literal_set_filter".to_string(),
                steps,
            )
            .into(),
        ))
    }

    fn try_verify_subtraction_from_known_addition(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(done) = self.try_verify_one_subtraction_from_known_addition(
            left,
            right,
            left,
            right,
            line_file.clone(),
        )? {
            return Ok(Some(done));
        }
        self.try_verify_one_subtraction_from_known_addition(left, right, right, left, line_file)
    }

    // Moves one addend across a known sum equality.
    // Example: from a known `a + b = c` or `b + a = c`, prove `a = c - b`.
    fn try_verify_one_subtraction_from_known_addition(
        &mut self,
        statement_left: &Obj,
        statement_right: &Obj,
        target_a: &Obj,
        subtraction_side: &Obj,
        line_file: LineFile,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Obj::Sub(subtraction) = subtraction_side else {
            return Ok(None);
        };

        let candidate_sum_1: Obj =
            Add::new(target_a.clone(), subtraction.right.as_ref().clone()).into();
        let known_sum_1 = self.verify_objs_are_equal_known_only(
            &candidate_sum_1,
            subtraction.left.as_ref(),
            line_file.clone(),
        );
        if known_sum_1.is_true() {
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    EqualFact::new(statement_left.clone(), statement_right.clone(), line_file)
                        .into(),
                    "equality: a = c - b from known a + b = c".to_string(),
                    vec![known_sum_1],
                )
                .into(),
            ));
        }

        let candidate_sum_2: Obj =
            Add::new(subtraction.right.as_ref().clone(), target_a.clone()).into();
        let known_sum_2 = self.verify_objs_are_equal_known_only(
            &candidate_sum_2,
            subtraction.left.as_ref(),
            line_file.clone(),
        );
        if known_sum_2.is_true() {
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    EqualFact::new(statement_left.clone(), statement_right.clone(), line_file)
                        .into(),
                    "equality: a = c - b from known b + a = c".to_string(),
                    vec![known_sum_2],
                )
                .into(),
            ));
        }

        Ok(None)
    }

    // Tuple extensionality: a tuple is equal to `(a, b, ...)` when its dimension matches
    // and each projection matches the corresponding component.
    // Example: from `tuple_dim(t) = 2`, `t[1] = a`, and `t[2] = b`, prove `t = (a, b)`.
    fn try_verify_tuple_equality_from_dim_and_projections(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
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
        let is_tuple_result =
            self.verify_atomic_fact_known_then_builtin_rules_only(&is_tuple_fact, verify_state)?;
        if !is_tuple_result.is_true() {
            return Ok(None);
        }

        let tuple_dim_obj: Obj = TupleDim::new(target_obj.clone()).into();
        let tuple_dim_value_obj: Obj = Number::new(tuple_obj.args.len().to_string()).into();
        let tuple_dim_fact: AtomicFact =
            EqualFact::new(tuple_dim_obj, tuple_dim_value_obj, line_file.clone()).into();
        let tuple_dim_result =
            self.verify_atomic_fact_known_then_builtin_rules_only(&tuple_dim_fact, verify_state)?;
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
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
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
    fn try_verify_symbolic_tuple_equality_from_coordinates(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
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
        let left_is_tuple_result =
            self.verify_non_equational_known_then_builtin_rules_only(&left_is_tuple, verify_state)?;
        if !left_is_tuple_result.is_true() {
            return Ok(None);
        }

        let right_is_tuple: AtomicFact = IsTupleFact::new(right.clone(), line_file.clone()).into();
        let right_is_tuple_result = self
            .verify_non_equational_known_then_builtin_rules_only(&right_is_tuple, verify_state)?;
        if !right_is_tuple_result.is_true() {
            return Ok(None);
        }

        let left_dim: Obj = TupleDim::new(left.clone()).into();
        let right_dim: Obj = TupleDim::new(right.clone()).into();
        let same_dim: AtomicFact =
            EqualFact::new(left_dim.clone(), right_dim, line_file.clone()).into();
        let same_dim_result =
            self.verify_atomic_fact_known_then_builtin_rules_only(&same_dim, verify_state)?;
        if !same_dim_result.is_true() {
            return Ok(None);
        }

        let dimension_is_positive: AtomicFact = LessEqualFact::new(
            Number::new("1".to_string()).into(),
            left_dim.clone(),
            line_file.clone(),
        )
        .into();
        let dimension_is_positive_result = self
            .verify_non_equational_known_then_builtin_rules_only(
                &dimension_is_positive,
                verify_state,
            )?;
        if !dimension_is_positive_result.is_true() {
            return Ok(None);
        }

        let index_name = self.generate_random_unused_name();
        let index_obj = obj_for_bound_param_in_scope(index_name.clone(), ParamObjType::Forall);
        let coordinate_equality: AtomicFact = EqualFact::new(
            ObjAtIndex::new(left.clone(), index_obj.clone()).into(),
            ObjAtIndex::new(right.clone(), index_obj).into(),
            line_file.clone(),
        )
        .into();
        let coordinate_params = ParamDefWithType::new(vec![ParamGroupWithParamType::new(
            vec![index_name],
            ParamType::Obj(ClosedRange::new(Number::new("1".to_string()).into(), left_dim).into()),
        )]);
        let coordinate_result = self.run_in_local_env(|rt| {
            rt.define_params_with_type(&coordinate_params, false, ParamObjType::Forall)?;
            rt.verify_atomic_fact_with_known_forall(&coordinate_equality, verify_state)
        })?;
        if !coordinate_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
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
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
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
        let is_cart_result =
            self.verify_non_equational_known_then_builtin_rules_only(&is_cart_fact, verify_state)?;
        if !is_cart_result.is_true() {
            return Ok(None);
        }

        let cart_dim_obj: Obj = CartDim::new(target_obj.clone()).into();
        let cart_dim_value_obj: Obj = Number::new(cart_obj.args.len().to_string()).into();
        let cart_dim_fact: AtomicFact =
            EqualFact::new(cart_dim_obj, cart_dim_value_obj, line_file.clone()).into();
        let cart_dim_result =
            self.verify_atomic_fact_known_then_builtin_rules_only(&cart_dim_fact, verify_state)?;
        if !cart_dim_result.is_true() {
            return Ok(None);
        }

        let mut steps = vec![is_cart_result, cart_dim_result];
        for (index, arg) in cart_obj.args.iter().enumerate() {
            let index_obj: Obj = Number::new((index + 1).to_string()).into();
            let projected_target: Obj = Proj::new(target_obj.clone(), index_obj).into();
            let projection_fact: AtomicFact =
                EqualFact::new(projected_target, arg.as_ref().clone(), line_file.clone()).into();
            let projection_result = self.verify_atomic_fact(&projection_fact, verify_state)?;
            if !projection_result.is_true() {
                return Ok(None);
            }
            steps.push(projection_result);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "cart equality from dimension and projections".to_string(),
                steps,
            )
            .into(),
        ))
    }

    fn try_verify_empty_set_equality_from_not_nonempty(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let set = match (left, right) {
            (Obj::ListSet(list), set) if list.list.is_empty() => set.clone(),
            (set, Obj::ListSet(list)) if list.list.is_empty() => set.clone(),
            _ => return Ok(None),
        };

        let not_nonempty: AtomicFact = NotIsNonemptySetFact::new(set, line_file.clone()).into();
        let sub =
            self.verify_non_equational_known_then_builtin_rules_only(&not_nonempty, verify_state)?;
        if !sub.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                InferResult::new(),
                "empty_set_equality_from_not_nonempty".to_string(),
                vec![sub],
            )
            .into(),
        ))
    }

    fn verify_weak_order_subgoal(
        &mut self,
        greater_or_equal: &Obj,
        less_or_equal: &Obj,
        line_file: LineFile,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let greater_equal: AtomicFact = GreaterEqualFact::new(
            greater_or_equal.clone(),
            less_or_equal.clone(),
            line_file.clone(),
        )
        .into();
        let result = self.verify_non_equational_known_then_builtin_rules_only(
            &greater_equal,
            &VerifyState::new(0, true),
        )?;
        if result.is_true() {
            return Ok(Some(result));
        }

        let less_equal: AtomicFact =
            LessEqualFact::new(less_or_equal.clone(), greater_or_equal.clone(), line_file).into();
        let result = self.verify_non_equational_known_then_builtin_rules_only(
            &less_equal,
            &VerifyState::new(0, true),
        )?;
        if result.is_true() {
            return Ok(Some(result));
        }

        Ok(None)
    }

    // Equality follows from antisymmetry of the standard weak order.
    // Example: from `a >= b` and `b >= a`, prove `a = b`.
    fn try_verify_equality_from_two_sided_weak_order(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let verify_state = VerifyState::new(0, true);
        let Some(mut steps) =
            self.verify_objects_are_known_reals(&[left, right], &line_file, &verify_state)?
        else {
            return Ok(None);
        };
        let Some(left_ge_right) = self.verify_weak_order_subgoal(left, right, line_file.clone())?
        else {
            return Ok(None);
        };
        let Some(right_ge_left) = self.verify_weak_order_subgoal(right, left, line_file.clone())?
        else {
            return Ok(None);
        };
        steps.push(left_ge_right);
        steps.push(right_ge_left);

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "equality from a >= b and b >= a".to_string(),
                steps,
            )
            .into(),
        ))
    }

    fn literal_zero_obj_for_division_builtin() -> Obj {
        Obj::Number(Number::new("0".to_string()))
    }

    fn objs_are_the_same_or_known_equal(&self, left: &Obj, right: &Obj) -> bool {
        verify_equality_by_they_are_the_same(left, right)
            || self.objs_have_same_known_equality_rc_in_some_env(left, right)
    }

    fn verify_division_denominator_nonzero_subgoal(
        &mut self,
        denominator: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let not_zero: AtomicFact = NotEqualFact::new(
            denominator.clone(),
            Self::literal_zero_obj_for_division_builtin(),
            line_file,
        )
        .into();
        let result =
            self.verify_non_equational_known_then_builtin_rules_only(&not_zero, verify_state)?;
        if result.is_true() {
            return Ok(Some(result));
        }
        Ok(None)
    }

    fn try_verify_product_from_known_division_candidate(
        &mut self,
        dividend: &Obj,
        quotient: &Obj,
        denominator: &Obj,
        target_left: &Obj,
        target_right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let division_obj: Obj = Div::new(dividend.clone(), denominator.clone()).into();
        if !self.objs_are_the_same_or_known_equal(&division_obj, quotient) {
            return Ok(None);
        }
        let Some(nonzero_result) = self.verify_division_denominator_nonzero_subgoal(
            denominator,
            line_file.clone(),
            verify_state,
        )?
        else {
            return Ok(None);
        };

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(target_left.clone(), target_right.clone(), line_file).into(),
                "division elimination: from a / b = c and b != 0, prove a = c * b".to_string(),
                vec![nonzero_result],
            )
            .into(),
        ))
    }

    fn try_verify_product_from_known_division(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (dividend, product) = match (left, right) {
            (dividend, Obj::Mul(product)) => (dividend, product),
            (Obj::Mul(product), dividend) => (dividend, product),
            _ => return Ok(None),
        };

        if let Some(done) = self.try_verify_product_from_known_division_candidate(
            dividend,
            product.left.as_ref(),
            product.right.as_ref(),
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(Some(done));
        }

        self.try_verify_product_from_known_division_candidate(
            dividend,
            product.right.as_ref(),
            product.left.as_ref(),
            left,
            right,
            line_file,
            verify_state,
        )
    }

    fn try_verify_division_from_known_product(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (division, quotient) = match (left, right) {
            (Obj::Div(division), quotient) => (division, quotient),
            (quotient, Obj::Div(division)) => (division, quotient),
            _ => return Ok(None),
        };

        let product_1: Obj = Mul::new(division.right.as_ref().clone(), quotient.clone()).into();
        let product_2: Obj = Mul::new(quotient.clone(), division.right.as_ref().clone()).into();
        if !self.objs_are_the_same_or_known_equal(division.left.as_ref(), &product_1)
            && !self.objs_are_the_same_or_known_equal(division.left.as_ref(), &product_2)
        {
            return Ok(None);
        }

        let Some(nonzero_result) = self.verify_division_denominator_nonzero_subgoal(
            division.right.as_ref(),
            line_file.clone(),
            verify_state,
        )?
        else {
            return Ok(None);
        };

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
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
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(done) = self.try_verify_product_from_known_division(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(Some(done));
        }

        self.try_verify_division_from_known_product(left, right, line_file, verify_state)
    }

    fn verify_user_prop_subgoal(
        &mut self,
        prop_name: &str,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Result<StmtResult, RuntimeError> {
        let fact: AtomicFact = NormalAtomicFact::new(
            AtomicName::WithoutMod(prop_name.to_string()),
            vec![left.clone(), right.clone()],
            line_file,
        )
        .into();
        self.verify_non_equational_known_then_builtin_rules_only(&fact, &VerifyState::new(0, true))
    }

    // Instantiated template objects materialize to ordinary Litex objects; compare those
    // materialized values when a template instance appears in an equality.
    // Example: if `\T<a>` resolves to `sum(1, n, f)` and `\T<b>` resolves to `sum(1, n, g)`,
    // prove `\T<a> = \T<b>` by proving the resolved sums equal.
    fn try_verify_instantiated_template_obj_equality_by_resolved_values(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !matches!(left, Obj::InstantiatedTemplateObj(_))
            && !matches!(right, Obj::InstantiatedTemplateObj(_))
        {
            return Ok(None);
        }

        self.materialize_instantiated_template_obj_if_needed(left, verify_state)?;
        self.materialize_instantiated_template_obj_if_needed(right, verify_state)?;

        let mut left_candidates = self.known_equal_objs_for_template_candidate(left);
        if left_candidates.is_empty() {
            left_candidates.push(left.clone());
        }
        let mut right_candidates = self.known_equal_objs_for_template_candidate(right);
        if right_candidates.is_empty() {
            right_candidates.push(right.clone());
        }

        for left_candidate in left_candidates.iter() {
            for right_candidate in right_candidates.iter() {
                if verify_equality_by_they_are_the_same(left_candidate, left)
                    && verify_equality_by_they_are_the_same(right_candidate, right)
                {
                    continue;
                }
                let resolved_result = self.verify_objs_are_equal_in_equality_builtin(
                    left_candidate,
                    right_candidate,
                    line_file.clone(),
                    verify_state,
                )?;
                if resolved_result.is_true() {
                    return Ok(Some(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            EqualFact::new(left.clone(), right.clone(), line_file).into(),
                            "equality: instantiated template objects resolve to equal objects"
                                .to_string(),
                            vec![resolved_result],
                        )
                        .into(),
                    ));
                }
            }
        }

        Ok(None)
    }

    fn materialize_instantiated_template_obj_if_needed(
        &mut self,
        obj: &Obj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        let Obj::InstantiatedTemplateObj(template_obj) = obj else {
            return Ok(());
        };
        if !self.known_equal_objs_for_template_candidate(obj).is_empty() {
            return Ok(());
        }
        self.materialize_instantiated_template_obj(template_obj, verify_state)
    }

    fn known_equal_objs_for_template_candidate(&self, obj: &Obj) -> Vec<Obj> {
        let key = obj.to_string();
        let mut result: Vec<Obj> = Vec::new();
        for env in self.iter_environments_from_top() {
            let Some((_, equal_objs)) = env.known_equality.get(&key) else {
                continue;
            };
            for equal_obj in equal_objs.iter() {
                if !result
                    .iter()
                    .any(|seen| verify_equality_by_they_are_the_same(seen, equal_obj))
                {
                    result.push(equal_obj.clone());
                }
            }
        }
        result
    }

    // General Cartesian product definition as a canonical set-builder.
    // Example: `general_cart(I, s, g) = {f fn(t I)big_union(s): forall! a I => {f(a) $in g(a)}}`.
    fn try_verify_general_cart_set_builder_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (general_cart_side, set_builder_side) in [(left, right), (right, left)] {
            let Obj::GeneralCart(general_cart) = general_cart_side else {
                continue;
            };
            let Obj::SetBuilder(set_builder) = set_builder_side else {
                continue;
            };
            let Some(steps) = self.general_cart_set_builder_canonical_steps(
                general_cart,
                set_builder,
                line_file.clone(),
                verify_state,
            )?
            else {
                continue;
            };
            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                left,
                right,
                line_file,
                "general_cart equals its canonical set-builder definition",
                steps,
            )));
        }
        Ok(None)
    }

    fn general_cart_set_builder_canonical_steps(
        &mut self,
        general_cart: &GeneralCart,
        set_builder: &SetBuilder,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        let Obj::FnSet(fn_set) = set_builder.param_set.as_ref() else {
            return Ok(None);
        };
        if ParamGroupWithSet::number_of_params(&fn_set.body.params_def_with_set) != 1 {
            return Ok(None);
        }
        if !fn_set.body.dom_facts.is_empty() {
            return Ok(None);
        }

        let domain_set = fn_set.body.params_def_with_set[0].set_obj();
        let domain_result = self.verify_objs_are_equal_in_equality_builtin(
            domain_set,
            general_cart.index_set.as_ref(),
            line_file.clone(),
            verify_state,
        )?;
        if !domain_result.is_true() {
            return Ok(None);
        }

        let expected_ret_set: Obj = BigUnion::new(general_cart.family_set.as_ref().clone()).into();
        let ret_result = self.verify_objs_are_equal_in_equality_builtin(
            fn_set.body.ret_set.as_ref(),
            &expected_ret_set,
            line_file.clone(),
            verify_state,
        )?;
        if !ret_result.is_true() {
            return Ok(None);
        }

        if !self.general_cart_set_builder_has_canonical_pointwise_fact(
            general_cart,
            set_builder,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(None);
        }

        Ok(Some(vec![domain_result, ret_result]))
    }

    fn general_cart_set_builder_has_canonical_pointwise_fact(
        &mut self,
        general_cart: &GeneralCart,
        set_builder: &SetBuilder,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        if set_builder.facts.len() != 1 {
            return Ok(false);
        }
        let ExistBodyFact::InlineForall(forall_fact) = &set_builder.facts[0] else {
            return Ok(false);
        };
        if forall_fact.params_def_with_type.number_of_params() != 1
            || !forall_fact.dom_facts.is_empty()
            || forall_fact.then_facts.len() != 1
        {
            return Ok(false);
        }
        let ParamType::Obj(param_type) = &forall_fact.params_def_with_type.groups[0].param_type
        else {
            return Ok(false);
        };
        let param_type_result = self.verify_objs_are_equal_in_equality_builtin(
            param_type,
            general_cart.index_set.as_ref(),
            line_file,
            verify_state,
        )?;
        if !param_type_result.is_true() {
            return Ok(false);
        }

        let param_name = forall_fact.params_def_with_type.collect_param_names()[0].clone();
        let param_obj = obj_for_bound_param_in_scope(param_name, ParamObjType::Forall);
        let member_obj =
            obj_for_bound_param_in_scope(set_builder.param.clone(), ParamObjType::SetBuilder);
        let Some(member_head) = FnObjHead::from_callable_obj(member_obj) else {
            return Ok(false);
        };
        let Some(family_head) =
            FnObjHead::from_callable_obj(general_cart.family_fn.as_ref().clone())
        else {
            return Ok(false);
        };
        let expected_element: Obj =
            FnObj::new(member_head, vec![vec![Box::new(param_obj.clone())]]).into();
        let expected_set: Obj = FnObj::new(family_head, vec![vec![Box::new(param_obj)]]).into();

        let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(in_fact)) =
            &forall_fact.then_facts[0]
        else {
            return Ok(false);
        };
        Ok(
            verify_equality_by_they_are_the_same(&in_fact.element, &expected_element)
                && verify_equality_by_they_are_the_same(&in_fact.set, &expected_set),
        )
    }

    // Integer ranges are the canonical sets of integer points between their endpoints.
    // Examples: `closed_range(a, b) = {x Z: a <= x <= b}` and
    // `range(a, b) = {x Z: a <= x < b}`.
    fn try_verify_integer_range_set_builder_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Result<Option<StmtResult>, RuntimeError> {
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
            let ExistBodyFact::ChainFact(chain) = &set_builder.facts[0] else {
                continue;
            };
            let Ok(chain_facts) = chain.facts() else {
                continue;
            };
            let [AtomicFact::LessEqualFact(lower), upper] = chain_facts.as_slice() else {
                continue;
            };
            let bound_param =
                obj_for_bound_param_in_scope(set_builder.param.clone(), ParamObjType::SetBuilder);
            let (upper_left_matches, upper_right_matches) = match (right_closed, upper) {
                (true, AtomicFact::LessEqualFact(fact)) => (
                    verify_equality_by_they_are_the_same(&fact.left, &bound_param),
                    verify_equality_by_they_are_the_same(&fact.right, end),
                ),
                (false, AtomicFact::LessFact(fact)) => (
                    verify_equality_by_they_are_the_same(&fact.left, &bound_param),
                    verify_equality_by_they_are_the_same(&fact.right, end),
                ),
                _ => (false, false),
            };
            if !verify_equality_by_they_are_the_same(&lower.left, start)
                || !verify_equality_by_they_are_the_same(&lower.right, &bound_param)
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
                left, right, line_file, rule,
            )));
        }
        Ok(None)
    }

    // Sequence-shaped spaces are exactly their corresponding function spaces.
    // Example: `matrix(R, 2, 3) = fn(i, j N_pos: i <= 2, j <= 3) R`.
    fn try_verify_indexed_fn_set_definition_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
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
            let expanded_equality = self.verify_fn_set_with_params_equality_by_builtin_rules(
                &expanded,
                fn_set,
                line_file.clone(),
                verify_state,
            )?;
            if expanded_equality.is_true() {
                return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                    left,
                    right,
                    line_file,
                    rule,
                    vec![expanded_equality],
                )));
            }
        }

        Ok(None)
    }

    // Antisymmetry rule for registered user-defined props.
    // Example: from `$p(a, b)` and `$p(b, a)`, prove `a = b`.
    fn try_verify_equality_from_known_antisymmetric_props(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Result<Option<StmtResult>, RuntimeError> {
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
                self.verify_user_prop_subgoal(&prop_name, left, right, line_file.clone())?;
            if !left_to_right.is_true() {
                continue;
            }
            let right_to_left =
                self.verify_user_prop_subgoal(&prop_name, right, left, line_file.clone())?;
            if !right_to_left.is_true() {
                continue;
            }
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    EqualFact::new(left.clone(), right.clone(), line_file).into(),
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
