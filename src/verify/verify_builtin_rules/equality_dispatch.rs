use crate::prelude::*;
use crate::verify::verify_equality_by_builtin_rules::{
    factual_equal_success_by_builtin_reason, verify_equality_by_they_are_the_same,
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

        if let Some(done) = self.try_verify_set_minus_equalities(left, right, line_file.clone()) {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_cart_count_product_equality(left, right, line_file.clone())
        {
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

        if let Some(done) =
            self.try_verify_equality_from_known_antisymmetric_props(left, right, line_file.clone())?
        {
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
        if let Some(done) =
            self.try_verify_empty_set_equality_from_not_nonempty(left, right, line_file.clone())?
        {
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

        if let Some(done) = self.try_verify_tuple_equality_from_dim_and_projections(
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

    fn try_verify_cart_count_product_equality(
        &self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Option<StmtResult> {
        // Cardinality of a finite Cartesian product is the product of factor cardinalities.
        // Example: `count(cart(A, B)) = count(A) * count(B)`.
        if Self::cart_count_product_shape(left, right)
            || Self::cart_count_product_shape(right, left)
        {
            return Some(Self::set_equality_success(
                left,
                right,
                line_file,
                "cart_count_product",
            ));
        }

        None
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

    fn cart_count_product_shape(count_side: &Obj, product_side: &Obj) -> bool {
        let Obj::Count(count) = count_side else {
            return false;
        };
        let Obj::Cart(cart) = count.set.as_ref() else {
            return false;
        };
        let Some(expected_product) = Self::count_product_for_cart_args(&cart.args) else {
            return false;
        };
        verify_equality_by_they_are_the_same(&expected_product, product_side)
    }

    fn count_product_for_cart_args(args: &[Box<Obj>]) -> Option<Obj> {
        let mut iter = args.iter();
        let first = iter.next()?;
        let mut product: Obj = Count::new(first.as_ref().clone()).into();
        for arg in iter {
            let factor_count: Obj = Count::new(arg.as_ref().clone()).into();
            product = Mul::new(product, factor_count).into();
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
        if self.loading_builtin_code {
            return Ok(None);
        }

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
            let component_result = self
                .verify_atomic_fact_known_then_builtin_rules_only(&component_fact, verify_state)?;
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

    fn try_verify_empty_set_equality_from_not_nonempty(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let set = match (left, right) {
            (Obj::ListSet(list), set) if list.list.is_empty() => set.clone(),
            (set, Obj::ListSet(list)) if list.list.is_empty() => set.clone(),
            _ => return Ok(None),
        };

        let not_nonempty: AtomicFact = NotIsNonemptySetFact::new(set, line_file.clone()).into();
        let sub = self.verify_non_equational_atomic_fact_with_known_atomic_facts(&not_nonempty)?;
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
        let Some(left_ge_right) = self.verify_weak_order_subgoal(left, right, line_file.clone())?
        else {
            return Ok(None);
        };
        let Some(right_ge_left) = self.verify_weak_order_subgoal(right, left, line_file.clone())?
        else {
            return Ok(None);
        };

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "equality from a >= b and b >= a".to_string(),
                vec![left_ge_right, right_ge_left],
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
