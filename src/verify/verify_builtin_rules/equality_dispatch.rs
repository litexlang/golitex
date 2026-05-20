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

        if let Some(done) = self.try_verify_objs_equal_by_expanding_family(
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

        if let Some(done) = self.try_verify_power_addition_exponent_rule(
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
            self.try_verify_log_equals_by_pow_inverse(left, right, line_file.clone(), verify_state)?
        {
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
        self.verify_non_equational_atomic_fact(&fact, &VerifyState::new(0, true), true)
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
