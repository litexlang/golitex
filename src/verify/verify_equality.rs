use crate::prelude::*;
use std::rc::Rc;

impl Runtime {
    pub fn verify_equal_fact(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        self.verify_objs_are_equal(
            &equal_fact.left,
            &equal_fact.right,
            equal_fact.line_file.clone(),
            verify_state,
        )
    }

    pub fn verify_objs_are_equal(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(done) =
            self.try_verify_function_equality_from_known_fn_eq(left, right, line_file.clone())?
        {
            return Ok(done);
        }

        let mut result =
            self.verify_equality_by_builtin_rules(left, right, line_file.clone(), verify_state)?;
        if result.is_true() {
            return Ok(result);
        }

        result = self.verify_objs_are_equal_known_only(left, right, line_file.clone());
        if result.is_true() {
            return Ok(result);
        }

        result = self.verify_equality_with_known_equalities(
            left,
            right,
            line_file.clone(),
            verify_state,
        )?;
        if result.is_true() {
            return Ok(result);
        }

        let verified_by_arg_to_arg = self
            .verify_objs_are_equal_when_they_have_same_builtin_shape_and_equal_args_recursively(
                left,
                right,
                verify_state,
                line_file.clone(),
            )?;
        if verified_by_arg_to_arg {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    EqualFact::new(left.clone(), right.clone(), line_file.clone()).into(),
                    same_shape_and_equal_args_reason(left, right),
                    Vec::new(),
                ))
                .into(),
            );
        }

        if let Some(done) = self.try_verify_anonymous_functions_equal_by_fn_eq(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if verify_state.is_round_0() && verify_state.equality_can_use_known_forall {
            let verify_state_add_one_round = verify_state.new_state_with_round_increased();
            result = self.verify_atomic_fact_with_known_forall(
                &EqualFact::new(left.clone(), right.clone(), line_file.clone()).into(),
                &verify_state_add_one_round,
            )?;
            if result.is_true() {
                return Ok(result);
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    // Function extensionality bridge from an already proved `$fn_eq`.
    // Example: after `$fn_eq(f, g)`, prove the ordinary equality `f = g`.
    fn try_verify_function_equality_from_known_fn_eq(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let direct = FnEqualFact::new(left.clone(), right.clone(), line_file.clone());
        if let Some(done) =
            self.try_verify_function_equality_from_one_known_fn_eq(left, right, &direct)?
        {
            return Ok(Some(done));
        }

        let reversed = FnEqualFact::new(right.clone(), left.clone(), line_file.clone());
        self.try_verify_function_equality_from_one_known_fn_eq(left, right, &reversed)
    }

    fn try_verify_function_equality_from_one_known_fn_eq(
        &mut self,
        left: &Obj,
        right: &Obj,
        fn_eq_fact: &FnEqualFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let fn_eq_atomic: AtomicFact = fn_eq_fact.clone().into();
        let fn_eq_result =
            self.verify_non_equational_atomic_fact_with_known_atomic_facts(&fn_eq_atomic)?;
        if !fn_eq_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), fn_eq_fact.line_file.clone()).into(),
                "function equality from known fn_eq".to_string(),
                vec![fn_eq_result],
            )
            .into(),
        ))
    }

    fn try_verify_anonymous_functions_equal_by_fn_eq(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !matches!((left, right), (Obj::AnonymousFn(_), Obj::AnonymousFn(_))) {
            return Ok(None);
        }

        // Function extensionality for anonymous function values.
        // Example: `fn(x R) R {f(x) + g(x)} = fn(y R) R {g(y) + f(y)}` follows from
        // the existing `$fn_eq` pointwise equality verifier.
        let fn_eq_fact = FnEqualFact::new(left.clone(), right.clone(), line_file.clone());
        let fn_eq_result =
            self.verify_fn_equal_fact_with_builtin_rules(&fn_eq_fact, verify_state)?;
        if !fn_eq_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "anonymous fn equality: pointwise function equality".to_string(),
                vec![fn_eq_result],
            )
            .into(),
        ))
    }

    pub(crate) fn verify_equality_with_known_equalities(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let left_string = left.to_string();
        let right_string = right.to_string();

        let known_pairs =
            self.collect_known_equality_pairs_from_envs(&left_string, &right_string, left, right);
        for (known_left, known_right) in known_pairs {
            if let Some(result) = self
                .try_verify_equality_with_known_equalities_by_builtin_rules_only(
                    left,
                    right,
                    line_file.clone(),
                    verify_state,
                    known_left.as_ref(),
                    known_right.as_ref(),
                )?
            {
                return Ok(result);
            }
        }

        if let Some(done) = self.try_verify_objs_equal_via_user_defined_fn_definition_substitution(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        Ok((StmtUnknown::new()).into())
    }

    /// Stored `have fn` body (`KnownFnInfo.equal_to`): unfold one application and compare.
    fn try_verify_objs_equal_via_user_defined_fn_definition_substitution(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(done) = self.try_one_side_user_defined_fn_app_equals_other_side(
            left,
            right,
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(Some(done));
        }
        if let Some(done) = self.try_one_side_user_defined_fn_app_equals_other_side(
            left,
            right,
            right,
            left,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(Some(done));
        }
        Ok(None)
    }

    fn try_one_side_user_defined_fn_app_equals_other_side(
        &mut self,
        statement_left: &Obj,
        statement_right: &Obj,
        application_side: &Obj,
        other_side: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(reduced) =
            self.unfold_known_fn_application_once(application_side, verify_state)?
        else {
            return Ok(None);
        };
        let inner = self.verify_objs_are_equal_in_equality_builtin(
            &reduced,
            other_side,
            line_file.clone(),
            verify_state,
        )?;
        if !inner.is_true() {
            return Ok(None);
        }
        let fact: Fact = EqualFact::new(
            statement_left.clone(),
            statement_right.clone(),
            line_file.clone(),
        )
        .into();
        let msg = format!(
            "according to user-defined function `{}` = `{}`",
            application_side, reduced
        );
        let cited = fact.clone();
        let verified_by = VerifiedByResult::cited_fact(fact.clone(), cited, Some(msg));
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_known_fact(fact, verified_by, Vec::new())
                .into(),
        ))
    }

    /// Build equality closures without merging the underlying environments.
    fn collect_known_equality_pairs_from_envs(
        &self,
        left_string: &str,
        right_string: &str,
        left: &Obj,
        right: &Obj,
    ) -> Vec<(Option<Rc<Vec<Obj>>>, Option<Rc<Vec<Obj>>>)> {
        let current_environments = self.iter_environments_from_top().collect::<Vec<_>>();
        let mut pairs = vec![(
            known_equality_class_across_environments(
                &current_environments,
                &[left_string.to_string()],
            ),
            known_equality_class_across_environments(
                &current_environments,
                &[right_string.to_string()],
            ),
        )];
        let mut module_names = self.obj_referenced_module_names(left);
        for module_name in self.obj_referenced_module_names(right) {
            if !module_names
                .iter()
                .any(|existing_module_name| existing_module_name == &module_name)
            {
                module_names.push(module_name);
            }
        }
        for module_name in module_names.iter() {
            let environments = self.active_imported_module_environments(module_name);
            if environments.is_empty() {
                continue;
            }
            let left_keys =
                equality_lookup_keys_for_module_env(left, left_string, module_name.as_str());
            let right_keys =
                equality_lookup_keys_for_module_env(right, right_string, module_name.as_str());
            pairs.push((
                known_equality_class_across_environments(&environments, &left_keys),
                known_equality_class_across_environments(&environments, &right_keys),
            ));
        }
        pairs
    }

    fn verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        right_left: &Obj,
        right_right: &Obj,
        verify_state: &VerifyState,
        equality_line_file: LineFile,
    ) -> Result<bool, RuntimeError> {
        let result = self.verify_two_objs_equal_by_builtin_rules_and_known_equalities(
            left_left,
            right_left,
            verify_state,
            equality_line_file.clone(),
        )?;
        if result.is_unknown() {
            return Ok(false);
        }
        let result = self.verify_two_objs_equal_by_builtin_rules_and_known_equalities(
            left_right,
            right_right,
            verify_state,
            equality_line_file.clone(),
        )?;
        if result.is_unknown() {
            return Ok(false);
        }
        Ok(true)
    }

    fn verify_unary_objs_are_equal_when_their_only_args_are_equal(
        &mut self,
        left_value: &Obj,
        right_value: &Obj,
        verify_state: &VerifyState,
        equality_line_file: LineFile,
    ) -> Result<bool, RuntimeError> {
        let result = self.verify_two_objs_equal_by_builtin_rules_and_known_equalities(
            left_value,
            right_value,
            verify_state,
            equality_line_file.clone(),
        )?;
        if result.is_true() {
            return Ok(true);
        }
        Ok(false)
    }

    fn verify_function_args_are_equal_for_iterated_operator(
        &mut self,
        left_func: &Obj,
        right_func: &Obj,
        verify_state: &VerifyState,
        equality_line_file: LineFile,
    ) -> Result<bool, RuntimeError> {
        // Iterated operators such as sum/product compare their summand
        // functions extensionally. Example:
        // `sum(1, n, fn(x Z) Z {f(x)}) = sum(1, n, fn(y Z) Z {f(y)})`.
        let fn_eq_fact = FnEqualFact::new(
            left_func.clone(),
            right_func.clone(),
            equality_line_file.clone(),
        );
        let fn_eq_result =
            self.verify_fn_equal_fact_with_builtin_rules(&fn_eq_fact, verify_state)?;
        if fn_eq_result.is_true() {
            return Ok(true);
        }

        self.verify_unary_objs_are_equal_when_their_only_args_are_equal(
            left_func,
            right_func,
            verify_state,
            equality_line_file,
        )
    }

    fn verify_obj_vec_are_equal_when_all_corresponding_args_are_equal(
        &mut self,
        left_values: &Vec<Box<Obj>>,
        right_values: &Vec<Box<Obj>>,
        verify_state: &VerifyState,
        equality_line_file: LineFile,
    ) -> Result<bool, RuntimeError> {
        if left_values.len() != right_values.len() {
            return Ok(false);
        }

        let mut current_index = 0;
        while current_index < left_values.len() {
            let result = self.verify_two_objs_equal_by_builtin_rules_and_known_equalities(
                &left_values[current_index],
                &right_values[current_index],
                verify_state,
                equality_line_file.clone(),
            )?;
            if result.is_unknown() {
                return Ok(false);
            }
            current_index += 1;
        }
        Ok(true)
    }

    fn verify_matrix_list_objs_equal_when_all_cells_equal(
        &mut self,
        left: &MatrixListObj,
        right: &MatrixListObj,
        verify_state: &VerifyState,
        equality_line_file: LineFile,
    ) -> Result<bool, RuntimeError> {
        if left.rows.len() != right.rows.len() {
            return Ok(false);
        }
        for (lr, rr) in left.rows.iter().zip(right.rows.iter()) {
            if !self.verify_obj_vec_are_equal_when_all_corresponding_args_are_equal(
                lr,
                rr,
                verify_state,
                equality_line_file.clone(),
            )? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn verify_fn_objs_equal_when_they_have_same_head_and_equal_args(
        &mut self,
        left_fn_obj: &FnObj,
        right_fn_obj: &FnObj,
        verify_state: &VerifyState,
        equality_line_file: LineFile,
    ) -> Result<bool, RuntimeError> {
        if left_fn_obj.body.len() != right_fn_obj.body.len() {
            return Ok(false);
        }

        if left_fn_obj.head.to_string() != right_fn_obj.head.to_string() {
            return Ok(false);
        }

        for (left_group, right_group) in left_fn_obj.body.iter().zip(right_fn_obj.body.iter()) {
            let result = self.verify_obj_vec_are_equal_when_all_corresponding_args_are_equal(
                left_group,
                right_group,
                verify_state,
                equality_line_file.clone(),
            )?;
            if !result {
                return Ok(false);
            }
        }

        Ok(true)
    }

    fn verify_fn_objs_are_equal_when_their_body_groups_match_from_right_to_left(
        &mut self,
        left_fn_obj: &FnObj,
        right_fn_obj: &FnObj,
        verify_state: &VerifyState,
        equality_line_file: LineFile,
    ) -> Result<bool, RuntimeError> {
        let mut remaining_left_group_count = left_fn_obj.body.len();
        let mut remaining_right_group_count = right_fn_obj.body.len();

        while remaining_left_group_count > 0 && remaining_right_group_count > 0 {
            let left_group = &left_fn_obj.body[remaining_left_group_count - 1];
            let right_group = &right_fn_obj.body[remaining_right_group_count - 1];
            if !self.verify_obj_vec_are_equal_when_all_corresponding_args_are_equal(
                left_group,
                right_group,
                verify_state,
                equality_line_file.clone(),
            )? {
                return Ok(false);
            }
            remaining_left_group_count -= 1;
            remaining_right_group_count -= 1;
        }

        let remaining_left_obj = fn_obj_prefix_to_obj(left_fn_obj, remaining_left_group_count);
        let remaining_right_obj = fn_obj_prefix_to_obj(right_fn_obj, remaining_right_group_count);
        let remaining_equality_result = self
            .verify_two_objs_equal_by_builtin_rules_and_known_equalities(
                &remaining_left_obj,
                &remaining_right_obj,
                verify_state,
                equality_line_file.clone(),
            )?;
        Ok(remaining_equality_result.is_true())
    }

    pub(crate) fn verify_objs_are_equal_when_they_have_same_builtin_shape_and_equal_args_recursively(
        &mut self,
        left_obj: &Obj,
        right_obj: &Obj,
        verify_state: &VerifyState,
        equality_line_file: LineFile,
    ) -> Result<bool, RuntimeError> {
        match (left_obj, right_obj) {
            (Obj::FnObj(left_fn_obj), Obj::FnObj(right_fn_obj)) => {
                if left_fn_obj.body.len() == right_fn_obj.body.len()
                    && left_fn_obj.head.to_string() == right_fn_obj.head.to_string()
                {
                    self.verify_fn_objs_equal_when_they_have_same_head_and_equal_args(
                        left_fn_obj,
                        right_fn_obj,
                        verify_state,
                        equality_line_file,
                    )
                } else {
                    self.verify_fn_objs_are_equal_when_their_body_groups_match_from_right_to_left(
                        left_fn_obj,
                        right_fn_obj,
                        verify_state,
                        equality_line_file,
                    )
                }
            }
            (Obj::Add(left_add), Obj::Add(right_add)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_add.left,
                    &left_add.right,
                    &right_add.left,
                    &right_add.right,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::Sub(left_sub), Obj::Sub(right_sub)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_sub.left,
                    &left_sub.right,
                    &right_sub.left,
                    &right_sub.right,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::Mul(left_mul), Obj::Mul(right_mul)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_mul.left,
                    &left_mul.right,
                    &right_mul.left,
                    &right_mul.right,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::Div(left_div), Obj::Div(right_div)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_div.left,
                    &left_div.right,
                    &right_div.left,
                    &right_div.right,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::Mod(left_mod), Obj::Mod(right_mod)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_mod.left,
                    &left_mod.right,
                    &right_mod.left,
                    &right_mod.right,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::Pow(left_pow), Obj::Pow(right_pow)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_pow.base,
                    &left_pow.exponent,
                    &right_pow.base,
                    &right_pow.exponent,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::Abs(left_abs), Obj::Abs(right_abs)) => self
                .verify_unary_objs_are_equal_when_their_only_args_are_equal(
                    &left_abs.arg,
                    &right_abs.arg,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::Sqrt(left_sqrt), Obj::Sqrt(right_sqrt)) => self
                .verify_unary_objs_are_equal_when_their_only_args_are_equal(
                    &left_sqrt.arg,
                    &right_sqrt.arg,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::Log(left_log), Obj::Log(right_log)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_log.base,
                    &left_log.arg,
                    &right_log.base,
                    &right_log.arg,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::MatrixAdd(left_m), Obj::MatrixAdd(right_m)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_m.left,
                    &left_m.right,
                    &right_m.left,
                    &right_m.right,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::MatrixSub(left_m), Obj::MatrixSub(right_m)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_m.left,
                    &left_m.right,
                    &right_m.left,
                    &right_m.right,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::MatrixMul(left_m), Obj::MatrixMul(right_m)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_m.left,
                    &left_m.right,
                    &right_m.left,
                    &right_m.right,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::MatrixScalarMul(left_m), Obj::MatrixScalarMul(right_m)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_m.scalar,
                    &left_m.matrix,
                    &right_m.scalar,
                    &right_m.matrix,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::MatrixPow(left_m), Obj::MatrixPow(right_m)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_m.base,
                    &left_m.exponent,
                    &right_m.base,
                    &right_m.exponent,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::Max(left_max), Obj::Max(right_max)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_max.left,
                    &left_max.right,
                    &right_max.left,
                    &right_max.right,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::Min(left_min), Obj::Min(right_min)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_min.left,
                    &left_min.right,
                    &right_min.left,
                    &right_min.right,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::Union(left_union), Obj::Union(right_union)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_union.left,
                    &left_union.right,
                    &right_union.left,
                    &right_union.right,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::Intersect(left_intersect), Obj::Intersect(right_intersect)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_intersect.left,
                    &left_intersect.right,
                    &right_intersect.left,
                    &right_intersect.right,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::SetMinus(left_set_minus), Obj::SetMinus(right_set_minus)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_set_minus.left,
                    &left_set_minus.right,
                    &right_set_minus.left,
                    &right_set_minus.right,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::SetDiff(left_set_diff), Obj::SetDiff(right_set_diff)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_set_diff.left,
                    &left_set_diff.right,
                    &right_set_diff.left,
                    &right_set_diff.right,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::Cup(left_cup), Obj::Cup(right_cup)) => self
                .verify_unary_objs_are_equal_when_their_only_args_are_equal(
                    &left_cup.left,
                    &right_cup.left,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::Cap(left_cap), Obj::Cap(right_cap)) => self
                .verify_unary_objs_are_equal_when_their_only_args_are_equal(
                    &left_cap.left,
                    &right_cap.left,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::PowerSet(left_power_set), Obj::PowerSet(right_power_set)) => self
                .verify_unary_objs_are_equal_when_their_only_args_are_equal(
                    &left_power_set.set,
                    &right_power_set.set,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::CartDim(left_cart_dim), Obj::CartDim(right_cart_dim)) => self
                .verify_unary_objs_are_equal_when_their_only_args_are_equal(
                    &left_cart_dim.set,
                    &right_cart_dim.set,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::TupleDim(left_dim), Obj::TupleDim(right_dim)) => self
                .verify_unary_objs_are_equal_when_their_only_args_are_equal(
                    &left_dim.arg,
                    &right_dim.arg,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::Count(left_count), Obj::Count(right_count)) => self
                .verify_unary_objs_are_equal_when_their_only_args_are_equal(
                    &left_count.set,
                    &right_count.set,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::FnRange(left_range), Obj::FnRange(right_range)) => self
                .verify_unary_objs_are_equal_when_their_only_args_are_equal(
                    &left_range.function,
                    &right_range.function,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::FnRangeOn(left_range), Obj::FnRangeOn(right_range)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_range.function,
                    &left_range.set,
                    &right_range.function,
                    &right_range.set,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::Replacement(left_replacement), Obj::Replacement(right_replacement)) => {
                if left_replacement.prop_name.to_string() != right_replacement.prop_name.to_string()
                {
                    Ok(false)
                } else {
                    self.verify_unary_objs_are_equal_when_their_only_args_are_equal(
                        &left_replacement.source_set,
                        &right_replacement.source_set,
                        verify_state,
                        equality_line_file,
                    )
                }
            }
            (Obj::Range(left_range), Obj::Range(right_range)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_range.start,
                    &left_range.end,
                    &right_range.start,
                    &right_range.end,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::Sum(ls), Obj::Sum(rs)) => {
                if !self.verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &ls.start,
                    &ls.end,
                    &rs.start,
                    &rs.end,
                    verify_state,
                    equality_line_file.clone(),
                )? {
                    return Ok(false);
                }
                self.verify_function_args_are_equal_for_iterated_operator(
                    ls.func.as_ref(),
                    rs.func.as_ref(),
                    verify_state,
                    equality_line_file,
                )
            }
            (Obj::SumOfFiniteSet(ls), Obj::SumOfFiniteSet(rs)) => {
                if !self
                    .verify_two_objs_equal_by_builtin_rules_and_known_equalities(
                        ls.set.as_ref(),
                        rs.set.as_ref(),
                        verify_state,
                        equality_line_file.clone(),
                    )?
                    .is_true()
                {
                    return Ok(false);
                }
                self.verify_function_args_are_equal_for_iterated_operator(
                    ls.func.as_ref(),
                    rs.func.as_ref(),
                    verify_state,
                    equality_line_file,
                )
            }
            (Obj::ProductOfFiniteSet(ls), Obj::ProductOfFiniteSet(rs)) => {
                if !self
                    .verify_two_objs_equal_by_builtin_rules_and_known_equalities(
                        ls.set.as_ref(),
                        rs.set.as_ref(),
                        verify_state,
                        equality_line_file.clone(),
                    )?
                    .is_true()
                {
                    return Ok(false);
                }
                self.verify_function_args_are_equal_for_iterated_operator(
                    ls.func.as_ref(),
                    rs.func.as_ref(),
                    verify_state,
                    equality_line_file,
                )
            }
            (Obj::Product(ls), Obj::Product(rs)) => {
                if !self.verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &ls.start,
                    &ls.end,
                    &rs.start,
                    &rs.end,
                    verify_state,
                    equality_line_file.clone(),
                )? {
                    return Ok(false);
                }
                self.verify_function_args_are_equal_for_iterated_operator(
                    ls.func.as_ref(),
                    rs.func.as_ref(),
                    verify_state,
                    equality_line_file,
                )
            }
            (Obj::ClosedRange(left_closed_range), Obj::ClosedRange(right_closed_range)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_closed_range.start,
                    &left_closed_range.end,
                    &right_closed_range.start,
                    &right_closed_range.end,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::FiniteSeqSet(left_fs), Obj::FiniteSeqSet(right_fs)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_fs.set,
                    &left_fs.n,
                    &right_fs.set,
                    &right_fs.n,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::SeqSet(left_s), Obj::SeqSet(right_s)) => self
                .verify_unary_objs_are_equal_when_their_only_args_are_equal(
                    left_s.set.as_ref(),
                    right_s.set.as_ref(),
                    verify_state,
                    equality_line_file,
                ),
            (Obj::FiniteSeqListObj(left_v), Obj::FiniteSeqListObj(right_v)) => self
                .verify_obj_vec_are_equal_when_all_corresponding_args_are_equal(
                    &left_v.objs,
                    &right_v.objs,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::MatrixSet(left_m), Obj::MatrixSet(right_m)) => {
                if !self.verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_m.set,
                    &left_m.row_len,
                    &right_m.set,
                    &right_m.row_len,
                    verify_state,
                    equality_line_file.clone(),
                )? {
                    return Ok(false);
                }
                let result = self.verify_two_objs_equal_by_builtin_rules_and_known_equalities(
                    &left_m.col_len,
                    &right_m.col_len,
                    verify_state,
                    equality_line_file,
                )?;
                if result.is_unknown() {
                    return Ok(false);
                }
                Ok(true)
            }
            (Obj::MatrixListObj(left_m), Obj::MatrixListObj(right_m)) => self
                .verify_matrix_list_objs_equal_when_all_cells_equal(
                    left_m,
                    right_m,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::Proj(left_proj), Obj::Proj(right_proj)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_proj.set,
                    &left_proj.dim,
                    &right_proj.set,
                    &right_proj.dim,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::ObjAtIndex(left_obj_at_index), Obj::ObjAtIndex(right_obj_at_index)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_obj_at_index.obj,
                    &left_obj_at_index.index,
                    &right_obj_at_index.obj,
                    &right_obj_at_index.index,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::Tuple(left_tuple), Obj::Tuple(right_tuple)) => self
                .verify_obj_vec_are_equal_when_all_corresponding_args_are_equal(
                    &left_tuple.args,
                    &right_tuple.args,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::ListSet(left_list_set), Obj::ListSet(right_list_set)) => self
                .verify_obj_vec_are_equal_when_all_corresponding_args_are_equal(
                    &left_list_set.list,
                    &right_list_set.list,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::Cart(left_cart), Obj::Cart(right_cart)) => self
                .verify_obj_vec_are_equal_when_all_corresponding_args_are_equal(
                    &left_cart.args,
                    &right_cart.args,
                    verify_state,
                    equality_line_file,
                ),
            _ => Ok(false),
        }
    }

    fn verify_two_objs_equal_by_builtin_rules_and_known_equalities(
        &mut self,
        left_obj: &Obj,
        right_obj: &Obj,
        verify_state: &VerifyState,
        equality_line_file: LineFile,
    ) -> Result<StmtResult, RuntimeError> {
        let mut result = self.verify_equality_by_builtin_rules(
            left_obj,
            right_obj,
            equality_line_file.clone(),
            verify_state,
        )?;
        if result.is_true() {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    EqualFact::new(
                        left_obj.clone(),
                        right_obj.clone(),
                        equality_line_file.clone(),
                    )
                    .into(),
                    "builtin rules".to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }

        result = self.verify_equality_with_known_equalities(
            left_obj,
            right_obj,
            equality_line_file.clone(),
            verify_state,
        )?;
        if result.is_true() {
            return Ok(result);
        }

        let verified_by_arg_to_arg = self
            .verify_objs_are_equal_when_they_have_same_builtin_shape_and_equal_args_recursively(
                left_obj,
                right_obj,
                verify_state,
                equality_line_file.clone(),
            )?;
        if verified_by_arg_to_arg {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    EqualFact::new(left_obj.clone(), right_obj.clone(), equality_line_file).into(),
                    same_shape_and_equal_args_reason(left_obj, right_obj),
                    Vec::new(),
                ))
                .into(),
            );
        }

        Ok((StmtUnknown::new()).into())
    }
}

fn equality_lookup_keys_for_module_env(
    obj: &Obj,
    default_key: &str,
    module_name: &str,
) -> Vec<String> {
    let mut keys = vec![default_key.to_string()];
    if let Obj::Atom(AtomObj::IdentifierWithMod(identifier)) = obj {
        if identifier.mod_name == module_name {
            keys.push(identifier.name.clone());
        }
    }
    keys
}

fn known_equality_class_across_environments(
    environments: &[&Environment],
    initial_keys: &[String],
) -> Option<Rc<Vec<Obj>>> {
    let mut keys = initial_keys.to_vec();
    let mut objects = Vec::new();
    let mut next_index = 0;
    let mut found_equality = false;

    while next_index < keys.len() {
        let current = keys[next_index].clone();
        next_index += 1;
        for environment in environments {
            let Some((_, equivalent_objects)) = environment.known_equality.get(&current) else {
                continue;
            };
            found_equality = true;
            for object in equivalent_objects.iter() {
                let object_key = object.to_string();
                if !keys.contains(&object_key) {
                    keys.push(object_key.clone());
                }
                if !objects
                    .iter()
                    .any(|known: &Obj| known.to_string() == object_key)
                {
                    objects.push(object.clone());
                }
            }
        }
    }

    if found_equality {
        Some(Rc::new(objects))
    } else {
        None
    }
}

fn fn_obj_prefix_to_obj(fn_obj: &FnObj, number_of_body_groups_to_keep: usize) -> Obj {
    if number_of_body_groups_to_keep == 0 {
        return fn_obj.head.as_ref().clone().into();
    }

    let mut kept_body_groups: Vec<Vec<Box<Obj>>> = Vec::new();
    let mut current_group_index = 0;
    while current_group_index < number_of_body_groups_to_keep {
        kept_body_groups.push(fn_obj.body[current_group_index].clone());
        current_group_index += 1;
    }

    FnObj::new(fn_obj.head.as_ref().clone(), kept_body_groups).into()
}

fn same_shape_and_equal_args_reason(left_obj: &Obj, right_obj: &Obj) -> String {
    match (left_obj, right_obj) {
        (Obj::FnObj(_), Obj::FnObj(_)) => {
            "the function parts are equal, and the function arguments are equal one by one"
                .to_string()
        }
        _ => "the corresponding builtin-object arguments are equal one by one".to_string(),
    }
}
