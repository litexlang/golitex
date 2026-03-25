use crate::calculate_and_simplify_rational_expression::objs_equal_by_rational_expression_simplification;
use crate::error::VerifyError;
use crate::execute::Runtime;
use crate::fact::{AtomicFact, EqualFact, Fact};
use crate::infer::InferResult;
use crate::obj::{FnObj, Obj};
use crate::result::FactVerifiedByBuiltinRules;
use crate::result::NonErrStmtExecResult;
use crate::result::StmtUnknown;
use crate::verify::VerifyState;
use std::rc::Rc;

impl<'a> Runtime<'a> {
    pub fn verify_equal_fact(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        self.verify_objs_are_equal(
            &equal_fact.left,
            &equal_fact.right,
            equal_fact.line_file,
            verify_state,
        )
    }

    pub fn verify_objs_are_equal(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: (usize, usize),
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let mut result = verify_equality_by_builtin_rules(self, left, right, line_file)?;
        if result.is_true() {
            return Ok(result);
        }

        result =
            self.verify_equality_with_known_equalities(left, right, line_file, verify_state)?;
        if result.is_true() {
            return Ok(result);
        }

        let verified_by_arg_to_arg = self
            .verify_objs_are_equal_when_they_have_same_builtin_shape_and_equal_args_recursively(
                left,
                right,
                verify_state,
                line_file,
            )?;
        if verified_by_arg_to_arg {
            return Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                FactVerifiedByBuiltinRules::new(
                    Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
                        left.clone(),
                        right.clone(),
                        line_file,
                    ))),
                    same_shape_and_equal_args_reason(left, right),
                    InferResult::new(),
                ),
            ));
        }

        if verify_state.is_round_0() {
            let verify_state_add_one_round = verify_state.new_state_with_round_increased();
            result = self.verify_atomic_fact_with_known_forall(
                &AtomicFact::EqualFact(EqualFact::new(left.clone(), right.clone(), line_file)),
                &verify_state_add_one_round,
            )?;
            if result.is_true() {
                return Ok(result);
            }
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn verify_equality_with_known_equalities(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: (usize, usize),
        _verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let left_string = left.to_string();
        let right_string = right.to_string();

        let known_pairs = self.collect_known_equality_pairs_from_envs(&left_string, &right_string);
        for (known_left, known_right) in known_pairs {
            if let Some(result) = try_verify_equality_with_known_equalities_by_builtin_rules_only(
                self,
                left,
                right,
                line_file,
                known_left.as_ref(),
                known_right.as_ref(),
            )? {
                return Ok(result);
            }
        }
        let known_left = self
            .runtime_context
            .builtin_environment
            .known_equality
            .get(&left_string)
            .map(Rc::clone);
        let known_right = self
            .runtime_context
            .builtin_environment
            .known_equality
            .get(&right_string)
            .map(Rc::clone);
        if let Some(result) = try_verify_equality_with_known_equalities_by_builtin_rules_only(
            self,
            left,
            right,
            line_file,
            known_left.as_ref(),
            known_right.as_ref(),
        )? {
            return Ok(result);
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    /// Collect (known_left, known_right) from each env in top-to-bottom order (last env first).
    fn collect_known_equality_pairs_from_envs(
        &self,
        left_string: &str,
        right_string: &str,
    ) -> Vec<(Option<Rc<Vec<Obj>>>, Option<Rc<Vec<Obj>>>)> {
        let mut pairs = Vec::with_capacity(self.runtime_context.environment_stack.len());
        for env in self.runtime_context.iter_environments_from_top() {
            let known_left = env.known_equality.get(left_string).map(Rc::clone);
            let known_right = env.known_equality.get(right_string).map(Rc::clone);
            pairs.push((known_left, known_right));
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
        equality_line_file: (usize, usize),
    ) -> Result<bool, VerifyError> {
        let result = self.verify_two_objs_equal_by_builtin_rules_and_known_equalities(
            left_left,
            right_left,
            verify_state,
            equality_line_file,
        )?;
        if result.is_unknown() {
            return Ok(false);
        }
        let result = self.verify_two_objs_equal_by_builtin_rules_and_known_equalities(
            left_right,
            right_right,
            verify_state,
            equality_line_file,
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
        equality_line_file: (usize, usize),
    ) -> Result<bool, VerifyError> {
        let result = self.verify_two_objs_equal_by_builtin_rules_and_known_equalities(
            left_value,
            right_value,
            verify_state,
            equality_line_file,
        )?;
        if result.is_true() {
            return Ok(true);
        }
        Ok(false)
    }

    fn verify_obj_vec_are_equal_when_all_corresponding_args_are_equal(
        &mut self,
        left_values: &Vec<Box<Obj>>,
        right_values: &Vec<Box<Obj>>,
        verify_state: &VerifyState,
        equality_line_file: (usize, usize),
    ) -> Result<bool, VerifyError> {
        if left_values.len() != right_values.len() {
            return Ok(false);
        }

        let mut current_index = 0;
        while current_index < left_values.len() {
            let result = self.verify_two_objs_equal_by_builtin_rules_and_known_equalities(
                &left_values[current_index],
                &right_values[current_index],
                verify_state,
                equality_line_file,
            )?;
            if result.is_unknown() {
                return Ok(false);
            }
            current_index += 1;
        }
        Ok(true)
    }

    fn verify_fn_objs_equal_when_they_have_same_head_and_equal_args(
        &mut self,
        left_fn_obj: &FnObj,
        right_fn_obj: &FnObj,
        verify_state: &VerifyState,
        equality_line_file: (usize, usize),
    ) -> Result<bool, VerifyError> {
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
                equality_line_file,
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
        equality_line_file: (usize, usize),
    ) -> Result<bool, VerifyError> {
        let mut remaining_left_group_count = left_fn_obj.body.len();
        let mut remaining_right_group_count = right_fn_obj.body.len();

        while remaining_left_group_count > 0 && remaining_right_group_count > 0 {
            let left_group = &left_fn_obj.body[remaining_left_group_count - 1];
            let right_group = &right_fn_obj.body[remaining_right_group_count - 1];
            if !self.verify_obj_vec_are_equal_when_all_corresponding_args_are_equal(
                left_group,
                right_group,
                verify_state,
                equality_line_file,
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
                equality_line_file,
            )?;
        Ok(remaining_equality_result.is_true())
    }

    fn verify_objs_are_equal_when_they_have_same_builtin_shape_and_equal_args_recursively(
        &mut self,
        left_obj: &Obj,
        right_obj: &Obj,
        verify_state: &VerifyState,
        equality_line_file: (usize, usize),
    ) -> Result<bool, VerifyError> {
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
            (Obj::Choose(left_choose), Obj::Choose(right_choose)) => self
                .verify_unary_objs_are_equal_when_their_only_args_are_equal(
                    &left_choose.set,
                    &right_choose.set,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::TupleDimObj(left_tuple_dim_obj), Obj::TupleDimObj(right_tuple_dim_obj)) => self
                .verify_unary_objs_are_equal_when_their_only_args_are_equal(
                    &left_tuple_dim_obj.obj,
                    &right_tuple_dim_obj.obj,
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
            (Obj::Dim(left_dim), Obj::Dim(right_dim)) => self
                .verify_unary_objs_are_equal_when_their_only_args_are_equal(
                    &left_dim.dim,
                    &right_dim.dim,
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
            (Obj::Val(left_val), Obj::Val(right_val)) => self
                .verify_unary_objs_are_equal_when_their_only_args_are_equal(
                    &left_val.value,
                    &right_val.value,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::Range(left_range), Obj::Range(right_range)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_range.start,
                    &left_range.end,
                    &right_range.start,
                    &right_range.end,
                    verify_state,
                    equality_line_file,
                ),
            (Obj::ClosedRange(left_closed_range), Obj::ClosedRange(right_closed_range)) => self
                .verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left_closed_range.start,
                    &left_closed_range.end,
                    &right_closed_range.start,
                    &right_closed_range.end,
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
                    &left_tuple.elements,
                    &right_tuple.elements,
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
        equality_line_file: (usize, usize),
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let mut result =
            verify_equality_by_builtin_rules(self, left_obj, right_obj, equality_line_file)?;
        if result.is_true() {
            return Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                FactVerifiedByBuiltinRules::new(
                    Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
                        left_obj.clone(),
                        right_obj.clone(),
                        equality_line_file,
                    ))),
                    "builtin rules".to_string(),
                    InferResult::new(),
                ),
            ));
        }

        result = self.verify_equality_with_known_equalities(
            left_obj,
            right_obj,
            equality_line_file,
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
                equality_line_file,
            )?;
        if verified_by_arg_to_arg {
            return Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                FactVerifiedByBuiltinRules::new(
                    Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
                        left_obj.clone(),
                        right_obj.clone(),
                        equality_line_file,
                    ))),
                    same_shape_and_equal_args_reason(left_obj, right_obj),
                    InferResult::new(),
                ),
            ));
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }
}

pub fn verify_equality_by_they_are_the_same(left: &Obj, right: &Obj) -> bool {
    if left.to_string() == right.to_string() {
        return true;
    }
    false
}

fn verify_equality_by_builtin_rules(
    runtime: &Runtime<'_>,
    left: &Obj,
    right: &Obj,
    line_file: (usize, usize),
) -> Result<NonErrStmtExecResult, VerifyError> {
    if verify_equality_by_they_are_the_same(left, right) {
        return Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
            FactVerifiedByBuiltinRules::new(
                Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
                    left.clone(),
                    right.clone(),
                    line_file,
                ))),
                "the same".to_string(),
                InferResult::new(),
            ),
        ));
    }

    let left_for_numeric_verification =
        runtime.obj_with_runtime_known_numbers_substituted_for_verification(left);
    let right_for_numeric_verification =
        runtime.obj_with_runtime_known_numbers_substituted_for_verification(right);

    if left_for_numeric_verification
        .two_objs_can_be_calculated_and_equal_by_calculation(&right_for_numeric_verification)
    {
        return Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
            FactVerifiedByBuiltinRules::new(
                Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
                    left.clone(),
                    right.clone(),
                    line_file,
                ))),
                "calculation".to_string(),
                InferResult::new(),
            ),
        ));
    }

    if objs_equal_by_rational_expression_simplification(
        &left_for_numeric_verification,
        &right_for_numeric_verification,
    ) {
        return Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
            FactVerifiedByBuiltinRules::new(
                Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
                    left.clone(),
                    right.clone(),
                    line_file,
                ))),
                "rational expression simplification".to_string(),
                InferResult::new(),
            ),
        ));
    }

    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
}

fn try_verify_equality_with_known_equalities_by_builtin_rules_only(
    runtime: &Runtime<'_>,
    left: &Obj,
    right: &Obj,
    line_file: (usize, usize),
    known_objs_equal_to_left: Option<&Rc<Vec<Obj>>>,
    known_objs_equal_to_right: Option<&Rc<Vec<Obj>>>,
) -> Result<Option<NonErrStmtExecResult>, VerifyError> {
    match (known_objs_equal_to_left, known_objs_equal_to_right) {
        (None, None) => Ok(None),
        (Some(known_objs_equal_to_left), None) => {
            for obj in known_objs_equal_to_left.iter() {
                let result = verify_equality_by_builtin_rules(runtime, obj, right, line_file)?;
                if result.is_true() {
                    return Ok(Some(result));
                }
            }
            Ok(None)
        }
        (None, Some(known_objs_equal_to_right)) => {
            for obj in known_objs_equal_to_right.iter() {
                let result = verify_equality_by_builtin_rules(runtime, left, obj, line_file)?;
                if result.is_true() {
                    return Ok(Some(result));
                }
            }
            Ok(None)
        }
        (Some(known_objs_equal_to_left), Some(known_objs_equal_to_right)) => {
            for obj1 in known_objs_equal_to_left.iter() {
                for obj2 in known_objs_equal_to_right.iter() {
                    let result = verify_equality_by_builtin_rules(runtime, obj1, obj2, line_file)?;
                    if result.is_true() {
                        return Ok(Some(result));
                    }
                }
            }
            Ok(None)
        }
    }
}

fn fn_obj_prefix_to_obj(fn_obj: &FnObj, number_of_body_groups_to_keep: usize) -> Obj {
    if number_of_body_groups_to_keep == 0 {
        return Obj::from(fn_obj.head.as_ref().clone());
    }

    let mut kept_body_groups: Vec<Vec<Box<Obj>>> = Vec::new();
    let mut current_group_index = 0;
    while current_group_index < number_of_body_groups_to_keep {
        kept_body_groups.push(fn_obj.body[current_group_index].clone());
        current_group_index += 1;
    }

    Obj::FnObj(FnObj::new(fn_obj.head.as_ref().clone(), kept_body_groups))
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
