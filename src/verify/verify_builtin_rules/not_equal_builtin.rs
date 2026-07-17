use crate::prelude::*;
use crate::verify::verify_number_in_standard_set::is_integer_after_simplification;

impl Runtime {
    pub fn _verify_not_equal_fact_with_builtin_rules(
        &mut self,
        not_equal_fact: &NotEqualFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let left_obj = &not_equal_fact.left;
        let right_obj = &not_equal_fact.right;

        match (
            self.resolve_obj_to_number_for_not_equal_builtin_rule(left_obj),
            self.resolve_obj_to_number_for_not_equal_builtin_rule(right_obj),
        ) {
            (Some(left_number), Some(right_number)) => {
                if left_number.normalized_value != right_number.normalized_value {
                    return Ok(
                        (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            not_equal_fact.clone().into(),
                            "not_equal_numeric_resolved_or_equal_class_calculation".to_string(),
                            Vec::new(),
                        ))
                        .into(),
                    );
                }
            }
            _ => {}
        }

        if let (Obj::ListSet(left_ls), Obj::ListSet(right_ls)) = (left_obj, right_obj) {
            if left_ls.list.len() != right_ls.list.len() {
                return Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        not_equal_fact.clone().into(),
                        "list_set_different_length".to_string(),
                        Vec::new(),
                    ))
                    .into(),
                );
            }
        }

        if let Some(verified_result) =
            self.try_verify_not_equal_empty_set_from_nonempty(not_equal_fact)?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) =
            self.try_verify_not_equal_from_known_strict_order(not_equal_fact)?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) =
            self.try_verify_not_equal_from_membership_contradiction(not_equal_fact)?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) =
            self.try_verify_abs_not_equal_zero_from_arg_nonzero(not_equal_fact, verify_state)?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) =
            self.try_verify_sub_not_equal_zero_from_operand_not_equal(not_equal_fact)?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) =
            self.try_verify_add_not_equal_zero_from_operand_not_equal_negation(not_equal_fact)?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) =
            self.try_verify_operand_not_equal_from_sub_not_equal_zero(not_equal_fact)?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) =
            self.try_verify_operand_not_equal_negation_from_add_not_equal_zero(not_equal_fact)?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) =
            self.try_verify_not_equal_zero_from_n_and_one_le(not_equal_fact, verify_state)?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) =
            self.try_verify_not_equal_pow_from_base_nonzero(not_equal_fact, verify_state)?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) =
            self.try_verify_div_not_equal_zero_from_numerator_nonzero(not_equal_fact, verify_state)?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) = self
            .try_verify_product_nonzero_component_from_known_product(not_equal_fact, verify_state)?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) = self
            .try_verify_square_sum_not_equal_zero_from_nonzero_component(
                not_equal_fact,
                verify_state,
            )?
        {
            return Ok(verified_result);
        }

        match self
            .try_verify_not_equal_fact_when_zero_and_binary_arithmetic_reduces_by_operand_facts(
                not_equal_fact,
                verify_state,
            )? {
            Some(verified_result) => return Ok(verified_result),
            None => {}
        }

        Ok((StmtUnknown::new()).into())
    }
}

impl Runtime {
    fn try_parse_number_literal_obj_string_for_not_equal_builtin_rule(
        &self,
        obj_string: &str,
    ) -> Option<Number> {
        let trimmed = obj_string.trim();
        if trimmed.is_empty() {
            return None;
        }
        let parsed = Number::new(trimmed.to_string());
        if parsed.to_string() == trimmed {
            return Some(parsed);
        }
        None
    }

    fn resolve_obj_to_number_for_not_equal_builtin_rule(&self, obj: &Obj) -> Option<Number> {
        if let Some(number) = self.resolve_obj_to_number_resolved(obj) {
            return Some(number);
        }
        let obj_key = obj.to_string();
        if let Some(number) = self.get_object_equal_to_normalized_decimal_number(&obj_key) {
            return Some(number);
        }
        let all_equal_obj_strings = self.get_all_objs_equal_to_given(&obj_key);
        for equal_obj_string in all_equal_obj_strings {
            if let Some(number) =
                self.get_object_equal_to_normalized_decimal_number(&equal_obj_string)
            {
                return Some(number);
            }
            if let Some(number) = self
                .try_parse_number_literal_obj_string_for_not_equal_builtin_rule(&equal_obj_string)
            {
                return Some(number);
            }
        }
        None
    }

    // Empty set rule: `S != {}` follows from `$is_nonempty_set(S)`.
    // This replaces the old common fact `S != {} <=> $is_nonempty_set(S)`.
    // Example: after `$is_nonempty_set(S)`, prove `S != {}`.
    fn try_verify_not_equal_empty_set_from_nonempty(
        &mut self,
        not_equal_fact: &NotEqualFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let set = match (&not_equal_fact.left, &not_equal_fact.right) {
            (Obj::ListSet(list), set) if list.list.is_empty() => set.clone(),
            (set, Obj::ListSet(list)) if list.list.is_empty() => set.clone(),
            _ => return Ok(None),
        };

        let nonempty: AtomicFact = IsNonemptySetFact::new(set, line_file).into();
        let sub = self.verify_non_equational_known_then_builtin_rules_only(
            &nonempty,
            &VerifyState::new(0, true),
        )?;
        if !sub.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                not_equal_fact.clone().into(),
                InferResult::new(),
                "not_equal_empty_set_from_nonempty".to_string(),
                vec![sub],
            )
            .into(),
        ))
    }

    // x < y or x > y (including y < x / y > x spellings) in known facts implies x != y.
    fn try_verify_not_equal_from_known_strict_order(
        &mut self,
        not_equal_fact: &NotEqualFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let x = not_equal_fact.left.clone();
        let y = not_equal_fact.right.clone();
        let verify_state = VerifyState::new(0, true);
        let Some(mut steps) =
            self.verify_objects_are_known_reals(&[&x, &y], &line_file, &verify_state)?
        else {
            return Ok(None);
        };
        let candidates: [AtomicFact; 4] = [
            LessFact::new(x.clone(), y.clone(), line_file.clone()).into(),
            GreaterFact::new(x.clone(), y.clone(), line_file.clone()).into(),
            LessFact::new(y.clone(), x.clone(), line_file.clone()).into(),
            GreaterFact::new(y.clone(), x.clone(), line_file.clone()).into(),
        ];
        for order_atomic in candidates {
            let sub =
                self.verify_non_equational_atomic_fact_with_known_atomic_facts(&order_atomic)?;
            if sub.is_true() {
                steps.push(sub);
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                        not_equal_fact.clone().into(),
                        InferResult::new(),
                        "not_equal_from_known_strict_order".to_string(),
                        steps,
                    )
                    .into(),
                ));
            }
        }
        Ok(None)
    }

    // Membership contradiction: if `x $in S` and `not y $in S`, then `x != y`.
    // Example: from `x $in A` and `not y $in A`, prove `x != y` so `{x, y}` is well-defined.
    fn try_verify_not_equal_from_membership_contradiction(
        &mut self,
        not_equal_fact: &NotEqualFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let candidates = [
            (not_equal_fact.left.clone(), not_equal_fact.right.clone()),
            (not_equal_fact.right.clone(), not_equal_fact.left.clone()),
        ];

        for (member_obj, non_member_obj) in candidates {
            for set in self.known_sets_containing_obj(&member_obj) {
                let not_in_set: AtomicFact =
                    NotInFact::new(non_member_obj.clone(), set.clone(), line_file.clone()).into();
                let not_in_result =
                    self.verify_non_equational_atomic_fact_with_known_atomic_facts(&not_in_set)?;
                if !not_in_result.is_true() {
                    continue;
                }

                let in_set: AtomicFact =
                    InFact::new(member_obj.clone(), set, line_file.clone()).into();
                let in_result =
                    self.verify_non_equational_atomic_fact_with_known_atomic_facts(&in_set)?;

                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                        not_equal_fact.clone().into(),
                        InferResult::new(),
                        "not_equal_from_membership_contradiction".to_string(),
                        vec![in_result, not_in_result],
                    )
                    .into(),
                ));
            }
        }

        Ok(None)
    }

    // Absolute values are nonzero exactly when their argument is nonzero.
    // Example: from `x != 0`, prove `abs(x) != 0`.
    fn try_verify_abs_not_equal_zero_from_arg_nonzero(
        &mut self,
        not_equal_fact: &NotEqualFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let abs = match (&not_equal_fact.left, &not_equal_fact.right) {
            (Obj::Abs(abs), right)
                if self.obj_represents_zero_for_not_equal_builtin_rules(right) =>
            {
                abs
            }
            (left, Obj::Abs(abs)) if self.obj_represents_zero_for_not_equal_builtin_rules(left) => {
                abs
            }
            _ => return Ok(None),
        };

        let zero_obj: Obj = Number::new("0".to_string()).into();
        let arg_nonzero: AtomicFact =
            NotEqualFact::new(abs.arg.as_ref().clone(), zero_obj, line_file.clone()).into();
        let result =
            self.verify_non_equational_known_then_builtin_rules_only(&arg_nonzero, verify_state)?;
        if !result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                not_equal_fact.clone().into(),
                InferResult::new(),
                "abs_not_equal_zero_from_arg_nonzero".to_string(),
                vec![result],
            )
            .into(),
        ))
    }

    // Difference nonzero rule: if `a != b` is known, then `a - b != 0`.
    // Example: from `x != 2`, prove `x - 2 != 0`.
    fn try_verify_sub_not_equal_zero_from_operand_not_equal(
        &mut self,
        not_equal_fact: &NotEqualFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let sub = match (&not_equal_fact.left, &not_equal_fact.right) {
            (Obj::Sub(sub), right)
                if self.obj_represents_zero_for_not_equal_builtin_rules(right) =>
            {
                sub
            }
            (left, Obj::Sub(sub)) if self.obj_represents_zero_for_not_equal_builtin_rules(left) => {
                sub
            }
            _ => return Ok(None),
        };

        let candidates: [AtomicFact; 2] = [
            NotEqualFact::new(
                sub.left.as_ref().clone(),
                sub.right.as_ref().clone(),
                line_file.clone(),
            )
            .into(),
            NotEqualFact::new(
                sub.right.as_ref().clone(),
                sub.left.as_ref().clone(),
                line_file.clone(),
            )
            .into(),
        ];

        for candidate in candidates {
            let sub_result =
                self.verify_non_equational_atomic_fact_with_known_atomic_facts(&candidate)?;
            if sub_result.is_true() {
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                        not_equal_fact.clone().into(),
                        InferResult::new(),
                        "sub_not_equal_zero_from_operand_not_equal".to_string(),
                        vec![sub_result],
                    )
                    .into(),
                ));
            }
        }

        Ok(None)
    }

    // Sum nonzero rule: if `a != -b` is known, then `a + b != 0`.
    // Example: from `x != -2`, prove `x + 2 != 0`.
    fn try_verify_add_not_equal_zero_from_operand_not_equal_negation(
        &mut self,
        not_equal_fact: &NotEqualFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let add = match (&not_equal_fact.left, &not_equal_fact.right) {
            (Obj::Add(add), right)
                if self.obj_represents_zero_for_not_equal_builtin_rules(right) =>
            {
                add
            }
            (left, Obj::Add(add)) if self.obj_represents_zero_for_not_equal_builtin_rules(left) => {
                add
            }
            _ => return Ok(None),
        };

        let candidates: [AtomicFact; 2] = [
            NotEqualFact::new(
                add.left.as_ref().clone(),
                Mul::new(
                    Number::new("-1".to_string()).into(),
                    add.right.as_ref().clone(),
                )
                .into(),
                line_file.clone(),
            )
            .into(),
            NotEqualFact::new(
                add.right.as_ref().clone(),
                Mul::new(
                    Number::new("-1".to_string()).into(),
                    add.left.as_ref().clone(),
                )
                .into(),
                line_file.clone(),
            )
            .into(),
        ];

        for candidate in candidates {
            let sub_result =
                self.verify_non_equational_atomic_fact_with_known_atomic_facts(&candidate)?;
            if sub_result.is_true() {
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                        not_equal_fact.clone().into(),
                        InferResult::new(),
                        "add_not_equal_zero_from_operand_not_equal_negation".to_string(),
                        vec![sub_result],
                    )
                    .into(),
                ));
            }
        }

        Ok(None)
    }

    // Difference nonzero reflection: if `a - b != 0` is known, then `a != b`.
    // Example: from `x - c != 0`, prove `x != c`.
    fn try_verify_operand_not_equal_from_sub_not_equal_zero(
        &mut self,
        not_equal_fact: &NotEqualFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let candidates: [AtomicFact; 2] = [
            NotEqualFact::new(
                Sub::new(not_equal_fact.left.clone(), not_equal_fact.right.clone()).into(),
                zero_obj.clone(),
                line_file.clone(),
            )
            .into(),
            NotEqualFact::new(
                Sub::new(not_equal_fact.right.clone(), not_equal_fact.left.clone()).into(),
                zero_obj,
                line_file.clone(),
            )
            .into(),
        ];

        for candidate in candidates {
            let sub_result =
                self.verify_non_equational_atomic_fact_with_known_atomic_facts(&candidate)?;
            if sub_result.is_true() {
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                        not_equal_fact.clone().into(),
                        InferResult::new(),
                        "operand_not_equal_from_sub_not_equal_zero".to_string(),
                        vec![sub_result],
                    )
                    .into(),
                ));
            }
        }

        Ok(None)
    }

    // Sum nonzero reflection: if `a + b != 0` is known, then `a != -b`.
    // Example: from `x + c != 0`, prove `x != -c`.
    fn try_verify_operand_not_equal_negation_from_add_not_equal_zero(
        &mut self,
        not_equal_fact: &NotEqualFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let mut candidates: Vec<AtomicFact> = Vec::new();

        if let Some(right_arg) = Self::negated_arg_for_not_equal_builtin_rule(&not_equal_fact.right)
        {
            candidates.push(
                NotEqualFact::new(
                    Add::new(not_equal_fact.left.clone(), right_arg.clone()).into(),
                    zero_obj.clone(),
                    line_file.clone(),
                )
                .into(),
            );
            candidates.push(
                NotEqualFact::new(
                    Add::new(right_arg, not_equal_fact.left.clone()).into(),
                    zero_obj.clone(),
                    line_file.clone(),
                )
                .into(),
            );
        }

        if let Some(left_arg) = Self::negated_arg_for_not_equal_builtin_rule(&not_equal_fact.left) {
            candidates.push(
                NotEqualFact::new(
                    Add::new(not_equal_fact.right.clone(), left_arg.clone()).into(),
                    zero_obj.clone(),
                    line_file.clone(),
                )
                .into(),
            );
            candidates.push(
                NotEqualFact::new(
                    Add::new(left_arg, not_equal_fact.right.clone()).into(),
                    zero_obj,
                    line_file.clone(),
                )
                .into(),
            );
        }

        for candidate in candidates {
            let sub_result =
                self.verify_non_equational_atomic_fact_with_known_atomic_facts(&candidate)?;
            if sub_result.is_true() {
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                        not_equal_fact.clone().into(),
                        InferResult::new(),
                        "operand_not_equal_negation_from_add_not_equal_zero".to_string(),
                        vec![sub_result],
                    )
                    .into(),
                ));
            }
        }

        Ok(None)
    }

    /// `n != 0` from `n $in N` and `1 <= n` (or `n >= 1`). Example: `forall x N: 1 <= x =>: x != 0`.
    fn try_verify_not_equal_zero_from_n_and_one_le(
        &mut self,
        not_equal_fact: &NotEqualFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let one_obj: Obj = Number::new("1".to_string()).into();
        let x = match (&not_equal_fact.left, &not_equal_fact.right) {
            (l, r) if self.obj_represents_zero_for_not_equal_builtin_rules(r) => l.clone(),
            (l, r) if self.obj_represents_zero_for_not_equal_builtin_rules(l) => r.clone(),
            _ => return Ok(None),
        };
        let in_n: AtomicFact =
            InFact::new(x.clone(), StandardSet::N.into(), line_file.clone()).into();
        if !self
            .verify_non_equational_known_then_builtin_rules_only(&in_n, verify_state)?
            .is_true()
        {
            return Ok(None);
        }
        let ge: AtomicFact =
            GreaterEqualFact::new(x.clone(), one_obj.clone(), line_file.clone()).into();
        if self
            .verify_non_equational_atomic_fact_with_known_atomic_facts(&ge)?
            .is_true()
        {
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    not_equal_fact.clone().into(),
                    "n != 0 from n $in N and 1 <= n".to_string(),
                    Vec::new(),
                )
                .into(),
            ));
        }
        let one_le: AtomicFact = LessEqualFact::new(one_obj, x, line_file.clone()).into();
        if self
            .verify_non_equational_atomic_fact_with_known_atomic_facts(&one_le)?
            .is_true()
        {
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    not_equal_fact.clone().into(),
                    "n != 0 from n $in N and 1 <= n".to_string(),
                    Vec::new(),
                )
                .into(),
            ));
        }
        Ok(None)
    }

    fn obj_is_verified_integer_exponent_for_not_equal_builtin(
        &mut self,
        obj: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        if let Obj::Number(exp_num) = obj {
            return Ok(is_integer_after_simplification(exp_num));
        }

        for standard_set in [StandardSet::Z, StandardSet::N, StandardSet::NPos] {
            let in_set: AtomicFact =
                InFact::new(obj.clone(), standard_set.into(), line_file.clone()).into();
            let result =
                self.verify_non_equational_known_then_builtin_rules_only(&in_set, verify_state)?;
            if result.is_true() {
                return Ok(true);
            }
        }
        Ok(false)
    }

    // a^n != 0 with integer exponent n, from a != 0.
    // Example: from `x R_nz` and `n Z`, prove `x^n != 0`.
    fn try_verify_not_equal_pow_from_base_nonzero(
        &mut self,
        not_equal_fact: &NotEqualFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let pow = match (&not_equal_fact.left, &not_equal_fact.right) {
            (Obj::Pow(p), r) if self.obj_represents_zero_for_not_equal_builtin_rules(r) => p,
            (l, Obj::Pow(p)) if self.obj_represents_zero_for_not_equal_builtin_rules(l) => p,
            _ => return Ok(None),
        };
        if !self.obj_is_verified_integer_exponent_for_not_equal_builtin(
            pow.exponent.as_ref(),
            line_file.clone(),
            verify_state,
        )? {
            return Ok(None);
        }

        let base = pow.base.as_ref().clone();
        let base_neq_zero: AtomicFact = NotEqualFact::new(base, zero_obj, line_file.clone()).into();
        let result =
            self.verify_non_equational_known_then_builtin_rules_only(&base_neq_zero, verify_state)?;
        if result.is_true() {
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                    not_equal_fact.clone().into(),
                    InferResult::new(),
                    "not_equal_pow_from_base_nonzero".to_string(),
                    vec![result],
                )
                .into(),
            ));
        }
        Ok(None)
    }

    // Quotient nonzero rule: if `a != 0` and `b != 0`, then `a / b != 0`.
    // Example: from `x != 0` and `y != 0`, prove `x / y != 0`.
    fn try_verify_div_not_equal_zero_from_numerator_nonzero(
        &mut self,
        not_equal_fact: &NotEqualFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let div = match (&not_equal_fact.left, &not_equal_fact.right) {
            (Obj::Div(div), right)
                if self.obj_represents_zero_for_not_equal_builtin_rules(right) =>
            {
                div
            }
            (left, Obj::Div(div)) if self.obj_represents_zero_for_not_equal_builtin_rules(left) => {
                div
            }
            _ => return Ok(None),
        };

        let zero_obj: Obj = Number::new("0".to_string()).into();
        let numerator_nonzero: AtomicFact = NotEqualFact::new(
            div.left.as_ref().clone(),
            zero_obj.clone(),
            line_file.clone(),
        )
        .into();
        let denominator_nonzero: AtomicFact =
            NotEqualFact::new(div.right.as_ref().clone(), zero_obj, line_file.clone()).into();

        let numerator_result = self.verify_non_equational_known_then_builtin_rules_only(
            &numerator_nonzero,
            verify_state,
        )?;
        if !numerator_result.is_true() {
            return Ok(None);
        }

        let denominator_result = self.verify_non_equational_known_then_builtin_rules_only(
            &denominator_nonzero,
            verify_state,
        )?;
        if !denominator_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                not_equal_fact.clone().into(),
                InferResult::new(),
                "div_not_equal_zero_from_numerator_nonzero".to_string(),
                vec![numerator_result, denominator_result],
            )
            .into(),
        ))
    }

    // A nonzero product of real factors has no zero factor.
    // Example: from `a * b != 0`, prove `a != 0` and separately `b != 0`.
    fn try_verify_product_nonzero_component_from_known_product(
        &mut self,
        not_equal_fact: &NotEqualFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let target = match (&not_equal_fact.left, &not_equal_fact.right) {
            (target, zero) if self.obj_represents_zero_for_not_equal_builtin_rules(zero) => {
                target.clone()
            }
            (zero, target) if self.obj_represents_zero_for_not_equal_builtin_rules(zero) => {
                target.clone()
            }
            _ => return Ok(None),
        };

        let mut known_not_equal_facts = Vec::new();
        for environment in self.iter_environments_from_top() {
            for known_facts_map in environment.known_atomic_facts_with_2_args.values() {
                for known_fact in known_facts_map.values() {
                    if matches!(known_fact, AtomicFact::NotEqualFact(_)) {
                        known_not_equal_facts.push(known_fact.clone());
                    }
                }
            }
        }

        for known_fact in known_not_equal_facts {
            let AtomicFact::NotEqualFact(known_not_equal) = known_fact else {
                continue;
            };
            let product = if self
                .obj_represents_zero_for_not_equal_builtin_rules(&known_not_equal.right)
            {
                &known_not_equal.left
            } else if self.obj_represents_zero_for_not_equal_builtin_rules(&known_not_equal.left) {
                &known_not_equal.right
            } else {
                continue;
            };
            let Obj::Mul(product) = product else {
                continue;
            };

            let target_matches_left = self.verify_zero_product_factor_matches_target(
                &target,
                product.left.as_ref(),
                not_equal_fact.line_file.clone(),
                verify_state,
            )?;
            let target_matches_right = self.verify_zero_product_factor_matches_target(
                &target,
                product.right.as_ref(),
                not_equal_fact.line_file.clone(),
                verify_state,
            )?;
            if !target_matches_left.is_true() && !target_matches_right.is_true() {
                continue;
            }

            let Some(mut steps) = self.verify_objects_are_known_reals(
                &[product.left.as_ref(), product.right.as_ref()],
                &not_equal_fact.line_file,
                verify_state,
            )?
            else {
                continue;
            };
            let known_result = self.verify_non_equational_atomic_fact_with_known_atomic_facts(
                &AtomicFact::NotEqualFact(known_not_equal.clone()),
            )?;
            if !known_result.is_true() {
                continue;
            }
            steps.push(known_result);
            if target_matches_left.is_true() {
                steps.push(target_matches_left);
            } else {
                steps.push(target_matches_right);
            }

            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    not_equal_fact.clone().into(),
                    "product_nonzero_component: a * b != 0 gives a != 0 and b != 0".to_string(),
                    steps,
                )
                .into(),
            ));
        }

        Ok(None)
    }

    // If `a != 0 or b != 0` is known, then `a^2 + b^2 != 0`.
    // This also accepts the expanded square spelling `a*a + b*b`.
    // Example:
    // `forall x, y R: x != 0 or y != 0 <=>: x^2 + y^2 != 0`.
    fn try_verify_square_sum_not_equal_zero_from_nonzero_component(
        &mut self,
        not_equal_fact: &NotEqualFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let expression_obj =
            if self.obj_represents_zero_for_not_equal_builtin_rules(&not_equal_fact.right) {
                &not_equal_fact.left
            } else if self.obj_represents_zero_for_not_equal_builtin_rules(&not_equal_fact.left) {
                &not_equal_fact.right
            } else {
                return Ok(None);
            };

        let Some((left_base, right_base)) =
            self.square_sum_bases_for_not_equal_zero(expression_obj)
        else {
            return Ok(None);
        };

        let zero_obj: Obj = Number::new("0".to_string()).into();
        let left_nonzero: AtomicFact =
            NotEqualFact::new(left_base.clone(), zero_obj.clone(), line_file.clone()).into();
        let right_nonzero: AtomicFact =
            NotEqualFact::new(right_base.clone(), zero_obj, line_file.clone()).into();
        let known_or = OrFact::new(
            vec![
                AndChainAtomicFact::AtomicFact(left_nonzero.clone()),
                AndChainAtomicFact::AtomicFact(right_nonzero.clone()),
            ],
            line_file.clone(),
        );

        let mut steps = Vec::new();
        let known_or_result =
            self.verify_or_fact_known_then_builtin_rules_only(&known_or, verify_state)?;
        if known_or_result.is_true() {
            steps.push(known_or_result);
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                    not_equal_fact.clone().into(),
                    InferResult::new(),
                    "square_sum_not_equal_zero_from_nonzero_component_or".to_string(),
                    steps,
                )
                .into(),
            ));
        }

        let left_result =
            self.verify_non_equational_known_then_builtin_rules_only(&left_nonzero, verify_state)?;
        if left_result.is_true() {
            steps.push(left_result);
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                    not_equal_fact.clone().into(),
                    InferResult::new(),
                    "square_sum_not_equal_zero_from_left_nonzero".to_string(),
                    steps,
                )
                .into(),
            ));
        }

        let right_result =
            self.verify_non_equational_known_then_builtin_rules_only(&right_nonzero, verify_state)?;
        if right_result.is_true() {
            steps.push(right_result);
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                    not_equal_fact.clone().into(),
                    InferResult::new(),
                    "square_sum_not_equal_zero_from_right_nonzero".to_string(),
                    steps,
                )
                .into(),
            ));
        }

        Ok(None)
    }

    fn square_sum_bases_for_not_equal_zero(&self, obj: &Obj) -> Option<(Obj, Obj)> {
        let Obj::Add(add) = obj else {
            return None;
        };
        let left_base = self.square_base_for_not_equal_zero(add.left.as_ref())?;
        let right_base = self.square_base_for_not_equal_zero(add.right.as_ref())?;
        Some((left_base, right_base))
    }

    fn square_base_for_not_equal_zero(&self, obj: &Obj) -> Option<Obj> {
        match obj {
            Obj::Pow(pow) => {
                let Obj::Number(exp_number) = pow.exponent.as_ref() else {
                    return None;
                };
                if exp_number.to_string() == "2" {
                    Some(pow.base.as_ref().clone())
                } else {
                    None
                }
            }
            Obj::Mul(mul) if mul.left.as_ref().to_string() == mul.right.as_ref().to_string() => {
                Some(mul.left.as_ref().clone())
            }
            _ => None,
        }
    }

    fn obj_represents_zero_for_not_equal_builtin_rules(self: &Self, obj: &Obj) -> bool {
        match self.resolve_obj_to_number(obj) {
            Some(number) => number.normalized_value == "0",
            None => false,
        }
    }

    fn obj_is_literal_neg_one_for_not_equal_builtin_rule(obj: &Obj) -> bool {
        match obj {
            Obj::Number(n) => n.normalized_value == "-1",
            _ => false,
        }
    }

    fn negated_arg_for_not_equal_builtin_rule(obj: &Obj) -> Option<Obj> {
        let Obj::Mul(mul) = obj else {
            return None;
        };
        if Self::obj_is_literal_neg_one_for_not_equal_builtin_rule(mul.left.as_ref()) {
            return Some(mul.right.as_ref().clone());
        }
        if Self::obj_is_literal_neg_one_for_not_equal_builtin_rule(mul.right.as_ref()) {
            return Some(mul.left.as_ref().clone());
        }
        None
    }

    fn operand_is_not_equal_to_zero_by_known_non_equational_facts(
        &mut self,
        operand: &Obj,
        line_file: LineFile,
    ) -> Result<bool, RuntimeError> {
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let operand_not_equal_zero_fact =
            NotEqualFact::new(operand.clone(), zero_obj, line_file).into();
        let verify_result = self.verify_non_equational_atomic_fact_with_known_atomic_facts(
            &operand_not_equal_zero_fact,
        )?;
        Ok(verify_result.is_true())
    }

    fn both_operands_nonzero_by_known_non_equational_facts(
        &mut self,
        left_operand: &Obj,
        right_operand: &Obj,
        line_file: LineFile,
    ) -> Result<bool, RuntimeError> {
        let left_nonzero = self.operand_is_not_equal_to_zero_by_known_non_equational_facts(
            left_operand,
            line_file.clone(),
        )?;
        if !left_nonzero {
            return Ok(false);
        }
        self.operand_is_not_equal_to_zero_by_known_non_equational_facts(right_operand, line_file)
    }

    fn both_operands_strictly_positive_by_non_equational_verify(
        &mut self,
        left_operand: &Obj,
        right_operand: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let zero_less_than_left =
            LessFact::new(zero_obj.clone(), left_operand.clone(), line_file.clone()).into();
        if !self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
            &zero_less_than_left,
            verify_state,
        )? {
            return Ok(false);
        }
        let zero_less_than_right = LessFact::new(zero_obj, right_operand.clone(), line_file).into();
        self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
            &zero_less_than_right,
            verify_state,
        )
    }

    fn both_operands_strictly_negative_by_non_equational_verify(
        &mut self,
        left_operand: &Obj,
        right_operand: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let left_less_than_zero =
            LessFact::new(left_operand.clone(), zero_obj.clone(), line_file.clone()).into();
        if !self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
            &left_less_than_zero,
            verify_state,
        )? {
            return Ok(false);
        }
        let right_less_than_zero = LessFact::new(right_operand.clone(), zero_obj, line_file).into();
        self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
            &right_less_than_zero,
            verify_state,
        )
    }

    pub fn mul_product_negative_when_factors_have_strict_opposite_sign_by_non_equational_verify(
        &mut self,
        left_factor: &Obj,
        right_factor: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let left_less_than_zero =
            LessFact::new(left_factor.clone(), zero_obj.clone(), line_file.clone()).into();
        let zero_less_than_right =
            LessFact::new(zero_obj.clone(), right_factor.clone(), line_file.clone()).into();
        if self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
            &left_less_than_zero,
            verify_state,
        )? && self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
            &zero_less_than_right,
            verify_state,
        )? {
            return Ok(true);
        }
        let zero_less_than_left =
            LessFact::new(zero_obj.clone(), left_factor.clone(), line_file.clone()).into();
        let right_less_than_zero = LessFact::new(right_factor.clone(), zero_obj, line_file).into();
        Ok(
            self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
                &zero_less_than_left,
                verify_state,
            )? && self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
                &right_less_than_zero,
                verify_state,
            )?,
        )
    }

    fn sub_difference_nonzero_when_operands_have_strict_opposite_sign_by_non_equational_verify(
        &mut self,
        minuend: &Obj,
        subtrahend: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let zero_less_than_minuend =
            LessFact::new(zero_obj.clone(), minuend.clone(), line_file.clone()).into();
        let subtrahend_less_than_zero =
            LessFact::new(subtrahend.clone(), zero_obj.clone(), line_file.clone()).into();
        if self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
            &zero_less_than_minuend,
            verify_state,
        )? && self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
            &subtrahend_less_than_zero,
            verify_state,
        )? {
            return Ok(true);
        }
        let minuend_less_than_zero =
            LessFact::new(minuend.clone(), zero_obj.clone(), line_file.clone()).into();
        let zero_less_than_subtrahend =
            LessFact::new(zero_obj, subtrahend.clone(), line_file).into();
        Ok(
            self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
                &minuend_less_than_zero,
                verify_state,
            )? && self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
                &zero_less_than_subtrahend,
                verify_state,
            )?,
        )
    }

    fn try_verify_not_equal_fact_when_zero_and_binary_arithmetic_reduces_by_operand_facts(
        &mut self,
        not_equal_fact: &NotEqualFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let expression_obj =
            if self.obj_represents_zero_for_not_equal_builtin_rules(&not_equal_fact.right) {
                &not_equal_fact.left
            } else if self.obj_represents_zero_for_not_equal_builtin_rules(&not_equal_fact.left) {
                &not_equal_fact.right
            } else {
                return Ok(None);
            };

        let builtin_rule_label = match expression_obj {
            Obj::Add(add) => {
                if self.both_operands_strictly_positive_by_non_equational_verify(
                    &add.left,
                    &add.right,
                    line_file.clone(),
                    verify_state,
                )? {
                    Some("add_not_equal_zero_both_operands_strictly_positive")
                } else if self.both_operands_strictly_negative_by_non_equational_verify(
                    &add.left,
                    &add.right,
                    line_file.clone(),
                    verify_state,
                )? {
                    Some("add_not_equal_zero_both_operands_strictly_negative")
                } else {
                    None
                }
            }
            Obj::Mul(mul) => {
                if self.both_operands_nonzero_by_known_non_equational_facts(
                    &mul.left,
                    &mul.right,
                    line_file.clone(),
                )? {
                    Some("mul_not_equal_zero_both_factors_nonzero_by_known_facts")
                } else if self.both_operands_strictly_positive_by_non_equational_verify(
                    &mul.left,
                    &mul.right,
                    line_file.clone(),
                    verify_state,
                )? {
                    Some("mul_not_equal_zero_both_factors_strictly_positive")
                } else if self.both_operands_strictly_negative_by_non_equational_verify(
                    &mul.left,
                    &mul.right,
                    line_file.clone(),
                    verify_state,
                )? {
                    Some("mul_not_equal_zero_both_factors_strictly_negative")
                } else {
                    None
                }
            }
            Obj::Sub(sub) => {
                if self.sub_difference_nonzero_when_operands_have_strict_opposite_sign_by_non_equational_verify(
                    &sub.left,
                    &sub.right,
                    line_file,
                    verify_state,
                )? {
                    Some("sub_not_equal_zero_operands_strict_opposite_sign")
                } else {
                    None
                }
            }
            other => {
                let zero_obj: Obj = Number::new("0".to_string()).into();
                let zero_lt_a = LessFact::new(
                    zero_obj.clone(),
                    other.clone(),
                    line_file.clone(),
                ).into();

                let final_round_verify_state = verify_state.make_final_round_state();

                if self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
                    &zero_lt_a,
                    &final_round_verify_state,
                )? {
                    Some("not_equal_zero_operand_strictly_positive")
                } else {
                    let a_lt_0 = LessFact::new(
                        other.clone(),
                        zero_obj,
                        line_file.clone(),
                    ).into();
                    if self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
                        &a_lt_0,
                        &final_round_verify_state,
                    )? {
                        Some("not_equal_zero_operand_strictly_negative")
                    } else {
                        None
                    }
                }
            }
        };

        match builtin_rule_label {
            Some(rule_label) => Ok(Some(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    not_equal_fact.clone().into(),
                    rule_label.to_string(),
                    Vec::new(),
                ))
                .into(),
            )),
            None => Ok(None),
        }
    }
}
