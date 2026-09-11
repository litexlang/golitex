use crate::prelude::*;
use crate::result::RuntimeResolvedNumericComparisonBuiltinRuleEvidence;
use crate::verification::verify_number_in_standard_set::is_integer_after_simplification;

impl Runtime {
    pub fn _verify_not_equal_fact_with_builtin_rules(
        &mut self,
        not_equal_fact: &NotEqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let left_obj = &not_equal_fact.left;
        let right_obj = &not_equal_fact.right;

        if let Some(result) = self.try_verify_native_i_nonzero(not_equal_fact) {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_native_complex_abs_nonzero(not_equal_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_native_sign_nonzero_characterization(not_equal_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) = try_verify_native_real_constant_nonzero(not_equal_fact) {
            return Ok(result);
        }
        if let Some(result) = try_verify_intrinsically_positive_native_value_nonzero(not_equal_fact)
        {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_trigonometric_not_equal(not_equal_fact, builtin_state)?
        {
            return Ok(result);
        }

        // Not-equality is symmetric.
        // Example: a known `a != b` proves the goal `b != a`.
        let reversed: AtomicFact = self
            .new_not_equal_fact(
                right_obj.clone(),
                left_obj.clone(),
                not_equal_fact.line_file.clone(),
            )
            .into();
        if let Some(reversed_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&reversed, builtin_state)?
        {
            return Ok(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    not_equal_fact.clone().into(),
                    "not-equality symmetry".to_string(),
                    BuiltinRuleEvidence::NotEqualSymmetry,
                    vec![reversed_result],
                )
                .into(),
            );
        }

        if let (Obj::ListSet(left_ls), Obj::ListSet(right_ls)) = (left_obj, right_obj) {
            if left_ls.list.len() != right_ls.list.len() {
                return Ok(
                    (SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        not_equal_fact.clone().into(),
                        "list_set_different_length".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyNotEqualFactWithBuiltinRules),
                        Vec::new(),
                    ))
                    .into(),
                );
            }
        }

        if let Some(verified_result) =
            self.try_verify_not_equal_empty_set_from_nonempty(not_equal_fact, builtin_state)?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) =
            self.try_verify_not_equal_from_known_strict_order(not_equal_fact, builtin_state)?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) = self
            .try_verify_not_equal_from_known_positive_lower_bound(not_equal_fact, builtin_state)?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) =
            self.try_verify_not_equal_from_membership_contradiction(not_equal_fact, builtin_state)?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) =
            self.try_verify_abs_not_equal_zero_from_arg_nonzero(not_equal_fact, builtin_state)?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) =
            self.try_verify_sqrt_not_equal_zero_from_positive_arg(not_equal_fact, builtin_state)?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) = self
            .try_verify_sub_not_equal_zero_from_operand_not_equal(not_equal_fact, builtin_state)?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) = self
            .try_verify_add_not_equal_zero_from_operand_not_equal_negation(
                not_equal_fact,
                builtin_state,
            )?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) = self
            .try_verify_operand_not_equal_from_sub_not_equal_zero(not_equal_fact, builtin_state)?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) = self
            .try_verify_operand_not_equal_negation_from_add_not_equal_zero(
                not_equal_fact,
                builtin_state,
            )?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) =
            self.try_verify_not_equal_zero_from_n_and_one_le(not_equal_fact, builtin_state)?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) =
            self.try_verify_not_equal_pow_from_base_nonzero(not_equal_fact, builtin_state)?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) = self
            .try_verify_div_not_equal_zero_from_numerator_nonzero(not_equal_fact, builtin_state)?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) = self
            .try_verify_product_nonzero_component_from_known_product(
                not_equal_fact,
                builtin_state,
            )?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) = self
            .try_verify_square_sum_not_equal_zero_from_nonzero_component(
                not_equal_fact,
                builtin_state,
            )?
        {
            return Ok(verified_result);
        }

        match self
            .try_verify_not_equal_fact_when_zero_and_binary_arithmetic_reduces_by_operand_facts(
                not_equal_fact,
                builtin_state,
            )? {
            Some(verified_result) => return Ok(verified_result),
            None => {}
        }

        Ok((UnknownGenericStmtResult::new()).into())
    }
}

// Primitive positive real constants are nonzero, and Euler's number is not one.
// Example: `e != 0`, `pi != 0`, and `e != 1`.
fn try_verify_native_real_constant_nonzero(
    not_equal_fact: &NotEqualFact,
) -> Option<ProveFactResult> {
    let is_zero = |obj: &Obj| {
        matches!(
            obj,
            Obj::Number(number) if number.normalized_value == "0"
        )
    };
    let is_native_positive_constant = |obj: &Obj| matches!(obj, Obj::EulerNumber(_) | Obj::Pi(_));
    let is_one = |obj: &Obj| {
        matches!(
            obj,
            Obj::Number(number) if number.normalized_value == "1"
        )
    };
    let is_e = |obj: &Obj| matches!(obj, Obj::EulerNumber(_));
    if !((is_zero(&not_equal_fact.left) && is_native_positive_constant(&not_equal_fact.right))
        || (is_native_positive_constant(&not_equal_fact.left) && is_zero(&not_equal_fact.right))
        || (is_one(&not_equal_fact.left) && is_e(&not_equal_fact.right))
        || (is_e(&not_equal_fact.left) && is_one(&not_equal_fact.right)))
    {
        return None;
    }
    Some(
        SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
            not_equal_fact.clone().into(),
            "native real constant distinctness".to_string(),
            BuiltinRuleEvidence::Uncatalogued(
                UncataloguedBuiltinRule::TryVerifyNativeRealConstantNonzero,
            ),
            Vec::new(),
        )
        .into(),
    )
}

// A well-defined exponential or factorial value is strictly positive, hence
// cannot equal zero. The operator-domain checks have already run in the
// enclosing fact's well-definedness phase.
fn try_verify_intrinsically_positive_native_value_nonzero(
    not_equal_fact: &NotEqualFact,
) -> Option<ProveFactResult> {
    let is_zero = |obj: &Obj| matches!(obj, Obj::Number(number) if number.normalized_value == "0");
    let is_positive_native = |obj: &Obj| matches!(obj, Obj::Exp(_) | Obj::Factorial(_));
    if !((is_zero(&not_equal_fact.left) && is_positive_native(&not_equal_fact.right))
        || (is_positive_native(&not_equal_fact.left) && is_zero(&not_equal_fact.right)))
    {
        return None;
    }
    Some(
        SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
            not_equal_fact.clone().into(),
            "well-defined exp/factorial values are strictly positive".to_string(),
            BuiltinRuleEvidence::Uncatalogued(
                UncataloguedBuiltinRule::TryVerifyIntrinsicallyPositiveNativeValueNonzero,
            ),
            Vec::new(),
        )
        .into(),
    )
}

impl Runtime {
    pub(in crate::verification) fn verify_resolved_numeric_not_equal_without_builtin_recursion(
        &self,
        not_equal_fact: &NotEqualFact,
    ) -> Option<ProveFactResult> {
        let left_number =
            self.resolve_obj_to_number_for_not_equal_builtin_rule(&not_equal_fact.left)?;
        let right_number =
            self.resolve_obj_to_number_for_not_equal_builtin_rule(&not_equal_fact.right)?;
        if left_number.normalized_value == right_number.normalized_value {
            return None;
        }
        let target: Fact = not_equal_fact.clone().into();
        let evidence = match (
            not_equal_fact
                .left
                .evaluate_to_normalized_decimal_number_with_result(),
            not_equal_fact
                .right
                .evaluate_to_normalized_decimal_number_with_result(),
        ) {
            (Some(left_evaluation), Some(right_evaluation)) => {
                BuiltinRuleEvidence::ClosedNumericComparison(
                    ClosedNumericComparisonBuiltinRuleEvidence::new(
                        target.clone(),
                        left_evaluation,
                        right_evaluation,
                    ),
                )
            }
            _ => BuiltinRuleEvidence::RuntimeResolvedNumericComparison(
                RuntimeResolvedNumericComparisonBuiltinRuleEvidence::new(
                    target.clone(),
                    left_number.into(),
                    right_number.into(),
                ),
            ),
        };
        Some(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                target,
                "not_equal_numeric_resolved_or_equal_class_calculation".to_string(),
                evidence,
                Vec::new(),
            )
            .into(),
        )
    }

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
        if let Some(number) = self.get_object_equal_to_normalized_decimal_number(obj) {
            return Some(number);
        }
        for equal_obj in self.get_all_obj_representatives_equal_to_given(obj) {
            if let Some(number) = self.get_object_equal_to_normalized_decimal_number(&equal_obj) {
                return Some(number);
            }
            if let Some(number) = self
                .try_parse_number_literal_obj_string_for_not_equal_builtin_rule(
                    &equal_obj.to_string(),
                )
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
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let set = match (&not_equal_fact.left, &not_equal_fact.right) {
            (Obj::ListSet(list), set) if list.list.is_empty() => set.clone(),
            (set, Obj::ListSet(list)) if list.list.is_empty() => set.clone(),
            _ => return Ok(None),
        };

        let nonempty: AtomicFact = self.new_is_nonempty_set_fact(set, line_file).into();
        let Some(sub) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&nonempty, builtin_state)?
        else {
            return Ok(None);
        };

        Ok(Some(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                not_equal_fact.clone().into(),
                SuccessInferResult::new(),
                "not_equal_empty_set_from_nonempty".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyNotEqualEmptySetFromNonempty,
                ),
                vec![sub],
            )
            .into(),
        ))
    }

    // x < y or x > y (including y < x / y > x spellings) in known facts implies x != y.
    fn try_verify_not_equal_from_known_strict_order(
        &mut self,
        not_equal_fact: &NotEqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let x = not_equal_fact.left.clone();
        let y = not_equal_fact.right.clone();
        let Some(mut steps) =
            self.verify_objects_are_known_reals_in_builtin(&[&x, &y], &line_file, builtin_state)?
        else {
            return Ok(None);
        };
        let candidates: [AtomicFact; 4] = [
            self.new_less_fact(x.clone(), y.clone(), line_file.clone())
                .into(),
            self.new_greater_fact(x.clone(), y.clone(), line_file.clone())
                .into(),
            self.new_less_fact(y.clone(), x.clone(), line_file.clone())
                .into(),
            self.new_greater_fact(y.clone(), x.clone(), line_file.clone())
                .into(),
        ];
        for order_atomic in &candidates {
            let Some(sub) =
                self.try_verify_atomic_fact_as_builtin_rule_premise(order_atomic, builtin_state)?
            else {
                continue;
            };
            steps.push(sub);
            let success =
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                    not_equal_fact.clone().into(),
                    SuccessInferResult::new(),
                    "not_equal_from_known_strict_order".to_string(),
                    BuiltinRuleEvidence::NotEqualFromStrictOrder,
                    steps,
                );
            return Ok(Some(success.into()));
        }

        for alternatives in [
            vec![vec![candidates[0].clone()], vec![candidates[1].clone()]],
            vec![vec![candidates[2].clone()], vec![candidates[3].clone()]],
        ] {
            let premise_result = self.try_verify_builtin_rule_premise_alternatives(
                alternatives,
                line_file.clone(),
                builtin_state,
            )?;
            if let Some(premise_result) = premise_result {
                steps.push(premise_result);
                return Ok(Some(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                        not_equal_fact.clone().into(),
                        SuccessInferResult::new(),
                        "not_equal_from_complete_strict_order_disjunction".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(
                            UncataloguedBuiltinRule::TryVerifyNotEqualFromKnownStrictOrder,
                        ),
                        steps,
                    )
                    .into(),
                ));
            }
        }
        Ok(None)
    }

    // A weak lower bound that is itself in a positive numeric carrier keeps
    // the bounded value away from zero. This stays leaf-only so it remains
    // available during anonymous-function well-definedness checks.
    // Example: `a R+`, `a <= x` implies `x != 0` (in particular for
    // `x` bound by a closed interval `[a, b]`).
    fn try_verify_not_equal_from_known_positive_lower_bound(
        &mut self,
        not_equal_fact: &NotEqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let target = match (&not_equal_fact.left, &not_equal_fact.right) {
            (target, zero) if self.obj_represents_zero_for_not_equal_builtin_rules(zero) => {
                target.clone()
            }
            (zero, target) if self.obj_represents_zero_for_not_equal_builtin_rules(zero) => {
                target.clone()
            }
            _ => return Ok(None),
        };

        let mut known_orders = Vec::new();
        for environment in self.iter_environments_from_top() {
            for known_facts_map in environment.facts.atomic.by_two_args.values() {
                for known_fact in known_facts_map.values() {
                    if let Some(normalized) =
                        super::normalize_positive_order_atomic_fact(self, known_fact)
                    {
                        known_orders.push(normalized);
                    }
                }
            }
        }

        for order in known_orders {
            let (lower, upper) = match &order {
                AtomicFact::LessFact(f) => (&f.left, &f.right),
                AtomicFact::LessEqualFact(f) => (&f.left, &f.right),
                _ => continue,
            };
            if upper.to_string() != target.to_string() {
                continue;
            }

            for positive_set in [StandardSet::NPos, StandardSet::QPos, StandardSet::RPos] {
                let positive_membership: AtomicFact = self
                    .new_in_fact(
                        lower.clone(),
                        positive_set.into(),
                        not_equal_fact.line_file.clone(),
                    )
                    .into();
                let Some(positive_result) = self.try_verify_atomic_fact_as_builtin_rule_premise(
                    &positive_membership,
                    builtin_state,
                )?
                else {
                    continue;
                };
                let Some(order_result) =
                    self.try_verify_atomic_fact_as_builtin_rule_premise(&order, builtin_state)?
                else {
                    continue;
                };
                return Ok(Some(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                        not_equal_fact.clone().into(),
                        SuccessInferResult::new(),
                        "not_equal_from_known_positive_lower_bound".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(
                            UncataloguedBuiltinRule::TryVerifyNotEqualFromKnownPositiveLowerBound,
                        ),
                        vec![positive_result, order_result],
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
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let candidates = [
            (not_equal_fact.left.clone(), not_equal_fact.right.clone()),
            (not_equal_fact.right.clone(), not_equal_fact.left.clone()),
        ];

        for (member_obj, non_member_obj) in candidates {
            for set in self.known_sets_containing_obj(&member_obj) {
                let not_in_set: AtomicFact = self
                    .new_not_in_fact(non_member_obj.clone(), set.clone(), line_file.clone())
                    .into();
                let Some(not_in_result) = self
                    .try_verify_atomic_fact_as_builtin_rule_premise(&not_in_set, builtin_state)?
                else {
                    continue;
                };

                let in_set: AtomicFact = self
                    .new_in_fact(member_obj.clone(), set, line_file.clone())
                    .into();
                let Some(in_result) =
                    self.try_verify_atomic_fact_as_builtin_rule_premise(&in_set, builtin_state)?
                else {
                    continue;
                };

                return Ok(Some(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                        not_equal_fact.clone().into(),
                        SuccessInferResult::new(),
                        "not_equal_from_membership_contradiction".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(
                            UncataloguedBuiltinRule::TryVerifyNotEqualFromMembershipContradiction,
                        ),
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
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
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
        let arg_nonzero: AtomicFact = self
            .new_not_equal_fact(abs.arg.as_ref().clone(), zero_obj, line_file.clone())
            .into();
        let Some(result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&arg_nonzero, builtin_state)?
        else {
            return Ok(None);
        };

        Ok(Some(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                not_equal_fact.clone().into(),
                SuccessInferResult::new(),
                "abs_not_equal_zero_from_arg_nonzero".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyAbsNotEqualZeroFromArgNonzero,
                ),
                vec![result],
            )
            .into(),
        ))
    }

    // The principal square root is nonzero when its real argument is strictly
    // positive. Example: `0 < x` proves `sqrt(x) != 0`; the strict premise is
    // essential because `sqrt(0) = 0`.
    fn try_verify_sqrt_not_equal_zero_from_positive_arg(
        &mut self,
        not_equal_fact: &NotEqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let sqrt = match (&not_equal_fact.left, &not_equal_fact.right) {
            (Obj::Sqrt(sqrt), right)
                if self.obj_represents_zero_for_not_equal_builtin_rules(right) =>
            {
                sqrt
            }
            (left, Obj::Sqrt(sqrt))
                if self.obj_represents_zero_for_not_equal_builtin_rules(left) =>
            {
                sqrt
            }
            _ => return Ok(None),
        };

        let zero: Obj = Number::new("0".to_string()).into();
        let positive: AtomicFact = self
            .new_greater_fact(sqrt.arg.as_ref().clone(), zero, line_file.clone())
            .into();
        let Some(positive_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&positive, builtin_state)?
        else {
            return Ok(None);
        };

        Ok(Some(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                not_equal_fact.clone().into(),
                "sqrt(x) != 0 from x > 0".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifySqrtNotEqualZeroFromPositiveArg,
                ),
                vec![positive_result],
            )
            .into(),
        ))
    }

    // Difference nonzero rule: if `a != b` is known, then `a - b != 0`.
    // Example: from `x != 2`, prove `x - 2 != 0`.
    fn try_verify_sub_not_equal_zero_from_operand_not_equal(
        &mut self,
        not_equal_fact: &NotEqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
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
            self.new_not_equal_fact(
                sub.left.as_ref().clone(),
                sub.right.as_ref().clone(),
                line_file.clone(),
            )
            .into(),
            self.new_not_equal_fact(
                sub.right.as_ref().clone(),
                sub.left.as_ref().clone(),
                line_file.clone(),
            )
            .into(),
        ];

        for candidate in &candidates {
            let Some(sub_result) =
                self.try_verify_atomic_fact_as_builtin_rule_premise(candidate, builtin_state)?
            else {
                continue;
            };
            return Ok(Some(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                    not_equal_fact.clone().into(),
                    SuccessInferResult::new(),
                    "sub_not_equal_zero_from_operand_not_equal".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::TryVerifySubNotEqualZeroFromOperandNotEqual01,
                    ),
                    vec![sub_result],
                )
                .into(),
            ));
        }

        let premise_result = self.try_verify_builtin_rule_premise_alternatives(
            candidates
                .into_iter()
                .map(|candidate| vec![candidate])
                .collect(),
            line_file,
            builtin_state,
        )?;
        if let Some(premise_result) = premise_result {
            return Ok(Some(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                    not_equal_fact.clone().into(),
                    SuccessInferResult::new(),
                    "sub_not_equal_zero_from_complete_operand_disjunction".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::TryVerifySubNotEqualZeroFromOperandNotEqual02,
                    ),
                    vec![premise_result],
                )
                .into(),
            ));
        }

        Ok(None)
    }

    // Sum nonzero rule: if `a != -b` is known, then `a + b != 0`.
    // Example: from `x != -2`, prove `x + 2 != 0`.
    fn try_verify_add_not_equal_zero_from_operand_not_equal_negation(
        &mut self,
        not_equal_fact: &NotEqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
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
            self.new_not_equal_fact(
                add.left.as_ref().clone(),
                Mul::new(
                    Number::new("-1".to_string()).into(),
                    add.right.as_ref().clone(),
                )
                .into(),
                line_file.clone(),
            )
            .into(),
            self.new_not_equal_fact(
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

        for candidate in &candidates {
            let Some(sub_result) =
                self.try_verify_atomic_fact_as_builtin_rule_premise(candidate, builtin_state)?
            else {
                continue;
            };
            return Ok(Some(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                    not_equal_fact.clone().into(),
                    SuccessInferResult::new(),
                    "add_not_equal_zero_from_operand_not_equal_negation".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryVerifyAddNotEqualZeroFromOperandNotEqualNegation01),
                    vec![sub_result],
                )
                .into(),
            ));
        }

        let premise_result = self.try_verify_builtin_rule_premise_alternatives(
            candidates
                .into_iter()
                .map(|candidate| vec![candidate])
                .collect(),
            line_file,
            builtin_state,
        )?;
        if let Some(premise_result) = premise_result {
            return Ok(Some(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                    not_equal_fact.clone().into(),
                    SuccessInferResult::new(),
                    "add_not_equal_zero_from_complete_negation_disjunction".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryVerifyAddNotEqualZeroFromOperandNotEqualNegation02),
                    vec![premise_result],
                )
                .into(),
            ));
        }

        Ok(None)
    }

    // Difference nonzero reflection: if `a - b != 0` is known, then `a != b`.
    // Example: from `x - c != 0`, prove `x != c`.
    fn try_verify_operand_not_equal_from_sub_not_equal_zero(
        &mut self,
        not_equal_fact: &NotEqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let candidates: [AtomicFact; 2] = [
            self.new_not_equal_fact(
                Sub::new(not_equal_fact.left.clone(), not_equal_fact.right.clone()).into(),
                zero_obj.clone(),
                line_file.clone(),
            )
            .into(),
            self.new_not_equal_fact(
                Sub::new(not_equal_fact.right.clone(), not_equal_fact.left.clone()).into(),
                zero_obj,
                line_file.clone(),
            )
            .into(),
        ];

        for candidate in &candidates {
            let Some(sub_result) =
                self.try_verify_atomic_fact_as_builtin_rule_premise(candidate, builtin_state)?
            else {
                continue;
            };
            return Ok(Some(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                    not_equal_fact.clone().into(),
                    SuccessInferResult::new(),
                    "operand_not_equal_from_sub_not_equal_zero".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::TryVerifyOperandNotEqualFromSubNotEqualZero01,
                    ),
                    vec![sub_result],
                )
                .into(),
            ));
        }

        let premise_result = self.try_verify_builtin_rule_premise_alternatives(
            candidates
                .into_iter()
                .map(|candidate| vec![candidate])
                .collect(),
            line_file,
            builtin_state,
        )?;
        if let Some(premise_result) = premise_result {
            return Ok(Some(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                    not_equal_fact.clone().into(),
                    SuccessInferResult::new(),
                    "operand_not_equal_from_complete_difference_disjunction".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::TryVerifyOperandNotEqualFromSubNotEqualZero02,
                    ),
                    vec![premise_result],
                )
                .into(),
            ));
        }

        Ok(None)
    }

    // Sum nonzero reflection: if `a + b != 0` is known, then `a != -b`.
    // Example: from `x + c != 0`, prove `x != -c`.
    fn try_verify_operand_not_equal_negation_from_add_not_equal_zero(
        &mut self,
        not_equal_fact: &NotEqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let mut candidates: Vec<AtomicFact> = Vec::new();

        if let Some(right_arg) = Self::negated_arg_for_not_equal_builtin_rule(&not_equal_fact.right)
        {
            candidates.push(
                self.new_not_equal_fact(
                    Add::new(not_equal_fact.left.clone(), right_arg.clone()).into(),
                    zero_obj.clone(),
                    line_file.clone(),
                )
                .into(),
            );
            candidates.push(
                self.new_not_equal_fact(
                    Add::new(right_arg, not_equal_fact.left.clone()).into(),
                    zero_obj.clone(),
                    line_file.clone(),
                )
                .into(),
            );
        }

        if let Some(left_arg) = Self::negated_arg_for_not_equal_builtin_rule(&not_equal_fact.left) {
            candidates.push(
                self.new_not_equal_fact(
                    Add::new(not_equal_fact.right.clone(), left_arg.clone()).into(),
                    zero_obj.clone(),
                    line_file.clone(),
                )
                .into(),
            );
            candidates.push(
                self.new_not_equal_fact(
                    Add::new(left_arg, not_equal_fact.right.clone()).into(),
                    zero_obj,
                    line_file.clone(),
                )
                .into(),
            );
        }

        for candidate in &candidates {
            let Some(sub_result) =
                self.try_verify_atomic_fact_as_builtin_rule_premise(candidate, builtin_state)?
            else {
                continue;
            };
            return Ok(Some(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                    not_equal_fact.clone().into(),
                    SuccessInferResult::new(),
                    "operand_not_equal_negation_from_add_not_equal_zero".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryVerifyOperandNotEqualNegationFromAddNotEqualZero01),
                    vec![sub_result],
                )
                .into(),
            ));
        }

        if !candidates.is_empty() {
            let premise_result = self.try_verify_builtin_rule_premise_alternatives(
                candidates
                    .into_iter()
                    .map(|candidate| vec![candidate])
                    .collect(),
                line_file,
                builtin_state,
            )?;
            if let Some(premise_result) = premise_result {
                return Ok(Some(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                        not_equal_fact.clone().into(),
                        SuccessInferResult::new(),
                        "operand_not_equal_negation_from_complete_sum_disjunction".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryVerifyOperandNotEqualNegationFromAddNotEqualZero02),
                        vec![premise_result],
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
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let one_obj: Obj = Number::new("1".to_string()).into();
        let x = match (&not_equal_fact.left, &not_equal_fact.right) {
            (l, r) if self.obj_represents_zero_for_not_equal_builtin_rules(r) => l.clone(),
            (l, r) if self.obj_represents_zero_for_not_equal_builtin_rules(l) => r.clone(),
            _ => return Ok(None),
        };
        let in_n: AtomicFact = self
            .new_in_fact(x.clone(), StandardSet::N.into(), line_file.clone())
            .into();
        let ge: AtomicFact = self
            .new_greater_equal_fact(x.clone(), one_obj.clone(), line_file.clone())
            .into();
        let one_le: AtomicFact = self
            .new_less_equal_fact(one_obj, x, line_file.clone())
            .into();
        let Some(premise_result) = self.try_verify_builtin_rule_premise_alternatives(
            vec![vec![in_n.clone(), ge], vec![in_n, one_le]],
            line_file,
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        Ok(Some(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                not_equal_fact.clone().into(),
                "n != 0 from n $in N and 1 <= n".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyNotEqualZeroFromNAndOneLe,
                ),
                vec![premise_result],
            )
            .into(),
        ))
    }

    fn try_verify_integer_exponent_for_not_equal_builtin(
        &mut self,
        obj: &Obj,
        line_file: LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        if let Obj::Number(exp_num) = obj {
            return Ok(is_integer_after_simplification(exp_num).then_some(Vec::new()));
        }

        // Preserve the immediate integer carrier through subtraction without
        // asking the builtin engine to chain a separate `n - 1 $in Z` fact.
        // This is needed while checking an induction hypothesis such as
        // `a^(n - 1) != 0`: the hypothesis must be well-defined before its
        // proof body can state the intermediate carrier fact.
        if let Obj::Sub(sub) = obj {
            let Some(mut left_results) = self.try_verify_integer_exponent_for_not_equal_builtin(
                sub.left.as_ref(),
                line_file.clone(),
                builtin_state,
            )?
            else {
                return Ok(None);
            };
            let Some(mut right_results) = self.try_verify_integer_exponent_for_not_equal_builtin(
                sub.right.as_ref(),
                line_file,
                builtin_state,
            )?
            else {
                return Ok(None);
            };
            left_results.append(&mut right_results);
            return Ok(Some(left_results));
        }

        for standard_set in [StandardSet::Z, StandardSet::N, StandardSet::NPos] {
            let in_set: AtomicFact = self
                .new_in_fact(obj.clone(), standard_set.into(), line_file.clone())
                .into();
            if let Some(result) =
                self.try_verify_atomic_fact_as_builtin_rule_premise(&in_set, builtin_state)?
            {
                return Ok(Some(vec![result]));
            }
        }
        Ok(None)
    }

    // a^n != 0 with integer exponent n, from a != 0.
    // Example: from `x R*` and `n Z`, prove `x^n != 0`.
    fn try_verify_not_equal_pow_from_base_nonzero(
        &mut self,
        not_equal_fact: &NotEqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let pow = match (&not_equal_fact.left, &not_equal_fact.right) {
            (Obj::Pow(p), r) if self.obj_represents_zero_for_not_equal_builtin_rules(r) => p,
            (l, Obj::Pow(p)) if self.obj_represents_zero_for_not_equal_builtin_rules(l) => p,
            _ => return Ok(None),
        };
        let Some(mut exponent_results) = self.try_verify_integer_exponent_for_not_equal_builtin(
            pow.exponent.as_ref(),
            line_file.clone(),
            builtin_state,
        )?
        else {
            return Ok(None);
        };

        let base = pow.base.as_ref().clone();
        let base_neq_zero: AtomicFact = self
            .new_not_equal_fact(base.clone(), zero_obj, line_file.clone())
            .into();
        if let Some(result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&base_neq_zero, builtin_state)?
        {
            exponent_results.push(result);
            return Ok(Some(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                    not_equal_fact.clone().into(),
                    SuccessInferResult::new(),
                    "not_equal_pow_from_base_nonzero".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::TryVerifyNotEqualPowFromBaseNonzero01,
                    ),
                    exponent_results,
                )
                .into(),
            ));
        }

        // A known positive numeric carrier makes the power base nonzero in
        // this same rule.  Do not spend another builtin layer converting the
        // carrier to `base != 0` while checking a division's well-definedness.
        // Example: `n N+` implies `n^2 != 0`.
        for positive_set in [StandardSet::NPos, StandardSet::QPos, StandardSet::RPos] {
            let positive_membership: AtomicFact = self
                .new_in_fact(base.clone(), positive_set.into(), line_file.clone())
                .into();
            if let Some(positive_result) = self.try_verify_atomic_fact_as_builtin_rule_premise(
                &positive_membership,
                builtin_state,
            )? {
                exponent_results.push(positive_result);
                return Ok(Some(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                        not_equal_fact.clone().into(),
                        SuccessInferResult::new(),
                        "not_equal_pow_from_positive_base_carrier".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(
                            UncataloguedBuiltinRule::TryVerifyNotEqualPowFromBaseNonzero02,
                        ),
                        exponent_results,
                    )
                    .into(),
                ));
            }
        }
        Ok(None)
    }

    // Quotient nonzero rule: if `a != 0` and `b != 0`, then `a / b != 0`.
    // Example: from `x != 0` and `y != 0`, prove `x / y != 0`.
    fn try_verify_div_not_equal_zero_from_numerator_nonzero(
        &mut self,
        not_equal_fact: &NotEqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let (div, orientation, matched_zero) = match (&not_equal_fact.left, &not_equal_fact.right) {
            (Obj::Div(div), right)
                if self.obj_represents_zero_for_not_equal_builtin_rules(right) =>
            {
                (div, NonzeroExpressionOrientation::ExpressionOnLeft, right)
            }
            (left, Obj::Div(div)) if self.obj_represents_zero_for_not_equal_builtin_rules(left) => {
                (div, NonzeroExpressionOrientation::ExpressionOnRight, left)
            }
            _ => return Ok(None),
        };

        let zero_obj: Obj = Number::new("0".to_string()).into();
        let numerator_nonzero: AtomicFact = self
            .new_not_equal_fact(
                div.left.as_ref().clone(),
                zero_obj.clone(),
                line_file.clone(),
            )
            .into();
        let denominator_nonzero: AtomicFact = self
            .new_not_equal_fact(div.right.as_ref().clone(), zero_obj, line_file.clone())
            .into();

        let Some(numerator_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&numerator_nonzero, builtin_state)?
        else {
            return Ok(None);
        };
        let Some(denominator_result) = self
            .try_verify_atomic_fact_as_builtin_rule_premise(&denominator_nonzero, builtin_state)?
        else {
            return Ok(None);
        };
        let step_results = vec![numerator_result, denominator_result];
        let success = if matches!(
            matched_zero,
            Obj::Number(number) if number.normalized_value == "0"
        ) {
            let evidence =
                BuiltinRuleEvidence::DivNotEqualZero(DivNotEqualZeroBuiltinRuleEvidence::new(
                    div.left.as_ref().clone(),
                    div.right.as_ref().clone(),
                    orientation,
                ));
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                not_equal_fact.clone().into(),
                SuccessInferResult::new(),
                "div_not_equal_zero_from_numerator_nonzero".to_string(),
                evidence,
                step_results,
            )
        } else {
            // Resolved aliases of zero still verify in Litex, but this rule
            // cannot yet return the equality evidence a compiler would need.
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                not_equal_fact.clone().into(),
                SuccessInferResult::new(),
                "div_not_equal_zero_from_numerator_nonzero".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyDivNotEqualZeroFromNumeratorNonzero,
                ),
                step_results,
            )
        };
        Ok(Some(success.into()))
    }

    // A nonzero product over the native fields R or C has no zero factor.
    // Example: from `a, b C` and `a * b != 0`, prove `a != 0` and `b != 0`.
    fn try_verify_product_nonzero_component_from_known_product(
        &mut self,
        not_equal_fact: &NotEqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
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
            for known_facts_map in environment.facts.atomic.by_two_args.values() {
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
                &self.new_equal_fact_from_refs(
                    &target,
                    product.left.as_ref(),
                    not_equal_fact.line_file.clone(),
                ),
                builtin_state,
            )?;
            let target_matches_right = self.verify_zero_product_factor_matches_target(
                &self.new_equal_fact_from_refs(
                    &target,
                    product.right.as_ref(),
                    not_equal_fact.line_file.clone(),
                ),
                builtin_state,
            )?;
            if !target_matches_left.is_success() && !target_matches_right.is_success() {
                continue;
            }

            let Some(mut steps) = self
                .verify_objects_are_known_real_or_complex_scalars_in_builtin(
                    &[product.left.as_ref(), product.right.as_ref()],
                    &not_equal_fact.line_file,
                    builtin_state,
                )?
            else {
                continue;
            };
            let Some(known_result) = self.try_verify_atomic_fact_as_builtin_rule_premise(
                &AtomicFact::NotEqualFact(known_not_equal.clone()),
                builtin_state,
            )?
            else {
                continue;
            };
            steps.push(known_result);
            if target_matches_left.is_success() {
                steps.push(target_matches_left);
            } else {
                steps.push(target_matches_right);
            }

            return Ok(Some(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    not_equal_fact.clone().into(),
                    "product_nonzero_component: a * b != 0 gives a != 0 and b != 0".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::TryVerifyProductNonzeroComponentFromKnownProduct,
                    ),
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
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
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
        let Some(mut steps) = self.verify_objects_are_known_reals_in_builtin(
            &[&left_base, &right_base],
            &line_file,
            builtin_state,
        )?
        else {
            return Ok(None);
        };

        let zero_obj: Obj = Number::new("0".to_string()).into();
        let left_nonzero: AtomicFact = self
            .new_not_equal_fact(left_base.clone(), zero_obj.clone(), line_file.clone())
            .into();
        let right_nonzero: AtomicFact = self
            .new_not_equal_fact(right_base.clone(), zero_obj, line_file.clone())
            .into();
        let premise = QuantifierFreeFact::OrFact(
            self.new_or_fact(vec![left_nonzero.into(), right_nonzero.into()], line_file),
        );
        let premise_result = self.try_verify_builtin_rule_premise(&premise, builtin_state)?;
        if let Some(premise_result) = premise_result {
            steps.push(premise_result);
            return Ok(Some(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                    not_equal_fact.clone().into(),
                    SuccessInferResult::new(),
                    "square_sum_not_equal_zero_from_nonzero_component_or".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::TryVerifySquareSumNotEqualZeroFromNonzeroComponent,
                    ),
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

    pub fn obj_represents_zero_for_not_equal_builtin_rules(self: &Self, obj: &Obj) -> bool {
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

    fn both_operands_nonzero_by_known_non_equational_facts(
        &mut self,
        left_operand: &Obj,
        right_operand: &Obj,
        line_file: LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let premises = [
            self.new_not_equal_fact(left_operand.clone(), zero_obj.clone(), line_file.clone())
                .into(),
            self.new_not_equal_fact(right_operand.clone(), zero_obj, line_file)
                .into(),
        ];
        // A factor may also be a directly computable nonzero scalar such as `7 / 5`.
        let mut results = Vec::with_capacity(premises.len());
        for premise in &premises {
            let Some(result) =
                self.try_verify_atomic_fact_as_builtin_rule_premise(premise, builtin_state)?
            else {
                return Ok(None);
            };
            results.push(result);
        }
        Ok(Some(results))
    }

    fn both_operands_strictly_positive_by_non_equational_verify(
        &mut self,
        left_operand: &Obj,
        right_operand: &Obj,
        line_file: LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let premises = [
            self.new_less_fact(zero_obj.clone(), left_operand.clone(), line_file.clone())
                .into(),
            self.new_less_fact(zero_obj, right_operand.clone(), line_file)
                .into(),
        ];
        self.verify_builtin_rule_premises(&premises, builtin_state)
    }

    fn both_operands_strictly_negative_by_non_equational_verify(
        &mut self,
        left_operand: &Obj,
        right_operand: &Obj,
        line_file: LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let premises = [
            self.new_less_fact(left_operand.clone(), zero_obj.clone(), line_file.clone())
                .into(),
            self.new_less_fact(right_operand.clone(), zero_obj, line_file)
                .into(),
        ];
        self.verify_builtin_rule_premises(&premises, builtin_state)
    }

    pub fn mul_product_negative_when_factors_have_strict_opposite_sign_by_non_equational_verify(
        &mut self,
        left_factor: &Obj,
        right_factor: &Obj,
        line_file: LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let alternatives = vec![
            vec![
                self.new_less_fact(left_factor.clone(), zero_obj.clone(), line_file.clone())
                    .into(),
                self.new_less_fact(zero_obj.clone(), right_factor.clone(), line_file.clone())
                    .into(),
            ],
            vec![
                self.new_less_fact(zero_obj.clone(), left_factor.clone(), line_file.clone())
                    .into(),
                self.new_less_fact(right_factor.clone(), zero_obj, line_file.clone())
                    .into(),
            ],
        ];
        let result = self.try_verify_builtin_rule_premise_alternatives(
            alternatives,
            line_file,
            builtin_state,
        )?;
        Ok(result.map(|result| vec![result]))
    }

    fn sub_difference_nonzero_when_operands_have_strict_opposite_sign_by_non_equational_verify(
        &mut self,
        minuend: &Obj,
        subtrahend: &Obj,
        line_file: LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let alternatives = vec![
            vec![
                self.new_less_fact(zero_obj.clone(), minuend.clone(), line_file.clone())
                    .into(),
                self.new_less_fact(subtrahend.clone(), zero_obj.clone(), line_file.clone())
                    .into(),
            ],
            vec![
                self.new_less_fact(minuend.clone(), zero_obj.clone(), line_file.clone())
                    .into(),
                self.new_less_fact(zero_obj, subtrahend.clone(), line_file.clone())
                    .into(),
            ],
        ];
        let result = self.try_verify_builtin_rule_premise_alternatives(
            alternatives,
            line_file,
            builtin_state,
        )?;
        Ok(result.map(|result| vec![result]))
    }

    fn try_verify_not_equal_fact_when_zero_and_binary_arithmetic_reduces_by_operand_facts(
        &mut self,
        not_equal_fact: &NotEqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let expression_obj =
            if self.obj_represents_zero_for_not_equal_builtin_rules(&not_equal_fact.right) {
                &not_equal_fact.left
            } else if self.obj_represents_zero_for_not_equal_builtin_rules(&not_equal_fact.left) {
                &not_equal_fact.right
            } else {
                return Ok(None);
            };

        let verified = match expression_obj {
            Obj::Add(add) => {
                if let Some(subgoals) = self.both_operands_strictly_positive_by_non_equational_verify(
                    &add.left,
                    &add.right,
                    line_file.clone(),
                    builtin_state,
                )? {
                    Some(("add_not_equal_zero_both_operands_strictly_positive", subgoals))
                } else if let Some(subgoals) = self.both_operands_strictly_negative_by_non_equational_verify(
                    &add.left,
                    &add.right,
                    line_file.clone(),
                    builtin_state,
                )? {
                    Some(("add_not_equal_zero_both_operands_strictly_negative", subgoals))
                } else {
                    None
                }
            }
            Obj::Mul(mul) => {
                if let Some(subgoals) = self.both_operands_nonzero_by_known_non_equational_facts(
                    &mul.left,
                    &mul.right,
                    line_file.clone(),
                    builtin_state,
                )? {
                    Some(("mul_not_equal_zero_both_factors_nonzero_by_known_facts", subgoals))
                } else if let Some(subgoals) = self.both_operands_strictly_positive_by_non_equational_verify(
                    &mul.left,
                    &mul.right,
                    line_file.clone(),
                    builtin_state,
                )? {
                    Some(("mul_not_equal_zero_both_factors_strictly_positive", subgoals))
                } else if let Some(subgoals) = self.both_operands_strictly_negative_by_non_equational_verify(
                    &mul.left,
                    &mul.right,
                    line_file.clone(),
                    builtin_state,
                )? {
                    Some(("mul_not_equal_zero_both_factors_strictly_negative", subgoals))
                } else {
                    None
                }
            }
            Obj::Sub(sub) => {
                if let Some(subgoals) = self.sub_difference_nonzero_when_operands_have_strict_opposite_sign_by_non_equational_verify(
                    &sub.left,
                    &sub.right,
                    line_file,
                    builtin_state,
                )? {
                    Some(("sub_not_equal_zero_operands_strict_opposite_sign", subgoals))
                } else {
                    None
                }
            }
            other => {
                let zero_obj: Obj = Number::new("0".to_string()).into();
                let zero_lt_a = self.new_less_fact(
                    zero_obj.clone(),
                    other.clone(),
                    line_file.clone(),
                ).into();

                let positive_result = self
                    .try_verify_atomic_fact_as_builtin_rule_premise(&zero_lt_a, builtin_state)?;
                if let Some(positive_result) = positive_result {
                    Some(("not_equal_zero_operand_strictly_positive", vec![positive_result]))
                } else {
                    let a_lt_0 = self.new_less_fact(
                        other.clone(),
                        zero_obj,
                        line_file.clone(),
                    ).into();
                    let negative_result = self
                        .try_verify_atomic_fact_as_builtin_rule_premise(&a_lt_0, builtin_state)?;
                    if let Some(negative_result) = negative_result {
                        Some(("not_equal_zero_operand_strictly_negative", vec![negative_result]))
                    } else {
                        None
                    }
                }
            }
        };

        match verified {
            Some((rule_label, subgoals)) => {
                let success = if rule_label
                    == "mul_not_equal_zero_both_factors_nonzero_by_known_facts"
                {
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        not_equal_fact.clone().into(),
                        rule_label.to_string(),
                        BuiltinRuleEvidence::Nonzero(NonzeroBuiltinRule::Mul),
                        subgoals,
                    )
                } else {
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        not_equal_fact.clone().into(),
                        rule_label.to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryVerifyNotEqualFactWhenZeroAndBinaryArithmeticReducesByOperandFacts),
                        subgoals,
                    )
                };
                Ok(Some(success.into()))
            }
            None => Ok(None),
        }
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/verification/builtin_rules/not_equal_builtin/tests.rs"]
mod tests;
