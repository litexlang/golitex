use super::order_normalize::normalize_positive_order_atomic_fact;
use crate::prelude::*;
use crate::verify::verify_equality_by_builtin_rules::verify_equality_by_they_are_the_same;

impl Runtime {
    // Natural exp/ln are inverse and agree with the existing e-power/log interface.
    // Examples: `exp(ln(x)) = x`, `ln(exp(x)) = x`,
    // `exp(x) = e^x`, and `ln(x) = log(e, x)`.
    pub(super) fn try_verify_native_exp_ln_identity(
        &self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Option<StmtResult> {
        if exp_ln_identity_shape(left, right) || exp_ln_identity_shape(right, left) {
            return Some(native_equal_success(
                left,
                right,
                line_file,
                "native exp/ln inverse or canonical-base identity",
                Vec::new(),
            ));
        }
        None
    }

    // Strict monotonicity makes exp injective on R and ln injective on R+.
    // Example: a known `exp(a) = exp(b)` proves `a = b`.
    pub(super) fn try_verify_native_exp_ln_injectivity(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let exp_left: Obj = Exp::new(left.clone()).into();
        let exp_right: Obj = Exp::new(right.clone()).into();
        let exp_result =
            self.verify_objs_are_equal_by_known_equality(&exp_left, &exp_right, line_file.clone());
        if exp_result.is_true() {
            return Ok(Some(native_equal_success(
                left,
                right,
                line_file,
                "injectivity of native exp",
                vec![exp_result],
            )));
        }
        let ln_left: Obj = Ln::new(left.clone()).into();
        let ln_right: Obj = Ln::new(right.clone()).into();
        let ln_result =
            self.verify_objs_are_equal_by_known_equality(&ln_left, &ln_right, line_file.clone());
        if !ln_result.is_true() {
            return Ok(None);
        }
        let zero: Obj = Number::new("0".to_string()).into();
        let mut positivity_results = Vec::new();
        for arg in [left, right] {
            let positive: AtomicFact =
                LessFact::new(zero.clone(), arg.clone(), line_file.clone()).into();
            let result = self.verify_builtin_rule_premise(&positive, builtin_state)?;
            if !result.is_true() {
                return Ok(None);
            }
            positivity_results.push(result);
        }
        positivity_results.push(ln_result);
        Ok(Some(native_equal_success(
            left,
            right,
            line_file,
            "injectivity of native ln",
            positivity_results,
        )))
    }

    // The zero value of sign characterizes the zero argument.
    // Example: a known `sign(x) = 0` proves `x = 0`.
    pub(super) fn try_verify_native_sign_zero_reflection(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        _builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let arg = if normalized_number_is(left, "0") {
            right
        } else if normalized_number_is(right, "0") {
            left
        } else {
            return Ok(None);
        };
        let sign: Obj = Sign::new(arg.clone()).into();
        let zero: Obj = Number::new("0".to_string()).into();
        let result = self.verify_objs_are_equal_by_known_equality(&sign, &zero, line_file.clone());
        if !result.is_true() {
            return Ok(None);
        }
        Ok(Some(native_equal_success(
            left,
            right,
            line_file,
            "sign is zero only at zero",
            vec![result],
        )))
    }

    // Nonzeroness is likewise reflected by sign.
    // Examples: `x != 0 => sign(x) != 0` and the converse.
    pub(super) fn try_verify_native_sign_nonzero_characterization(
        &mut self,
        goal: &NotEqualFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let zero: Obj = Number::new("0".to_string()).into();
        let (nonzero_obj, zero_on_right) = if normalized_number_is(&goal.right, "0") {
            (&goal.left, true)
        } else if normalized_number_is(&goal.left, "0") {
            (&goal.right, false)
        } else {
            return Ok(None);
        };
        let premise: AtomicFact = if let Obj::Sign(sign) = nonzero_obj {
            NotEqualFact::new(
                sign.arg.as_ref().clone(),
                zero.clone(),
                goal.line_file.clone(),
            )
            .into()
        } else {
            let sign: Obj = Sign::new(nonzero_obj.clone()).into();
            if zero_on_right {
                NotEqualFact::new(sign, zero.clone(), goal.line_file.clone()).into()
            } else {
                NotEqualFact::new(zero.clone(), sign, goal.line_file.clone()).into()
            }
        };
        let result = self.verify_non_equational_atomic_fact_with_known_atomic_facts(&premise)?;
        if !result.is_true() {
            return Ok(None);
        }
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                goal.clone().into(),
                "sign is nonzero exactly for nonzero arguments".to_string(),
                vec![result],
            )
            .into(),
        ))
    }

    // Exponential turns sums into products and differences into quotients;
    // natural logarithm turns positive products into sums and quotients into differences.
    // Examples: `exp(a+b)=exp(a)*exp(b)` and `ln(a*b)=ln(a)+ln(b)`.
    pub(super) fn try_verify_native_exp_ln_algebra(
        &self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Option<StmtResult> {
        if exp_ln_algebra_shape(left, right) || exp_ln_algebra_shape(right, left) {
            return Some(native_equal_success(
                left,
                right,
                line_file,
                "native exp/ln algebra identity",
                Vec::new(),
            ));
        }
        None
    }

    // The sign function is selected by the sign of its real argument.
    // Example: `x > 0` proves `sign(x) = 1`.
    pub(super) fn try_verify_native_sign_value(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (sign, selected) = match (left, right) {
            (Obj::Sign(sign), selected) | (selected, Obj::Sign(sign)) => (sign, selected),
            _ => return Ok(None),
        };
        let Some(number) = selected.evaluate_to_normalized_decimal_number() else {
            return Ok(None);
        };
        let zero: Obj = Number::new("0".to_string()).into();
        let premise: AtomicFact = match number.normalized_value.as_str() {
            "1" => GreaterFact::new((*sign.arg).clone(), zero, line_file.clone()).into(),
            "0" => EqualFact::new((*sign.arg).clone(), zero, line_file.clone()).into(),
            "-1" => LessFact::new((*sign.arg).clone(), zero, line_file.clone()).into(),
            _ => return Ok(None),
        };
        let premise_result = self.verify_builtin_rule_premise(&premise, builtin_state)?;
        if premise_result.is_unknown() {
            return Ok(None);
        }
        Ok(Some(native_equal_success(
            left,
            right,
            line_file,
            "sign value selected from the argument order at zero",
            vec![premise_result],
        )))
    }

    // Multiplying magnitude by sign restores a real value.
    // Example: `sign(x) * abs(x) = x`.
    pub(super) fn try_verify_native_sign_abs_identity(
        &self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Option<StmtResult> {
        if sign_abs_identity_shape(left, right) || sign_abs_identity_shape(right, left) {
            return Some(native_equal_success(
                left,
                right,
                line_file,
                "sign times absolute value restores the argument",
                Vec::new(),
            ));
        }
        None
    }

    // Sign is odd and multiplicative on real inputs.
    // Examples: `sign(-x) = -sign(x)` and
    // `sign(a*b) = sign(a)*sign(b)`.
    pub(super) fn try_verify_native_sign_algebra(
        &self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Option<StmtResult> {
        if !sign_algebra_shape(left, right) && !sign_algebra_shape(right, left) {
            return None;
        }
        Some(native_equal_success(
            left,
            right,
            line_file,
            "native sign oddness or multiplicativity",
            Vec::new(),
        ))
    }

    // Natural factorial obeys the successor recurrence.
    // Example: `factorial(n + 1) = (n + 1) * factorial(n)`.
    pub(super) fn try_verify_native_factorial_recurrence(
        &self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Option<StmtResult> {
        if factorial_recurrence_shape(left, right) || factorial_recurrence_shape(right, left) {
            return Some(native_equal_success(
                left,
                right,
                line_file,
                "factorial successor recurrence",
                Vec::new(),
            ));
        }
        None
    }

    // Earlier factorials divide later factorials.
    // Example: `m <= n => factorial(n) % factorial(m) = 0`.
    pub(super) fn try_verify_native_factorial_divisibility(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (remainder, zero) = match (left, right) {
            (Obj::Mod(remainder), zero) | (zero, Obj::Mod(remainder)) => (remainder, zero),
            _ => return Ok(None),
        };
        if !normalized_number_is(zero, "0") {
            return Ok(None);
        }
        let (Obj::Factorial(later), Obj::Factorial(earlier)) =
            (remainder.left.as_ref(), remainder.right.as_ref())
        else {
            return Ok(None);
        };
        let premise: AtomicFact = LessEqualFact::new(
            earlier.arg.as_ref().clone(),
            later.arg.as_ref().clone(),
            line_file.clone(),
        )
        .into();
        let result = self.verify_builtin_rule_premise(&premise, builtin_state)?;
        if !result.is_true() {
            return Ok(None);
        }
        Ok(Some(native_equal_success(
            left,
            right,
            line_file,
            "earlier factorial divides later factorial",
            vec![result],
        )))
    }

    // Characteristic bounds for the second native-function batch.
    // Examples: `0 < exp(x)`, `-1 <= sign(x) <= 1`, and `1 <= factorial(n)`.
    pub(super) fn try_verify_native_exp_sign_factorial_order(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(result) =
            self.try_verify_native_factorial_monotonicity(atomic_fact, builtin_state)?
        {
            return Ok(Some(result));
        }
        if let Some(result) =
            self.try_verify_native_sign_monotonicity(atomic_fact, builtin_state)?
        {
            return Ok(Some(result));
        }
        if let Some(result) =
            self.try_verify_native_exp_ln_monotonicity(atomic_fact, builtin_state)?
        {
            return Ok(Some(result));
        }
        let Some((verified, subgoals)) =
            self.native_exp_sign_factorial_order_shape(atomic_fact, builtin_state)?
        else {
            return Ok(None);
        };
        if !verified {
            return Ok(None);
        }
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "native exp/sign/factorial characteristic order bound".to_string(),
                subgoals,
            )
            .into(),
        ))
    }

    fn try_verify_native_factorial_monotonicity(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        // Factorial preserves weak order on N and strict order from a positive
        // smaller argument. Examples: `m <= n => m! <= n!` and
        // `m in N+, m < n => m! < n!`.
        let Some(normalized) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let (left, right, strict, line_file) = match &normalized {
            AtomicFact::LessFact(f) => (&f.left, &f.right, true, f.line_file.clone()),
            AtomicFact::LessEqualFact(f) => (&f.left, &f.right, false, f.line_file.clone()),
            _ => return Ok(None),
        };
        let (Obj::Factorial(left), Obj::Factorial(right)) = (left, right) else {
            return Ok(None);
        };
        let mut premises: Vec<AtomicFact> = Vec::new();
        if strict {
            premises.push(
                InFact::new(
                    left.arg.as_ref().clone(),
                    StandardSet::NPos.into(),
                    line_file.clone(),
                )
                .into(),
            );
            premises.push(
                LessFact::new(
                    left.arg.as_ref().clone(),
                    right.arg.as_ref().clone(),
                    line_file,
                )
                .into(),
            );
        } else {
            premises.push(
                LessEqualFact::new(
                    left.arg.as_ref().clone(),
                    right.arg.as_ref().clone(),
                    line_file,
                )
                .into(),
            );
        }
        let mut results = Vec::new();
        for premise in premises {
            let result = self.verify_builtin_rule_premise(&premise, builtin_state)?;
            if !result.is_true() {
                return Ok(None);
            }
            results.push(result);
        }
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "native factorial monotonicity".to_string(),
                results,
            )
            .into(),
        ))
    }

    fn try_verify_native_sign_monotonicity(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        // The real sign function preserves weak order but not strict order.
        // Example: `a <= b => sign(a) <= sign(b)`.
        let Some(AtomicFact::LessEqualFact(f)) = normalize_positive_order_atomic_fact(atomic_fact)
        else {
            return Ok(None);
        };
        let (Obj::Sign(left), Obj::Sign(right)) = (&f.left, &f.right) else {
            return Ok(None);
        };
        let premise: AtomicFact = LessEqualFact::new(
            left.arg.as_ref().clone(),
            right.arg.as_ref().clone(),
            f.line_file.clone(),
        )
        .into();
        let result = self.verify_builtin_rule_premise(&premise, builtin_state)?;
        if !result.is_true() {
            return Ok(None);
        }
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "native sign preserves weak order".to_string(),
                vec![result],
            )
            .into(),
        ))
    }

    fn native_exp_sign_factorial_order_shape(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<(bool, Vec<StmtResult>)>, RuntimeError> {
        let (left, right, strict) = match atomic_fact {
            AtomicFact::LessFact(f) => (&f.left, &f.right, true),
            AtomicFact::GreaterFact(f) => (&f.right, &f.left, true),
            AtomicFact::LessEqualFact(f) => (&f.left, &f.right, false),
            AtomicFact::GreaterEqualFact(f) => (&f.right, &f.left, false),
            _ => return Ok(None),
        };
        if strict
            && is_zero(left)
            && (matches!(right, Obj::Exp(_)) || matches!(right, Obj::Factorial(_)))
        {
            return Ok(Some((true, Vec::new())));
        }
        if !strict
            && ((is_minus_one(left) && matches!(right, Obj::Sign(_)))
                || (matches!(left, Obj::Sign(_)) && is_one(right))
                || (is_one(left) && matches!(right, Obj::Factorial(_))))
        {
            return Ok(Some((true, Vec::new())));
        }

        let (ln, premise): (&Ln, AtomicFact) = if strict && is_zero(left) {
            let Obj::Ln(ln) = right else {
                return Ok(None);
            };
            (
                ln,
                GreaterFact::new(
                    (*ln.arg).clone(),
                    Number::new("1".to_string()).into(),
                    default_line_file(),
                )
                .into(),
            )
        } else if strict && is_zero(right) {
            let Obj::Ln(ln) = left else {
                return Ok(None);
            };
            (
                ln,
                LessFact::new(
                    (*ln.arg).clone(),
                    Number::new("1".to_string()).into(),
                    default_line_file(),
                )
                .into(),
            )
        } else {
            return Ok(None);
        };
        let _ = ln;
        let premise_result = self.verify_builtin_rule_premise(&premise, builtin_state)?;
        if premise_result.is_unknown() {
            return Ok(None);
        }
        Ok(Some((true, vec![premise_result])))
    }

    fn try_verify_native_exp_ln_monotonicity(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        // Natural exp is strictly increasing on R, and natural ln is strictly
        // increasing on R+. Examples: `a < b => exp(a) < exp(b)` and
        // `0 < a < b => ln(a) < ln(b)`; weak order is preserved as well.
        let Some(normalized) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let (left, right, strict, line_file) = match &normalized {
            AtomicFact::LessFact(f) => (&f.left, &f.right, true, f.line_file.clone()),
            AtomicFact::LessEqualFact(f) => (&f.left, &f.right, false, f.line_file.clone()),
            _ => return Ok(None),
        };

        // Order reflection is the converse interface supplied by strict
        // monotonicity. Try it before the forward native-object shapes below.
        let reflected_premises: Vec<AtomicFact> = if strict {
            vec![
                LessFact::new(
                    Exp::new(left.clone()).into(),
                    Exp::new(right.clone()).into(),
                    line_file.clone(),
                )
                .into(),
                LessFact::new(
                    Ln::new(left.clone()).into(),
                    Ln::new(right.clone()).into(),
                    line_file.clone(),
                )
                .into(),
            ]
        } else {
            vec![
                LessEqualFact::new(
                    Exp::new(left.clone()).into(),
                    Exp::new(right.clone()).into(),
                    line_file.clone(),
                )
                .into(),
                LessEqualFact::new(
                    Ln::new(left.clone()).into(),
                    Ln::new(right.clone()).into(),
                    line_file.clone(),
                )
                .into(),
            ]
        };
        for (index, premise) in reflected_premises.into_iter().enumerate() {
            let result =
                self.verify_non_equational_atomic_fact_with_known_atomic_facts(&premise)?;
            if !result.is_true() {
                continue;
            }
            let mut subgoals = Vec::new();
            if index == 1 {
                let zero: Obj = Number::new("0".to_string()).into();
                for arg in [left, right] {
                    let positive: AtomicFact =
                        LessFact::new(zero.clone(), arg.clone(), line_file.clone()).into();
                    let result = self.verify_builtin_rule_premise(&positive, builtin_state)?;
                    if !result.is_true() {
                        subgoals.clear();
                        break;
                    }
                    subgoals.push(result);
                }
                if subgoals.len() != 2 {
                    continue;
                }
            }
            subgoals.push(result);
            let order_kind = if strict { "strict" } else { "weak" };
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    format!("native exp/ln reflects {order_kind} order"),
                    subgoals,
                )
                .into(),
            ));
        }

        let (left_arg, right_arg, function_name, require_positive) = match (left, right) {
            (Obj::Exp(left_exp), Obj::Exp(right_exp)) => {
                (left_exp.arg.as_ref(), right_exp.arg.as_ref(), EXP, false)
            }
            (Obj::Ln(left_ln), Obj::Ln(right_ln)) => {
                (left_ln.arg.as_ref(), right_ln.arg.as_ref(), LN, true)
            }
            _ => return Ok(None),
        };

        let mut premises = Vec::new();
        if require_positive {
            let zero: Obj = Number::new("0".to_string()).into();
            premises.push(LessFact::new(zero.clone(), left_arg.clone(), line_file.clone()).into());
            premises.push(LessFact::new(zero, right_arg.clone(), line_file.clone()).into());
        }
        if strict {
            premises.push(LessFact::new(left_arg.clone(), right_arg.clone(), line_file).into());
        } else {
            premises
                .push(LessEqualFact::new(left_arg.clone(), right_arg.clone(), line_file).into());
        }

        let mut results = Vec::new();
        for premise in premises {
            let result = self.verify_builtin_rule_premise(&premise, builtin_state)?;
            if !result.is_true() {
                return Ok(None);
            }
            results.push(result);
        }
        let order_kind = if strict { "strict" } else { "weak" };
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                format!("native {function_name} preserves {order_kind} order"),
                results,
            )
            .into(),
        ))
    }
}

fn native_equal_success(
    left: &Obj,
    right: &Obj,
    line_file: LineFile,
    reason: &str,
    subgoals: Vec<StmtResult>,
) -> StmtResult {
    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
        EqualFact::new(left.clone(), right.clone(), line_file).into(),
        reason.to_string(),
        subgoals,
    )
    .into()
}

fn exp_ln_identity_shape(native: &Obj, other: &Obj) -> bool {
    match native {
        Obj::Exp(exp) => {
            if let Obj::Ln(ln) = exp.arg.as_ref() {
                return same(&ln.arg, other);
            }
            let Obj::Pow(pow) = other else {
                return false;
            };
            matches!(pow.base.as_ref(), Obj::EulerNumber(_)) && same(&exp.arg, &pow.exponent)
        }
        Obj::Ln(ln) => {
            if let Obj::Exp(exp) = ln.arg.as_ref() {
                return same(&exp.arg, other);
            }
            let Obj::Log(log) = other else {
                return false;
            };
            matches!(log.base.as_ref(), Obj::EulerNumber(_)) && same(&ln.arg, &log.arg)
        }
        _ => false,
    }
}

fn exp_ln_algebra_shape(native: &Obj, other: &Obj) -> bool {
    match native {
        Obj::Exp(exp) => match exp.arg.as_ref() {
            Obj::Add(add) => {
                let Obj::Mul(product) = other else {
                    return false;
                };
                exp_pair_matches(&add.left, &add.right, &product.left, &product.right)
            }
            Obj::Sub(sub) => {
                let Obj::Div(quotient) = other else {
                    return false;
                };
                exp_pair_matches(&sub.left, &sub.right, &quotient.left, &quotient.right)
            }
            _ => false,
        },
        Obj::Ln(ln) => match ln.arg.as_ref() {
            Obj::Mul(product) => {
                let Obj::Add(sum) = other else {
                    return false;
                };
                ln_pair_matches(&product.left, &product.right, &sum.left, &sum.right)
            }
            Obj::Div(quotient) => {
                let Obj::Sub(difference) = other else {
                    return false;
                };
                ln_pair_matches(
                    &quotient.left,
                    &quotient.right,
                    &difference.left,
                    &difference.right,
                )
            }
            _ => false,
        },
        _ => false,
    }
}

fn exp_pair_matches(first: &Obj, second: &Obj, first_native: &Obj, second_native: &Obj) -> bool {
    let (Obj::Exp(first_exp), Obj::Exp(second_exp)) = (first_native, second_native) else {
        return false;
    };
    same(first, &first_exp.arg) && same(second, &second_exp.arg)
}

fn ln_pair_matches(first: &Obj, second: &Obj, first_native: &Obj, second_native: &Obj) -> bool {
    let (Obj::Ln(first_ln), Obj::Ln(second_ln)) = (first_native, second_native) else {
        return false;
    };
    same(first, &first_ln.arg) && same(second, &second_ln.arg)
}

fn sign_abs_identity_shape(product: &Obj, other: &Obj) -> bool {
    let Obj::Mul(product) = product else {
        return false;
    };
    let (sign, abs) = match (product.left.as_ref(), product.right.as_ref()) {
        (Obj::Sign(sign), Obj::Abs(abs)) | (Obj::Abs(abs), Obj::Sign(sign)) => (sign, abs),
        _ => return false,
    };
    same(&sign.arg, &abs.arg) && same(&sign.arg, other)
}

fn sign_algebra_shape(native: &Obj, other: &Obj) -> bool {
    let Obj::Sign(sign) = native else {
        return false;
    };
    if let (Obj::Mul(product), Obj::Mul(other_product)) = (sign.arg.as_ref(), other) {
        if let (Obj::Sign(left_sign), Obj::Sign(right_sign)) =
            (other_product.left.as_ref(), other_product.right.as_ref())
        {
            if same(&product.left, &left_sign.arg) && same(&product.right, &right_sign.arg) {
                return true;
            }
        }
    }

    let Some(inner) = negative_one_factor(sign.arg.as_ref()) else {
        return false;
    };
    let Some(other_inner) = negative_one_factor(other) else {
        return false;
    };
    let Obj::Sign(other_sign) = other_inner else {
        return false;
    };
    same(inner, &other_sign.arg)
}

fn negative_one_factor(obj: &Obj) -> Option<&Obj> {
    let Obj::Mul(product) = obj else {
        return None;
    };
    if normalized_number_is(&product.left, "-1") {
        Some(product.right.as_ref())
    } else if normalized_number_is(&product.right, "-1") {
        Some(product.left.as_ref())
    } else {
        None
    }
}

fn factorial_recurrence_shape(factorial: &Obj, product: &Obj) -> bool {
    let Obj::Factorial(successor_factorial) = factorial else {
        return false;
    };
    let Obj::Mul(product) = product else {
        return false;
    };
    let matches_successor_product = |successor: &Obj, factorial: &Obj| {
        let Some(predecessor) = successor_predecessor(successor_factorial.arg.as_ref()) else {
            return false;
        };
        let Obj::Factorial(predecessor_factorial) = factorial else {
            return false;
        };
        same(successor_factorial.arg.as_ref(), successor)
            && same(predecessor, predecessor_factorial.arg.as_ref())
    };
    let matches_predecessor_product = |factor: &Obj, factorial: &Obj| {
        let Obj::Factorial(predecessor_factorial) = factorial else {
            return false;
        };
        let Obj::Sub(predecessor) = predecessor_factorial.arg.as_ref() else {
            return false;
        };
        same(successor_factorial.arg.as_ref(), factor)
            && same(successor_factorial.arg.as_ref(), predecessor.left.as_ref())
            && is_one(predecessor.right.as_ref())
    };
    matches_successor_product(product.left.as_ref(), product.right.as_ref())
        || matches_successor_product(product.right.as_ref(), product.left.as_ref())
        || matches_predecessor_product(product.left.as_ref(), product.right.as_ref())
        || matches_predecessor_product(product.right.as_ref(), product.left.as_ref())
}

fn successor_predecessor(obj: &Obj) -> Option<&Obj> {
    let Obj::Add(add) = obj else {
        return None;
    };
    if is_one(&add.left) {
        Some(&add.right)
    } else if is_one(&add.right) {
        Some(&add.left)
    } else {
        None
    }
}

fn same(left: &Obj, right: &Obj) -> bool {
    verify_equality_by_they_are_the_same(left, right)
}

fn is_zero(obj: &Obj) -> bool {
    normalized_number_is(obj, "0")
}

fn is_one(obj: &Obj) -> bool {
    normalized_number_is(obj, "1")
}

fn is_minus_one(obj: &Obj) -> bool {
    normalized_number_is(obj, "-1")
}

fn normalized_number_is(obj: &Obj, expected: &str) -> bool {
    obj.evaluate_to_normalized_decimal_number()
        .is_some_and(|number| number.normalized_value == expected)
}
