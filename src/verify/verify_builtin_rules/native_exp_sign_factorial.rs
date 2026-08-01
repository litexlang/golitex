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
        builtin_state: &mut BuiltinRuleVerifyState,
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
        let premise_result = self.verify_cross_family_builtin_child(&premise, builtin_state)?;
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

    // Characteristic bounds for the second native-function batch.
    // Examples: `0 < exp(x)`, `-1 <= sign(x) <= 1`, and `1 <= factorial(n)`.
    pub(super) fn try_verify_native_exp_sign_factorial_order(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &mut BuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
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

    fn native_exp_sign_factorial_order_shape(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &mut BuiltinRuleVerifyState,
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
        let premise_result = self.verify_cross_family_builtin_child(&premise, builtin_state)?;
        if premise_result.is_unknown() {
            return Ok(None);
        }
        Ok(Some((true, vec![premise_result])))
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
