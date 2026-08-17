use super::order_normalize::normalize_positive_order_atomic_fact;
use crate::prelude::*;
use crate::verify::verify_equality_by_builtin_rules::objs_match_for_pattern;

impl Runtime {
    // Integer inputs are fixed by both rounding operations.
    // Example: `n $in Z` proves `floor(n) = n` and `ceil(n) = n`.
    pub(super) fn try_verify_native_rounding_integer_equality(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let (arg, other, name) = match (left, right) {
            (Obj::Floor(value), other) | (other, Obj::Floor(value)) => {
                (value.arg.as_ref(), other, FLOOR)
            }
            (Obj::Ceil(value), other) | (other, Obj::Ceil(value)) => {
                (value.arg.as_ref(), other, CEIL)
            }
            _ => return Ok(None),
        };
        if !objs_match_for_pattern(arg, other) {
            return Ok(None);
        }
        let integer_fact: AtomicFact =
            InFact::new(arg.clone(), StandardSet::Z.into(), line_file.clone()).into();
        let premise_result =
            self.verify_atomic_fact_as_builtin_rule_premise(&integer_fact, builtin_state)?;
        if premise_result.is_unknown() {
            return Ok(None);
        }
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                equal_fact.clone().into(),
                format!("{name} fixes integer inputs"),
                vec![premise_result],
            )
            .into(),
        ))
    }

    // Floor and ceiling are dual under negation and commute with integer shifts.
    // Examples: `floor(-x) = -ceil(x)` and
    // `n in Z => floor(x+n) = floor(x)+n`.
    pub(super) fn try_verify_native_rounding_algebra_equality(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        if rounding_negation_shape(left, right) || rounding_negation_shape(right, left) {
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    equal_fact.clone().into(),
                    "native floor/ceil negation duality".to_string(),
                    Vec::new(),
                )
                .into(),
            ));
        }

        let shift = rounding_integer_translation_shift(left, right)
            .or_else(|| rounding_integer_translation_shift(right, left));
        let Some(shift) = shift else {
            return Ok(None);
        };
        let premise: AtomicFact =
            InFact::new(shift, StandardSet::Z.into(), line_file.clone()).into();
        let premise_result =
            self.verify_atomic_fact_as_builtin_rule_premise(&premise, builtin_state)?;
        if !premise_result.is_true() {
            return Ok(None);
        }
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                equal_fact.clone().into(),
                "native floor/ceil integer translation".to_string(),
                vec![premise_result],
            )
            .into(),
        ))
    }

    // Selects the appropriate argument once its order is known.
    // Example: `a <= b` proves `min(a, b) = a` and `max(a, b) = b`.
    pub(super) fn try_verify_native_min_max_equality(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let (first_arg, second_arg, selected, is_min) = match (left, right) {
            (Obj::Min(value), selected) | (selected, Obj::Min(value)) => {
                (value.left.as_ref(), value.right.as_ref(), selected, true)
            }
            (Obj::Max(value), selected) | (selected, Obj::Max(value)) => {
                (value.left.as_ref(), value.right.as_ref(), selected, false)
            }
            _ => return Ok(None),
        };
        let selected_is_first = objs_match_for_pattern(selected, first_arg);
        let selected_is_second = objs_match_for_pattern(selected, second_arg);
        if !selected_is_first && !selected_is_second {
            return Ok(None);
        }
        let (premise_left, premise_right) =
            if (is_min && selected_is_first) || (!is_min && selected_is_second) {
                (first_arg, second_arg)
            } else {
                (second_arg, first_arg)
            };
        let premise = LessEqualFact::new(
            premise_left.clone(),
            premise_right.clone(),
            line_file.clone(),
        );
        let premise_result =
            self.verify_atomic_fact_as_builtin_rule_premise(&premise.into(), builtin_state)?;
        if premise_result.is_unknown() {
            return Ok(None);
        }
        let name = if is_min { "min" } else { "max" };
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                equal_fact.clone().into(),
                format!("{name} selects the ordered argument: {premise_left} <= {premise_right}"),
                vec![premise_result],
            )
            .into(),
        ))
    }

    // Characteristic order bounds for floor, ceiling, minimum, and maximum.
    // Examples: `floor(x) <= x < floor(x)+1`, `ceil(x)-1 < x <= ceil(x)`,
    // `min(a,b) <= a`, and `a <= max(a,b)`.
    pub(super) fn try_verify_native_rounding_extrema_order(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(result) =
            self.try_verify_native_lcm_le_common_positive_multiple(atomic_fact, builtin_state)?
        {
            return Ok(Some(result));
        }
        if let Some(result) =
            self.try_verify_native_rounding_extrema_monotonicity(atomic_fact, builtin_state)?
        {
            return Ok(Some(result));
        }
        let (left, right, is_strict) = match atomic_fact {
            AtomicFact::LessFact(f) => (&f.left, &f.right, true),
            AtomicFact::LessEqualFact(f) => (&f.left, &f.right, false),
            _ => return Ok(None),
        };
        let verified = if is_strict {
            floor_upper_shape(left, right) || ceil_lower_shape(left, right)
        } else {
            floor_lower_shape(left, right)
                || ceil_upper_shape(left, right)
                || min_lower_shape(left, right)
                || max_upper_shape(left, right)
        };
        Ok(verified.then(|| {
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "native rounding/extremum characteristic order bound".to_string(),
                Vec::new(),
            )
            .into()
        }))
    }

    fn try_verify_native_lcm_le_common_positive_multiple(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        // A positive common multiple bounds the least common multiple.
        // The modulo premises intentionally use abs(input), matching the
        // Euclidean remainder interface for signed integers.
        let Some(AtomicFact::LessEqualFact(f)) = normalize_positive_order_atomic_fact(atomic_fact)
        else {
            return Ok(None);
        };
        let Obj::Lcm(lcm) = &f.left else {
            return Ok(None);
        };
        let zero: Obj = Number::new("0".to_string()).into();
        let premises: Vec<AtomicFact> = vec![
            InFact::new(
                f.right.clone(),
                StandardSet::NPos.into(),
                f.line_file.clone(),
            )
            .into(),
            EqualFact::new(
                Mod::new(f.right.clone(), Abs::new(lcm.left.as_ref().clone()).into()).into(),
                zero.clone(),
                f.line_file.clone(),
            )
            .into(),
            EqualFact::new(
                Mod::new(f.right.clone(), Abs::new(lcm.right.as_ref().clone()).into()).into(),
                zero,
                f.line_file.clone(),
            )
            .into(),
        ];
        let Some(results) = self.verify_builtin_rule_premises(&premises, builtin_state)? else {
            return Ok(None);
        };
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "native lcm is bounded by every positive common multiple".to_string(),
                results,
            )
            .into(),
        ))
    }

    fn try_verify_native_rounding_extrema_monotonicity(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        // Floor, ceiling, min, and max preserve weak componentwise order.
        // Examples: `a <= b => floor(a) <= floor(b)` and
        // `a <= c, b <= d => min(a,b) <= min(c,d)`.
        let Some(AtomicFact::LessEqualFact(f)) = normalize_positive_order_atomic_fact(atomic_fact)
        else {
            return Ok(None);
        };
        let (premises, reason) = match (&f.left, &f.right) {
            (Obj::Floor(left), Obj::Floor(right)) => (
                vec![LessEqualFact::new(
                    left.arg.as_ref().clone(),
                    right.arg.as_ref().clone(),
                    f.line_file.clone(),
                )
                .into()],
                "native floor preserves weak order",
            ),
            (Obj::Ceil(left), Obj::Ceil(right)) => (
                vec![LessEqualFact::new(
                    left.arg.as_ref().clone(),
                    right.arg.as_ref().clone(),
                    f.line_file.clone(),
                )
                .into()],
                "native ceil preserves weak order",
            ),
            (Obj::Min(left), Obj::Min(right)) => (
                vec![
                    LessEqualFact::new(
                        left.left.as_ref().clone(),
                        right.left.as_ref().clone(),
                        f.line_file.clone(),
                    )
                    .into(),
                    LessEqualFact::new(
                        left.right.as_ref().clone(),
                        right.right.as_ref().clone(),
                        f.line_file.clone(),
                    )
                    .into(),
                ],
                "native min preserves componentwise weak order",
            ),
            (Obj::Max(left), Obj::Max(right)) => (
                vec![
                    LessEqualFact::new(
                        left.left.as_ref().clone(),
                        right.left.as_ref().clone(),
                        f.line_file.clone(),
                    )
                    .into(),
                    LessEqualFact::new(
                        left.right.as_ref().clone(),
                        right.right.as_ref().clone(),
                        f.line_file.clone(),
                    )
                    .into(),
                ],
                "native max preserves componentwise weak order",
            ),
            _ => return Ok(None),
        };

        let Some(results) = self.verify_builtin_rule_premises(&premises, builtin_state)? else {
            return Ok(None);
        };
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                reason.to_string(),
                results,
            )
            .into(),
        ))
    }

    // Min and max form the ordinary lattice operations on real numbers.
    // Examples: `min(a,b)=min(b,a)`, `min(a,a)=a`, and
    // `min(a,max(a,b))=a`, with dual max laws.
    pub(super) fn try_verify_native_min_max_lattice_equality(
        &self,
        equal_fact: &EqualFact,
    ) -> Option<StmtResult> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        if !min_max_lattice_shape(left, right) && !min_max_lattice_shape(right, left) {
            return None;
        }
        Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                equal_fact.clone().into(),
                "native min/max lattice identity".to_string(),
                Vec::new(),
            )
            .into(),
        )
    }

    // The least common multiple and positive gcd satisfy lcm(a,b)gcd(a,b)=|ab|.
    // Example: `a != 0 or b != 0` proves
    // `lcm(a, b) * gcd(a, b) = abs(a * b)`.
    pub(super) fn try_verify_native_lcm_gcd_product_equality(
        &self,
        equal_fact: &EqualFact,
    ) -> Option<StmtResult> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        if !lcm_gcd_product_shape(left, right) && !lcm_gcd_product_shape(right, left) {
            return None;
        }
        Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                equal_fact.clone().into(),
                "lcm times gcd is the absolute product".to_string(),
                Vec::new(),
            )
            .into(),
        )
    }

    // Lcm is symmetric, vanishes with a zero argument, and is divisible by
    // either nonzero input. Examples: `lcm(a,b)=lcm(b,a)` and
    // `lcm(a,b) % abs(a) = 0` when the remainder is well-defined.
    pub(super) fn try_verify_native_lcm_basic_equality(
        &self,
        equal_fact: &EqualFact,
    ) -> Option<StmtResult> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        if !lcm_basic_shape(left, right) && !lcm_basic_shape(right, left) {
            return None;
        }
        Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                equal_fact.clone().into(),
                "native lcm symmetry, zero law, or divisibility".to_string(),
                Vec::new(),
            )
            .into(),
        )
    }
}

fn floor_lower_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::Floor(floor) = left else {
        return false;
    };
    objs_match_for_pattern(&floor.arg, right)
}

fn floor_upper_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::Add(add) = right else {
        return false;
    };
    let Obj::Floor(floor) = add.left.as_ref() else {
        return false;
    };
    objs_match_for_pattern(left, &floor.arg)
        && add
            .right
            .evaluate_to_normalized_decimal_number()
            .is_some_and(|n| n.normalized_value == "1")
}

fn ceil_lower_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::Sub(sub) = left else {
        return false;
    };
    let Obj::Ceil(ceil) = sub.left.as_ref() else {
        return false;
    };
    objs_match_for_pattern(&ceil.arg, right)
        && sub
            .right
            .evaluate_to_normalized_decimal_number()
            .is_some_and(|n| n.normalized_value == "1")
}

fn ceil_upper_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::Ceil(ceil) = right else {
        return false;
    };
    objs_match_for_pattern(left, &ceil.arg)
}

fn min_lower_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::Min(min) = left else {
        return false;
    };
    objs_match_for_pattern(&min.left, right) || objs_match_for_pattern(&min.right, right)
}

fn max_upper_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::Max(max) = right else {
        return false;
    };
    objs_match_for_pattern(left, &max.left) || objs_match_for_pattern(left, &max.right)
}

fn lcm_gcd_product_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::Mul(product) = left else {
        return false;
    };
    let (lcm, gcd) = match (product.left.as_ref(), product.right.as_ref()) {
        (Obj::Lcm(lcm), Obj::Gcd(gcd)) | (Obj::Gcd(gcd), Obj::Lcm(lcm)) => (lcm, gcd),
        _ => return false,
    };
    let Obj::Abs(abs) = right else {
        return false;
    };
    let Obj::Mul(arguments_product) = abs.arg.as_ref() else {
        return false;
    };
    objs_match_for_pattern(&lcm.left, &gcd.left)
        && objs_match_for_pattern(&lcm.right, &gcd.right)
        && objs_match_for_pattern(&lcm.left, &arguments_product.left)
        && objs_match_for_pattern(&lcm.right, &arguments_product.right)
}

fn lcm_basic_shape(native: &Obj, other: &Obj) -> bool {
    if let Obj::Lcm(lcm) = native {
        if let Obj::Lcm(swapped) = other {
            if objs_match_for_pattern(&lcm.left, &swapped.right)
                && objs_match_for_pattern(&lcm.right, &swapped.left)
            {
                return true;
            }
        }
        if normalized_number_is(other, "0")
            && (normalized_number_is(&lcm.left, "0") || normalized_number_is(&lcm.right, "0"))
        {
            return true;
        }
    }
    let Obj::Mod(remainder) = native else {
        return false;
    };
    if !normalized_number_is(other, "0") {
        return false;
    }
    let Obj::Lcm(lcm) = remainder.left.as_ref() else {
        return false;
    };
    let Obj::Abs(modulus) = remainder.right.as_ref() else {
        return false;
    };
    objs_match_for_pattern(&modulus.arg, &lcm.left)
        || objs_match_for_pattern(&modulus.arg, &lcm.right)
}

fn min_max_lattice_shape(lattice: &Obj, other: &Obj) -> bool {
    match lattice {
        Obj::Min(min) => {
            if objs_match_for_pattern(&min.left, &min.right)
                && objs_match_for_pattern(&min.left, other)
            {
                return true;
            }
            if let Obj::Min(swapped) = other {
                if objs_match_for_pattern(&min.left, &swapped.right)
                    && objs_match_for_pattern(&min.right, &swapped.left)
                {
                    return true;
                }
            }
            if objs_match_for_pattern(&min.left, other) && max_contains(min.right.as_ref(), other) {
                return true;
            }
            if objs_match_for_pattern(&min.right, other) && max_contains(min.left.as_ref(), other) {
                return true;
            }
            min_associative_shape(min, other)
        }
        Obj::Max(max) => {
            if objs_match_for_pattern(&max.left, &max.right)
                && objs_match_for_pattern(&max.left, other)
            {
                return true;
            }
            if let Obj::Max(swapped) = other {
                if objs_match_for_pattern(&max.left, &swapped.right)
                    && objs_match_for_pattern(&max.right, &swapped.left)
                {
                    return true;
                }
            }
            if objs_match_for_pattern(&max.left, other) && min_contains(max.right.as_ref(), other) {
                return true;
            }
            if objs_match_for_pattern(&max.right, other) && min_contains(max.left.as_ref(), other) {
                return true;
            }
            max_associative_shape(max, other)
        }
        _ => false,
    }
}

fn min_associative_shape(left: &Min, other: &Obj) -> bool {
    let Obj::Min(left_inner) = left.left.as_ref() else {
        return false;
    };
    let Obj::Min(right_outer) = other else {
        return false;
    };
    let Obj::Min(right_inner) = right_outer.right.as_ref() else {
        return false;
    };
    objs_match_for_pattern(&left_inner.left, &right_outer.left)
        && objs_match_for_pattern(&left_inner.right, &right_inner.left)
        && objs_match_for_pattern(&left.right, &right_inner.right)
}

fn max_associative_shape(left: &Max, other: &Obj) -> bool {
    let Obj::Max(left_inner) = left.left.as_ref() else {
        return false;
    };
    let Obj::Max(right_outer) = other else {
        return false;
    };
    let Obj::Max(right_inner) = right_outer.right.as_ref() else {
        return false;
    };
    objs_match_for_pattern(&left_inner.left, &right_outer.left)
        && objs_match_for_pattern(&left_inner.right, &right_inner.left)
        && objs_match_for_pattern(&left.right, &right_inner.right)
}

fn min_contains(obj: &Obj, expected: &Obj) -> bool {
    let Obj::Min(min) = obj else {
        return false;
    };
    objs_match_for_pattern(&min.left, expected) || objs_match_for_pattern(&min.right, expected)
}

fn max_contains(obj: &Obj, expected: &Obj) -> bool {
    let Obj::Max(max) = obj else {
        return false;
    };
    objs_match_for_pattern(&max.left, expected) || objs_match_for_pattern(&max.right, expected)
}

fn rounding_negation_shape(native: &Obj, other: &Obj) -> bool {
    let (arg, expect_floor) = match native {
        Obj::Floor(floor) => (floor.arg.as_ref(), false),
        Obj::Ceil(ceil) => (ceil.arg.as_ref(), true),
        _ => return false,
    };
    let Some(inner) = negative_one_factor(arg) else {
        return false;
    };
    let Some(other_rounding) = negative_one_factor(other) else {
        return false;
    };
    match other_rounding {
        Obj::Floor(floor) if expect_floor => objs_match_for_pattern(inner, &floor.arg),
        Obj::Ceil(ceil) if !expect_floor => objs_match_for_pattern(inner, &ceil.arg),
        _ => false,
    }
}

fn rounding_integer_translation_shift(native: &Obj, other: &Obj) -> Option<Obj> {
    let (arg, is_floor) = match native {
        Obj::Floor(floor) => (floor.arg.as_ref(), true),
        Obj::Ceil(ceil) => (ceil.arg.as_ref(), false),
        _ => return None,
    };
    let Obj::Add(argument_sum) = arg else {
        return None;
    };
    let Obj::Add(result_sum) = other else {
        return None;
    };
    for (rounded, shift) in [
        (result_sum.left.as_ref(), result_sum.right.as_ref()),
        (result_sum.right.as_ref(), result_sum.left.as_ref()),
    ] {
        let rounded_arg = match rounded {
            Obj::Floor(floor) if is_floor => floor.arg.as_ref(),
            Obj::Ceil(ceil) if !is_floor => ceil.arg.as_ref(),
            _ => continue,
        };
        if (objs_match_for_pattern(&argument_sum.left, rounded_arg)
            && objs_match_for_pattern(&argument_sum.right, shift))
            || (objs_match_for_pattern(&argument_sum.right, rounded_arg)
                && objs_match_for_pattern(&argument_sum.left, shift))
        {
            return Some(shift.clone());
        }
    }
    None
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

fn normalized_number_is(obj: &Obj, expected: &str) -> bool {
    obj.evaluate_to_normalized_decimal_number()
        .is_some_and(|number| number.normalized_value == expected)
}
