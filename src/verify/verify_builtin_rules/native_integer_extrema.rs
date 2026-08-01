use crate::prelude::*;
use crate::verify::verify_equality_by_builtin_rules::verify_equality_by_they_are_the_same;

impl Runtime {
    // Integer inputs are fixed by both rounding operations.
    // Example: `n $in Z` proves `floor(n) = n` and `ceil(n) = n`.
    pub(super) fn try_verify_native_rounding_integer_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (arg, other, name) = match (left, right) {
            (Obj::Floor(value), other) | (other, Obj::Floor(value)) => {
                (value.arg.as_ref(), other, FLOOR)
            }
            (Obj::Ceil(value), other) | (other, Obj::Ceil(value)) => {
                (value.arg.as_ref(), other, CEIL)
            }
            _ => return Ok(None),
        };
        if !verify_equality_by_they_are_the_same(arg, other) {
            return Ok(None);
        }
        let integer_fact: AtomicFact =
            InFact::new(arg.clone(), StandardSet::Z.into(), line_file.clone()).into();
        let premise_result = self.verify_builtin_rule_premise(&integer_fact, builtin_state)?;
        if premise_result.is_unknown() {
            return Ok(None);
        }
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                format!("{name} fixes integer inputs"),
                vec![premise_result],
            )
            .into(),
        ))
    }

    // Selects the appropriate argument once its order is known.
    // Example: `a <= b` proves `min(a, b) = a` and `max(a, b) = b`.
    pub(super) fn try_verify_native_min_max_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (first_arg, second_arg, selected, is_min) = match (left, right) {
            (Obj::Min(value), selected) | (selected, Obj::Min(value)) => {
                (value.left.as_ref(), value.right.as_ref(), selected, true)
            }
            (Obj::Max(value), selected) | (selected, Obj::Max(value)) => {
                (value.left.as_ref(), value.right.as_ref(), selected, false)
            }
            _ => return Ok(None),
        };
        let selected_is_first = verify_equality_by_they_are_the_same(selected, first_arg);
        let selected_is_second = verify_equality_by_they_are_the_same(selected, second_arg);
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
        let premise_result = self.verify_builtin_rule_premise(&premise.into(), builtin_state)?;
        if premise_result.is_unknown() {
            return Ok(None);
        }
        let name = if is_min { "min" } else { "max" };
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
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
        &self,
        atomic_fact: &AtomicFact,
    ) -> Option<StmtResult> {
        let (left, right, is_strict) = match atomic_fact {
            AtomicFact::LessFact(f) => (&f.left, &f.right, true),
            AtomicFact::LessEqualFact(f) => (&f.left, &f.right, false),
            _ => return None,
        };
        let verified = if is_strict {
            floor_upper_shape(left, right) || ceil_lower_shape(left, right)
        } else {
            floor_lower_shape(left, right)
                || ceil_upper_shape(left, right)
                || min_lower_shape(left, right)
                || max_upper_shape(left, right)
        };
        verified.then(|| {
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "native rounding/extremum characteristic order bound".to_string(),
                Vec::new(),
            )
            .into()
        })
    }

    // The least common multiple and positive gcd satisfy lcm(a,b)gcd(a,b)=|ab|.
    // Example: `a != 0 or b != 0` proves
    // `lcm(a, b) * gcd(a, b) = abs(a * b)`.
    pub(super) fn try_verify_native_lcm_gcd_product_equality(
        &self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Option<StmtResult> {
        if !lcm_gcd_product_shape(left, right) && !lcm_gcd_product_shape(right, left) {
            return None;
        }
        Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "lcm times gcd is the absolute product".to_string(),
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
    verify_equality_by_they_are_the_same(&floor.arg, right)
}

fn floor_upper_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::Add(add) = right else {
        return false;
    };
    let Obj::Floor(floor) = add.left.as_ref() else {
        return false;
    };
    verify_equality_by_they_are_the_same(left, &floor.arg)
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
    verify_equality_by_they_are_the_same(&ceil.arg, right)
        && sub
            .right
            .evaluate_to_normalized_decimal_number()
            .is_some_and(|n| n.normalized_value == "1")
}

fn ceil_upper_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::Ceil(ceil) = right else {
        return false;
    };
    verify_equality_by_they_are_the_same(left, &ceil.arg)
}

fn min_lower_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::Min(min) = left else {
        return false;
    };
    verify_equality_by_they_are_the_same(&min.left, right)
        || verify_equality_by_they_are_the_same(&min.right, right)
}

fn max_upper_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::Max(max) = right else {
        return false;
    };
    verify_equality_by_they_are_the_same(left, &max.left)
        || verify_equality_by_they_are_the_same(left, &max.right)
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
    verify_equality_by_they_are_the_same(&lcm.left, &gcd.left)
        && verify_equality_by_they_are_the_same(&lcm.right, &gcd.right)
        && verify_equality_by_they_are_the_same(&lcm.left, &arguments_product.left)
        && verify_equality_by_they_are_the_same(&lcm.right, &arguments_product.right)
}
