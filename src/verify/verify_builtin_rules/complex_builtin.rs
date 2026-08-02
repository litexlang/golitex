use crate::prelude::*;
use crate::verify::verify_equality_by_builtin_rules::verify_equality_by_they_are_the_same;

impl Runtime {
    /// Native complex equalities use dedicated AST nodes and intentionally normalize only the
    /// imaginary unit and the first coordinate/modulus interfaces.
    /// Example: `i^2 = -1`, while an arbitrary `(a + b*i) * (c + d*i)` stays opaque.
    pub(super) fn try_verify_native_complex_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some((expected, reason)) = native_i_normal_form(left) {
            if native_normal_form_matches(&expected, right) {
                return Ok(Some(complex_equality_result(
                    left, right, line_file, reason,
                )));
            }
        }
        if let Some((expected, reason)) = native_i_normal_form(right) {
            if native_normal_form_matches(&expected, left) {
                return Ok(Some(complex_equality_result(
                    left, right, line_file, reason,
                )));
            }
        }

        if let Some((reason, steps)) = self.try_verify_native_coordinate_equality(
            left,
            right,
            line_file.clone(),
            builtin_state,
        )? {
            return Ok(Some(complex_equality_result_with_steps(
                left, right, line_file, &reason, steps,
            )));
        }
        if let Some((reason, steps)) = self.try_verify_native_coordinate_equality(
            right,
            left,
            line_file.clone(),
            builtin_state,
        )? {
            return Ok(Some(complex_equality_result_with_steps(
                left, right, line_file, &reason, steps,
            )));
        }

        if let Some(result) = self.try_verify_native_complex_abs_equality(
            left,
            right,
            line_file.clone(),
            builtin_state,
        )? {
            return Ok(Some(result));
        }
        if let Some((reason, steps)) = self.native_complex_abs_equality_reason_and_steps(
            right,
            left,
            line_file.clone(),
            builtin_state,
        )? {
            return Ok(Some(complex_equality_result_with_steps(
                left, right, line_file, &reason, steps,
            )));
        }

        let zero: Obj = Number::new("0".to_string()).into();
        let candidate = if obj_is_literal_zero(right) {
            Some(left)
        } else if obj_is_literal_zero(left) {
            Some(right)
        } else {
            None
        };
        if let Some(z) = candidate {
            let complex_abs: Obj = ComplexAbs::new(z.clone()).into();
            let known_zero = self.verify_objs_are_equal_by_known_equality(
                &complex_abs,
                &zero,
                line_file.clone(),
            );
            if known_zero.is_true() {
                let Some(mut steps) =
                    self.verify_objects_are_known_complex(&[z], &line_file, builtin_state)?
                else {
                    return Ok(None);
                };
                steps.push(known_zero);
                return Ok(Some(complex_equality_result_with_steps(
                    left,
                    right,
                    line_file,
                    "complex modulus zero implies zero argument",
                    steps,
                )));
            }
        }

        let (z, expected) = native_reconstruction_pair(left);
        if verify_equality_by_they_are_the_same(&expected, right) {
            let Some(steps) =
                self.verify_objects_are_known_complex(&[z], &line_file, builtin_state)?
            else {
                return Ok(None);
            };
            return Ok(Some(complex_equality_result_with_steps(
                left,
                right,
                line_file,
                "complex reconstruction from real and imaginary coordinates",
                steps,
            )));
        }
        let (z, expected) = native_reconstruction_pair(right);
        if verify_equality_by_they_are_the_same(&expected, left) {
            let Some(steps) =
                self.verify_objects_are_known_complex(&[z], &line_file, builtin_state)?
            else {
                return Ok(None);
            };
            return Ok(Some(complex_equality_result_with_steps(
                left,
                right,
                line_file,
                "complex reconstruction from real and imaginary coordinates",
                steps,
            )));
        }

        let Some(mut steps) =
            self.verify_objects_are_known_complex(&[left, right], &line_file, builtin_state)?
        else {
            return Ok(None);
        };
        if self.objects_have_known_standard_membership(&[left, right], StandardSet::R) {
            return Ok(None);
        }
        let left_re: Obj = RealPart::new(left.clone()).into();
        let right_re: Obj = RealPart::new(right.clone()).into();
        let left_img: Obj = ImaginaryPart::new(left.clone()).into();
        let right_img: Obj = ImaginaryPart::new(right.clone()).into();
        let re_result =
            self.verify_objs_are_equal_by_known_equality(&left_re, &right_re, line_file.clone());
        if !re_result.is_true() {
            return Ok(None);
        }
        let img_result =
            self.verify_objs_are_equal_by_known_equality(&left_img, &right_img, line_file.clone());
        if !img_result.is_true() {
            return Ok(None);
        }
        steps.push(re_result);
        steps.push(img_result);
        Ok(Some(complex_equality_result_with_steps(
            left,
            right,
            line_file,
            "complex extensionality by re and img",
            steps,
        )))
    }

    pub(super) fn try_verify_native_i_nonzero(
        &self,
        not_equal_fact: &NotEqualFact,
    ) -> Option<StmtResult> {
        if (obj_is_native_i(&not_equal_fact.left) && obj_is_literal_zero(&not_equal_fact.right))
            || (obj_is_native_i(&not_equal_fact.right) && obj_is_literal_zero(&not_equal_fact.left))
        {
            return Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    not_equal_fact.clone().into(),
                    "native imaginary unit is nonzero".to_string(),
                    Vec::new(),
                )
                .into(),
            );
        }
        None
    }

    pub(super) fn try_verify_native_complex_abs_nonnegative(
        &self,
        atomic_fact: &AtomicFact,
    ) -> Option<StmtResult> {
        let matches = match atomic_fact {
            AtomicFact::LessEqualFact(f) => {
                obj_is_literal_zero(&f.left) && matches!(&f.right, Obj::ComplexAbs(_))
            }
            AtomicFact::GreaterEqualFact(f) => {
                obj_is_literal_zero(&f.right) && matches!(&f.left, Obj::ComplexAbs(_))
            }
            _ => false,
        };
        matches.then(|| {
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "complex modulus is a nonnegative real".to_string(),
                Vec::new(),
            )
            .into()
        })
    }

    fn try_verify_native_coordinate_equality(
        &mut self,
        application: &Obj,
        expected: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<(String, Vec<StmtResult>)>, RuntimeError> {
        let (coordinate, is_real_part, arg) = match application {
            Obj::RealPart(real_part) => (RE, true, real_part.arg.as_ref()),
            Obj::ImaginaryPart(imaginary_part) => (IMG, false, imaginary_part.arg.as_ref()),
            _ => return Ok(None),
        };

        if obj_is_native_i(arg) {
            let target: Obj = Number::new(if is_real_part { "0" } else { "1" }.to_string()).into();
            if verify_equality_by_they_are_the_same(&target, expected) {
                return Ok(Some((
                    format!("{coordinate}: native imaginary-unit coordinate"),
                    Vec::new(),
                )));
            }
        }

        if let Some((real_part, imaginary_part)) = linear_complex_parts(arg) {
            let target = if is_real_part {
                real_part.clone()
            } else {
                imaginary_part.clone()
            };
            if verify_equality_by_they_are_the_same(&target, expected) {
                let Some(steps) = self.verify_objects_are_known_reals_in_builtin(
                    &[real_part, imaginary_part],
                    &line_file,
                    builtin_state,
                )?
                else {
                    return Ok(None);
                };
                return Ok(Some((
                    format!("{coordinate}: coordinate of a + b*i"),
                    steps,
                )));
            }
        }

        if verify_equality_by_they_are_the_same(arg, expected) && is_real_part {
            let Some(steps) =
                self.verify_objects_are_known_reals_in_builtin(&[arg], &line_file, builtin_state)?
            else {
                return Ok(None);
            };
            return Ok(Some(("re: real embedding".to_string(), steps)));
        }
        if obj_is_literal_zero(expected) && !is_real_part {
            let Some(steps) =
                self.verify_objects_are_known_reals_in_builtin(&[arg], &line_file, builtin_state)?
            else {
                return Ok(None);
            };
            return Ok(Some(("img: real embedding".to_string(), steps)));
        }

        // Coordinates respect a known equality of complex numbers.
        // Example: `z = w` implies `re(z) = re(w)` and `img(z) = img(w)`.
        let expected_coordinate_arg = match expected {
            Obj::RealPart(real_part) if is_real_part => Some(real_part.arg.as_ref()),
            Obj::ImaginaryPart(imaginary_part) if !is_real_part => {
                Some(imaginary_part.arg.as_ref())
            }
            _ => None,
        };
        if let Some(expected_arg) = expected_coordinate_arg {
            let known =
                self.verify_objs_are_equal_by_known_equality(arg, expected_arg, line_file.clone());
            if known.is_true() {
                return Ok(Some((
                    format!("{coordinate}: coordinates respect complex equality"),
                    vec![known],
                )));
            }
        }

        // Complex coordinates distribute over addition and subtraction.
        // Example: `re(z + w) = re(z) + re(w)` and `img(z - w) = img(z) - img(w)`.
        let additive_target = match arg {
            Obj::Add(add) => Some(
                Add::new(
                    native_coordinate(add.left.as_ref(), is_real_part),
                    native_coordinate(add.right.as_ref(), is_real_part),
                )
                .into(),
            ),
            Obj::Sub(sub) => Some(
                Sub::new(
                    native_coordinate(sub.left.as_ref(), is_real_part),
                    native_coordinate(sub.right.as_ref(), is_real_part),
                )
                .into(),
            ),
            _ => None,
        };
        if let Some(target) = additive_target {
            if verify_equality_by_they_are_the_same(&target, expected) {
                let operands = match arg {
                    Obj::Add(add) => [add.left.as_ref(), add.right.as_ref()],
                    Obj::Sub(sub) => [sub.left.as_ref(), sub.right.as_ref()],
                    _ => unreachable!(),
                };
                let Some(steps) =
                    self.verify_objects_are_known_complex(&operands, &line_file, builtin_state)?
                else {
                    return Ok(None);
                };
                return Ok(Some((
                    format!("{coordinate}: coordinate of complex sum or difference"),
                    steps,
                )));
            }
        }

        // Complex multiplication follows the usual coordinate formulas.
        // Example: `re(z*w) = re(z)*re(w) - img(z)*img(w)`.
        if let Obj::Mul(mul) = arg {
            let left_re = native_coordinate(mul.left.as_ref(), true);
            let left_img = native_coordinate(mul.left.as_ref(), false);
            let right_re = native_coordinate(mul.right.as_ref(), true);
            let right_img = native_coordinate(mul.right.as_ref(), false);
            let target: Obj = if is_real_part {
                Sub::new(
                    Mul::new(left_re, right_re).into(),
                    Mul::new(left_img, right_img).into(),
                )
                .into()
            } else {
                Add::new(
                    Mul::new(left_re, right_img).into(),
                    Mul::new(left_img, right_re).into(),
                )
                .into()
            };
            if verify_equality_by_they_are_the_same(&target, expected) {
                let Some(steps) = self.verify_objects_are_known_complex(
                    &[mul.left.as_ref(), mul.right.as_ref()],
                    &line_file,
                    builtin_state,
                )?
                else {
                    return Ok(None);
                };
                return Ok(Some((
                    format!("{coordinate}: coordinate of complex product"),
                    steps,
                )));
            }
        }

        Ok(None)
    }

    fn try_verify_native_complex_abs_equality(
        &mut self,
        application: &Obj,
        expected: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some((reason, steps)) = self.native_complex_abs_equality_reason_and_steps(
            application,
            expected,
            line_file.clone(),
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        Ok(Some(complex_equality_result_with_steps(
            application,
            expected,
            line_file,
            &reason,
            steps,
        )))
    }

    fn native_complex_abs_equality_reason_and_steps(
        &mut self,
        application: &Obj,
        expected: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<(String, Vec<StmtResult>)>, RuntimeError> {
        let Obj::ComplexAbs(complex_abs) = application else {
            return Ok(None);
        };
        let arg = complex_abs.arg.as_ref();
        if obj_is_native_i(arg) && obj_is_literal_one(expected) {
            return Ok(Some(("complex modulus of i".to_string(), Vec::new())));
        }

        let real_abs: Obj = Abs::new(arg.clone()).into();
        if verify_equality_by_they_are_the_same(&real_abs, expected) {
            let Some(steps) =
                self.verify_objects_are_known_reals_in_builtin(&[arg], &line_file, builtin_state)?
            else {
                return Ok(None);
            };
            return Ok(Some((
                "complex modulus restricts to real abs".to_string(),
                steps,
            )));
        }

        let definition = native_complex_abs_definition(arg);
        if verify_equality_by_they_are_the_same(&definition, expected) {
            return Ok(Some((
                "complex modulus coordinate definition".to_string(),
                Vec::new(),
            )));
        }

        if obj_is_literal_zero(expected) {
            let zero: Obj = Number::new("0".to_string()).into();
            let arg_zero =
                self.verify_objs_are_equal_by_known_equality(arg, &zero, line_file.clone());
            if arg_zero.is_true() {
                return Ok(Some((
                    "complex modulus is zero when its argument is zero".to_string(),
                    vec![arg_zero],
                )));
            }
        }
        Ok(None)
    }

    fn verify_objects_are_known_complex(
        &mut self,
        objs: &[&Obj],
        line_file: &LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        let mut steps = Vec::new();
        for obj in objs {
            let fact: AtomicFact =
                InFact::new((*obj).clone(), StandardSet::C.into(), line_file.clone()).into();
            let result = self.verify_builtin_rule_premise(&fact, builtin_state)?;
            if !result.is_true() {
                return Ok(None);
            }
            steps.push(result);
        }
        Ok(Some(steps))
    }

    fn objects_have_known_standard_membership(&self, objs: &[&Obj], set: StandardSet) -> bool {
        for obj in objs {
            let has_membership =
                self.known_sets_containing_obj(obj)
                    .iter()
                    .any(|known_set| match known_set {
                        Obj::StandardSet(known) => {
                            std::mem::discriminant(known) == std::mem::discriminant(&set)
                        }
                        _ => false,
                    });
            if !has_membership {
                return false;
            }
        }
        true
    }
}

fn complex_equality_result(
    left: &Obj,
    right: &Obj,
    line_file: LineFile,
    reason: &str,
) -> StmtResult {
    complex_equality_result_with_steps(left, right, line_file, reason, Vec::new())
}

fn complex_equality_result_with_steps(
    left: &Obj,
    right: &Obj,
    line_file: LineFile,
    reason: &str,
    steps: Vec<StmtResult>,
) -> StmtResult {
    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
        EqualFact::new(left.clone(), right.clone(), line_file).into(),
        reason.to_string(),
        steps,
    )
    .into()
}

fn native_i_normal_form(obj: &Obj) -> Option<(Obj, &'static str)> {
    if let Obj::Mul(mul) = obj {
        if obj_is_native_i(mul.left.as_ref()) && obj_is_native_i(mul.right.as_ref()) {
            return Some((
                Number::new("-1".to_string()).into(),
                "native imaginary unit multiplication",
            ));
        }
    }
    let Obj::Pow(pow) = obj else {
        return None;
    };
    if !obj_is_native_i(pow.base.as_ref()) {
        return None;
    }
    let exponent = pow.exponent.evaluate_to_normalized_decimal_number()?;
    let exponent = exponent.normalized_value.parse::<i128>().ok()?;
    let normalized = match exponent.rem_euclid(4) {
        0 => Number::new("1".to_string()).into(),
        1 => ImaginaryUnit::new().into(),
        2 => Number::new("-1".to_string()).into(),
        3 => Mul::new(
            Number::new("-1".to_string()).into(),
            ImaginaryUnit::new().into(),
        )
        .into(),
        _ => unreachable!(),
    };
    Some((normalized, "native imaginary unit integer-power cycle"))
}

fn native_normal_form_matches(expected: &Obj, target: &Obj) -> bool {
    if verify_equality_by_they_are_the_same(expected, target) {
        return true;
    }
    match (
        expected.evaluate_to_normalized_decimal_number(),
        target.evaluate_to_normalized_decimal_number(),
    ) {
        (Some(expected_number), Some(target_number)) => {
            expected_number.normalized_value == target_number.normalized_value
        }
        _ => false,
    }
}

fn native_reconstruction_pair(obj: &Obj) -> (&Obj, Obj) {
    let z = obj;
    let re: Obj = RealPart::new(z.clone()).into();
    let img: Obj = ImaginaryPart::new(z.clone()).into();
    let imaginary_term = Mul::new(img, ImaginaryUnit::new().into()).into();
    (z, Add::new(re, imaginary_term).into())
}

fn native_complex_abs_definition(arg: &Obj) -> Obj {
    let re: Obj = RealPart::new(arg.clone()).into();
    let img: Obj = ImaginaryPart::new(arg.clone()).into();
    let two: Obj = Number::new("2".to_string()).into();
    let squared_re: Obj = Pow::new(re, two.clone()).into();
    let squared_img: Obj = Pow::new(img, two).into();
    Sqrt::new(Add::new(squared_re, squared_img).into()).into()
}

fn native_coordinate(arg: &Obj, is_real_part: bool) -> Obj {
    if is_real_part {
        RealPart::new(arg.clone()).into()
    } else {
        ImaginaryPart::new(arg.clone()).into()
    }
}

fn linear_complex_parts(obj: &Obj) -> Option<(&Obj, &Obj)> {
    let Obj::Add(add) = obj else {
        return None;
    };
    let Obj::Mul(mul) = add.right.as_ref() else {
        return None;
    };
    if obj_is_native_i(mul.right.as_ref()) {
        Some((add.left.as_ref(), mul.left.as_ref()))
    } else if obj_is_native_i(mul.left.as_ref()) {
        Some((add.left.as_ref(), mul.right.as_ref()))
    } else {
        None
    }
}

fn obj_is_native_i(obj: &Obj) -> bool {
    matches!(obj, Obj::ImaginaryUnit(_))
}

fn obj_is_literal_zero(obj: &Obj) -> bool {
    matches!(obj, Obj::Number(number) if number.normalized_value == "0")
}

fn obj_is_literal_one(obj: &Obj) -> bool {
    matches!(obj, Obj::Number(number) if number.normalized_value == "1")
}
