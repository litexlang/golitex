use crate::prelude::*;
use crate::verify::verify_equality_by_builtin_rules::verify_equality_by_they_are_the_same;

impl Runtime {
    /// Native complex equalities use stable builtin symbols and intentionally normalize only
    /// the imaginary unit and the first coordinate/modulus interfaces.
    /// Example: `i^2 = -1`, while an arbitrary `(a + b*i) * (c + d*i)` stays opaque.
    pub(super) fn try_verify_native_complex_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
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
            verify_state,
        )? {
            return Ok(Some(complex_equality_result_with_steps(
                left, right, line_file, &reason, steps,
            )));
        }
        if let Some((reason, steps)) = self.try_verify_native_coordinate_equality(
            right,
            left,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(Some(complex_equality_result_with_steps(
                left, right, line_file, &reason, steps,
            )));
        }

        if let Some(result) = self.try_verify_native_complex_abs_equality(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(Some(result));
        }
        if let Some((reason, steps)) = self.native_complex_abs_equality_reason_and_steps(
            right,
            left,
            line_file.clone(),
            verify_state,
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
            if let Some(complex_abs) = native_builtin_call(C_ABS, z.clone()) {
                let known_zero =
                    self.verify_objs_are_equal_known_only(&complex_abs, &zero, line_file.clone());
                if known_zero.is_true() {
                    let Some(mut steps) =
                        self.verify_objects_are_known_complex(&[z], &line_file, verify_state)?
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
        }

        if let Some((z, expected)) = native_reconstruction_pair(left) {
            if verify_equality_by_they_are_the_same(&expected, right) {
                let Some(steps) =
                    self.verify_objects_are_known_complex(&[z], &line_file, verify_state)?
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
        }
        if let Some((z, expected)) = native_reconstruction_pair(right) {
            if verify_equality_by_they_are_the_same(&expected, left) {
                let Some(steps) =
                    self.verify_objects_are_known_complex(&[z], &line_file, verify_state)?
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
        }

        let Some(mut steps) =
            self.verify_objects_are_known_complex(&[left, right], &line_file, verify_state)?
        else {
            return Ok(None);
        };
        if self.objects_have_known_standard_membership(&[left, right], StandardSet::R) {
            return Ok(None);
        }
        let Some(left_re) = native_builtin_call(RE, left.clone()) else {
            return Ok(None);
        };
        let Some(right_re) = native_builtin_call(RE, right.clone()) else {
            return Ok(None);
        };
        let Some(left_img) = native_builtin_call(IMG, left.clone()) else {
            return Ok(None);
        };
        let Some(right_img) = native_builtin_call(IMG, right.clone()) else {
            return Ok(None);
        };
        let re_result =
            self.verify_objs_are_equal_known_only(&left_re, &right_re, line_file.clone());
        if !re_result.is_true() {
            return Ok(None);
        }
        let img_result =
            self.verify_objs_are_equal_known_only(&left_img, &right_img, line_file.clone());
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
                obj_is_literal_zero(&f.left) && native_builtin_call_arg(&f.right, C_ABS).is_some()
            }
            AtomicFact::GreaterEqualFact(f) => {
                obj_is_literal_zero(&f.right) && native_builtin_call_arg(&f.left, C_ABS).is_some()
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
        verify_state: &VerifyState,
    ) -> Result<Option<(String, Vec<StmtResult>)>, RuntimeError> {
        let (coordinate, arg) = if let Some(arg) = native_builtin_call_arg(application, RE) {
            (RE, arg)
        } else if let Some(arg) = native_builtin_call_arg(application, IMG) {
            (IMG, arg)
        } else {
            return Ok(None);
        };

        if obj_is_native_i(arg) {
            let target: Obj =
                Number::new(if coordinate == RE { "0" } else { "1" }.to_string()).into();
            if verify_equality_by_they_are_the_same(&target, expected) {
                return Ok(Some((
                    format!("{coordinate}: native imaginary-unit coordinate"),
                    Vec::new(),
                )));
            }
        }

        if let Some((real_part, imaginary_part)) = linear_complex_parts(arg) {
            let target = if coordinate == RE {
                real_part.clone()
            } else {
                imaginary_part.clone()
            };
            if verify_equality_by_they_are_the_same(&target, expected) {
                let Some(steps) = self.verify_objects_are_known_reals(
                    &[real_part, imaginary_part],
                    &line_file,
                    verify_state,
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

        if verify_equality_by_they_are_the_same(arg, expected) && coordinate == RE {
            let Some(steps) =
                self.verify_objects_are_known_reals(&[arg], &line_file, verify_state)?
            else {
                return Ok(None);
            };
            return Ok(Some(("re: real embedding".to_string(), steps)));
        }
        if obj_is_literal_zero(expected) && coordinate == IMG {
            let Some(steps) =
                self.verify_objects_are_known_reals(&[arg], &line_file, verify_state)?
            else {
                return Ok(None);
            };
            return Ok(Some(("img: real embedding".to_string(), steps)));
        }

        Ok(None)
    }

    fn try_verify_native_complex_abs_equality(
        &mut self,
        application: &Obj,
        expected: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some((reason, steps)) = self.native_complex_abs_equality_reason_and_steps(
            application,
            expected,
            line_file.clone(),
            verify_state,
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
        verify_state: &VerifyState,
    ) -> Result<Option<(String, Vec<StmtResult>)>, RuntimeError> {
        let Some(arg) = native_builtin_call_arg(application, C_ABS) else {
            return Ok(None);
        };
        if obj_is_native_i(arg) && obj_is_literal_one(expected) {
            return Ok(Some(("complex modulus of i".to_string(), Vec::new())));
        }

        let real_abs: Obj = Abs::new(arg.clone()).into();
        if verify_equality_by_they_are_the_same(&real_abs, expected) {
            let Some(steps) =
                self.verify_objects_are_known_reals(&[arg], &line_file, verify_state)?
            else {
                return Ok(None);
            };
            return Ok(Some((
                "complex modulus restricts to real abs".to_string(),
                steps,
            )));
        }

        let Some(definition) = native_complex_abs_definition(arg) else {
            return Ok(None);
        };
        if verify_equality_by_they_are_the_same(&definition, expected) {
            return Ok(Some((
                "complex modulus coordinate definition".to_string(),
                Vec::new(),
            )));
        }

        if obj_is_literal_zero(expected) {
            let zero: Obj = Number::new("0".to_string()).into();
            let arg_zero = self.verify_objs_are_equal_known_only(arg, &zero, line_file.clone());
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
        verify_state: &VerifyState,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        let mut steps = Vec::new();
        for obj in objs {
            let fact: AtomicFact =
                InFact::new((*obj).clone(), StandardSet::C.into(), line_file.clone()).into();
            let result =
                self.verify_non_equational_known_then_builtin_rules_only(&fact, verify_state)?;
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
        1 => native_builtin_identifier_obj(I)?,
        2 => Number::new("-1".to_string()).into(),
        3 => Mul::new(
            Number::new("-1".to_string()).into(),
            native_builtin_identifier_obj(I)?,
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

fn native_reconstruction_pair(obj: &Obj) -> Option<(&Obj, Obj)> {
    let z = obj;
    let re = native_builtin_call(RE, z.clone())?;
    let img = native_builtin_call(IMG, z.clone())?;
    let imaginary_term = Mul::new(img, native_builtin_identifier_obj(I)?).into();
    Some((z, Add::new(re, imaginary_term).into()))
}

fn native_complex_abs_definition(arg: &Obj) -> Option<Obj> {
    let re = native_builtin_call(RE, arg.clone())?;
    let img = native_builtin_call(IMG, arg.clone())?;
    let two: Obj = Number::new("2".to_string()).into();
    let squared_re: Obj = Pow::new(re, two.clone()).into();
    let squared_img: Obj = Pow::new(img, two).into();
    Some(Sqrt::new(Add::new(squared_re, squared_img).into()).into())
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

fn native_builtin_call(name: &str, arg: Obj) -> Option<Obj> {
    let identifier = Identifier::new_bound(name.to_string(), builtin_symbol_ref(name)?);
    Some(FnObj::new(FnObjHead::Identifier(identifier), vec![vec![Box::new(arg)]]).into())
}

fn native_builtin_call_arg<'a>(obj: &'a Obj, name: &str) -> Option<&'a Obj> {
    let Obj::FnObj(fn_obj) = obj else {
        return None;
    };
    let FnObjHead::Identifier(identifier) = fn_obj.head.as_ref() else {
        return None;
    };
    if !identifier.is_builtin(name) {
        return None;
    }
    let [group] = fn_obj.body.as_slice() else {
        return None;
    };
    let [arg] = group.as_slice() else {
        return None;
    };
    Some(arg.as_ref())
}

fn native_builtin_identifier_obj(name: &str) -> Option<Obj> {
    Some(Identifier::new_bound(name.to_string(), builtin_symbol_ref(name)?).into())
}

fn obj_is_native_i(obj: &Obj) -> bool {
    matches!(obj, Obj::Atom(AtomObj::Identifier(identifier)) if identifier.is_builtin(I))
}

fn obj_is_literal_zero(obj: &Obj) -> bool {
    matches!(obj, Obj::Number(number) if number.normalized_value == "0")
}

fn obj_is_literal_one(obj: &Obj) -> bool {
    matches!(obj, Obj::Number(number) if number.normalized_value == "1")
}
