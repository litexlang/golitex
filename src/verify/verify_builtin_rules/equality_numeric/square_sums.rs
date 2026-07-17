use super::*;

impl Runtime {
    // Two real squares sum to zero when both bases are zero.
    // Example: from `a = 0` and `b = 0`, prove `a^2 + b^2 = 0`.
    pub(crate) fn try_verify_square_sum_zero_from_zero_components(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let square_sum = if Self::obj_is_builtin_literal_zero(left) {
            right
        } else if Self::obj_is_builtin_literal_zero(right) {
            left
        } else {
            return Ok(None);
        };
        let Some((first_base, second_base)) = square_sum_bases(square_sum) else {
            return Ok(None);
        };
        let Some(mut steps) = self.verify_objects_are_known_reals(
            &[&first_base, &second_base],
            &line_file,
            verify_state,
        )?
        else {
            return Ok(None);
        };

        let zero = Self::literal_zero_obj_for_abs_builtin();
        let first_zero =
            self.verify_objs_are_equal_known_only(&first_base, &zero, line_file.clone());
        let second_zero =
            self.verify_objs_are_equal_known_only(&second_base, &zero, line_file.clone());
        if !first_zero.is_true() || !second_zero.is_true() {
            return Ok(None);
        }
        steps.push(first_zero);
        steps.push(second_zero);

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "equality: a^2 + b^2 = 0 from a = 0 and b = 0 over R".to_string(),
                steps,
            )
            .into(),
        ))
    }

    // A zero sum of two real squares has each component equal to zero.
    // Example: from `a^2 + b^2 = 0`, prove `a = 0` and separately `b = 0`.
    pub(crate) fn try_verify_square_sum_component_zero_from_known_sum_zero(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let target = if Self::obj_is_builtin_literal_zero(left) {
            right
        } else if Self::obj_is_builtin_literal_zero(right) {
            left
        } else {
            return Ok(None);
        };
        let zero = Self::literal_zero_obj_for_abs_builtin();
        let zero_key = zero.to_string();
        let zero_equal_objs_by_env: Vec<Vec<Obj>> = self
            .iter_environments_from_top()
            .filter_map(|environment| {
                environment
                    .known_equality
                    .get(&zero_key)
                    .map(|(_, equal_objs)| equal_objs.iter().cloned().collect())
            })
            .collect();

        for zero_equal_objs in zero_equal_objs_by_env {
            for square_sum in zero_equal_objs {
                let Some((first_base, second_base)) = square_sum_bases(&square_sum) else {
                    continue;
                };
                let Some(mut steps) = self.verify_objects_are_known_reals(
                    &[&first_base, &second_base],
                    &line_file,
                    verify_state,
                )?
                else {
                    continue;
                };
                let sum_zero =
                    self.verify_objs_are_equal_known_only(&square_sum, &zero, line_file.clone());
                if !sum_zero.is_true() {
                    continue;
                }
                let first_matches = self.verify_zero_product_factor_matches_target(
                    target,
                    &first_base,
                    line_file.clone(),
                    verify_state,
                )?;
                let second_matches = self.verify_zero_product_factor_matches_target(
                    target,
                    &second_base,
                    line_file.clone(),
                    verify_state,
                )?;
                if !first_matches.is_true() && !second_matches.is_true() {
                    continue;
                }
                steps.push(sum_zero);
                if first_matches.is_true() {
                    steps.push(first_matches);
                } else {
                    steps.push(second_matches);
                }
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        EqualFact::new(left.clone(), right.clone(), line_file).into(),
                        "equality: a = 0 from a^2 + b^2 = 0 over R".to_string(),
                        steps,
                    )
                    .into(),
                ));
            }
        }

        Ok(None)
    }
}

fn square_sum_bases(obj: &Obj) -> Option<(Obj, Obj)> {
    let Obj::Add(sum) = obj else {
        return None;
    };
    let first_base = square_base(sum.left.as_ref())?;
    let second_base = square_base(sum.right.as_ref())?;
    Some((first_base, second_base))
}

fn square_base(obj: &Obj) -> Option<Obj> {
    let Obj::Pow(power) = obj else {
        return None;
    };
    if Runtime::obj_is_builtin_literal_two(power.exponent.as_ref()) {
        return Some(power.base.as_ref().clone());
    }
    None
}
