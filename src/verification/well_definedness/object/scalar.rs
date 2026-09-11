//! Scalar arithmetic and analytic object well-definedness.

use crate::prelude::*;

impl Runtime {
    pub(in crate::verification) fn push_required_real_object_wd_result(
        &mut self,
        steps: &mut SuccessVerifyObjWellDefinedStepsResult,
        object: &Obj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        match object {
            Obj::Abs(value) => {
                self.push_required_real_object_wd_result(steps, &value.arg, verify_state)
            }
            Obj::Sqrt(_) => {
                let dependency_index = steps.children.len();
                steps.push_child(self.verify_child_obj_well_defined_result(
                    object,
                    verify_state,
                    WellDefinedObjChildRole::VerificationDependency { dependency_index },
                )?);
                Ok(())
            }
            Obj::Log(value) => {
                self.push_required_real_object_wd_result(steps, &value.base, verify_state)?;
                self.push_required_real_object_wd_result(steps, &value.arg, verify_state)
            }
            _ => {
                let fact: AtomicFact = self
                    .new_in_fact(object.clone(), StandardSet::R.into(), default_line_file())
                    .into();
                let result = self.verify_atomic_fact(&fact, verify_state)?;
                if result.is_unknown() {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!("obj {object} is not in r")),
                    )));
                }
                steps.push_fact_check(super::success_obj_fact_check(result)?);
                Ok(())
            }
        }
    }

    pub(in crate::verification) fn verify_pow_well_defined_result(
        &mut self,
        value: &Pow,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        for (argument_index, child) in [&value.base, &value.exponent].into_iter().enumerate() {
            steps.push_child(self.verify_child_obj_well_defined_result(
                child,
                verify_state,
                WellDefinedObjChildRole::ConstructorArgument { argument_index },
            )?);
        }
        let zero: Obj = Number::new("0".to_string()).into();
        let complex_natural = AndChainAtomicFact::AndFact(self.new_and_fact(
            vec![
                self.new_in_fact(
                    (*value.base).clone(),
                    StandardSet::C.into(),
                    default_line_file(),
                )
                .into(),
                self.new_in_fact(
                    (*value.exponent).clone(),
                    StandardSet::N.into(),
                    default_line_file(),
                )
                .into(),
            ],
            default_line_file(),
        ));
        let result = self.verify_and_chain_atomic_fact(&complex_natural, verify_state)?;
        if result.is_success() {
            steps.push_fact_check(super::success_obj_fact_check(result)?);
            return Ok(steps);
        }

        let nonzero_complex_integer = AndChainAtomicFact::AndFact(self.new_and_fact(
            vec![
                    self.new_in_fact(
                        (*value.base).clone(),
                        StandardSet::C.into(),
                        default_line_file(),
                    )
                    .into(),
                    self.new_in_fact(
                        (*value.exponent).clone(),
                        StandardSet::Z.into(),
                        default_line_file(),
                    )
                    .into(),
                    self.new_not_equal_fact(
                        (*value.base).clone(),
                        zero.clone(),
                        default_line_file(),
                    )
                    .into(),
                ],
            default_line_file(),
        ));
        let result = self.verify_and_chain_atomic_fact(&nonzero_complex_integer, verify_state)?;
        if result.is_success() {
            steps.push_fact_check(super::success_obj_fact_check(result)?);
            return Ok(steps);
        }

        if self
            .push_required_real_object_wd_result(&mut steps, &value.base, verify_state)
            .is_err()
        {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "base and exponent do not satisfy the pow domain: {}",
                    Obj::Pow(value.clone())
                )),
            )));
        }

        let nonnegative_positive_real = AndChainAtomicFact::AndFact(self.new_and_fact(
            vec![
                    self.new_less_equal_fact(
                        zero.clone(),
                        (*value.base).clone(),
                        default_line_file(),
                    )
                    .into(),
                    self.new_in_fact(
                        (*value.exponent).clone(),
                        StandardSet::R.into(),
                        default_line_file(),
                    )
                    .into(),
                    self.new_greater_fact(
                        (*value.exponent).clone(),
                        zero.clone(),
                        default_line_file(),
                    )
                    .into(),
                ],
            default_line_file(),
        ));
        let result = self.verify_and_chain_atomic_fact(&nonnegative_positive_real, verify_state)?;
        if result.is_success() {
            steps.push_fact_check(super::success_obj_fact_check(result)?);
            return Ok(steps);
        }

        let positive_real = AndChainAtomicFact::AndFact(self.new_and_fact(
            vec![
                    self.new_greater_fact((*value.base).clone(), zero.clone(), default_line_file())
                        .into(),
                    self.new_in_fact(
                        (*value.exponent).clone(),
                        StandardSet::R.into(),
                        default_line_file(),
                    )
                    .into(),
                ],
            default_line_file(),
        ));
        let result = self.verify_and_chain_atomic_fact(&positive_real, verify_state)?;
        if result.is_success() {
            steps.push_fact_check(super::success_obj_fact_check(result)?);
            return Ok(steps);
        }

        let zero_positive_real = AndChainAtomicFact::AndFact(self.new_and_fact(
            vec![
                    self.new_equal_fact((*value.base).clone(), zero.clone(), default_line_file())
                        .into(),
                    self.new_in_fact(
                        (*value.exponent).clone(),
                        StandardSet::R.into(),
                        default_line_file(),
                    )
                    .into(),
                    self.new_greater_fact((*value.exponent).clone(), zero, default_line_file())
                        .into(),
                ],
            default_line_file(),
        ));
        let result = self.verify_and_chain_atomic_fact(&zero_positive_real, verify_state)?;
        if result.is_success() {
            steps.push_fact_check(super::success_obj_fact_check(result)?);
            return Ok(steps);
        }

        let domain = self.new_or_fact(
            vec![nonnegative_positive_real, positive_real, zero_positive_real],
            default_line_file(),
        );
        let result = self.verify_or_fact(&domain, verify_state)?;
        if result.is_success() {
            steps.push_fact_check(super::success_obj_fact_check(result)?);
            return Ok(steps);
        }
        Err(RuntimeError::from(WellDefinedRuntimeError(
            RuntimeErrorStruct::new_with_just_msg(format!(
                "base and exponent do not satisfy the pow domain: {}",
                Obj::Pow(value.clone())
            )),
        )))
    }

    /// Mathematical contract: require the object to be provably complex.
    pub(in crate::verification) fn require_obj_in_c(
        &mut self,
        obj: &Obj,
        verify_state: &VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
        let c_obj = StandardSet::C.into();
        let in_fact = self.new_in_fact(obj.clone(), c_obj, default_line_file());
        let result = self.verify_atomic_fact(&in_fact.into(), verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!("obj {} is not in C", obj)),
            )));
        }
        Ok(result)
    }
}

impl Runtime {
    pub(in crate::verification) fn verify_add_well_defined_result(
        &mut self,
        add: &Add,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        steps.push_child(self.verify_child_obj_well_defined_result(
            &add.left,
            verify_state,
            WellDefinedObjChildRole::BuiltinArgument { argument_index: 0 },
        )?);
        steps.push_child(self.verify_child_obj_well_defined_result(
            &add.right,
            verify_state,
            WellDefinedObjChildRole::BuiltinArgument { argument_index: 1 },
        )?);
        let parent: Obj = add.clone().into();
        let left = self.require_obj_in_c(&add.left, verify_state)?;
        steps.push_target_requirement(super::success_obj_target_requirement(
            parent.clone(),
            WellDefinednessRequirementRole::BuiltinArgumentMembership { argument_index: 0 },
            left,
        )?);
        let right = self.require_obj_in_c(&add.right, verify_state)?;
        steps.push_target_requirement(super::success_obj_target_requirement(
            parent,
            WellDefinednessRequirementRole::BuiltinArgumentMembership { argument_index: 1 },
            right,
        )?);
        Ok(steps)
    }

    pub(in crate::verification) fn verify_sub_well_defined_result(
        &mut self,
        sub: &Sub,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        steps.push_child(self.verify_child_obj_well_defined_result(
            &sub.left,
            verify_state,
            WellDefinedObjChildRole::BuiltinArgument { argument_index: 0 },
        )?);
        steps.push_child(self.verify_child_obj_well_defined_result(
            &sub.right,
            verify_state,
            WellDefinedObjChildRole::BuiltinArgument { argument_index: 1 },
        )?);
        let parent: Obj = sub.clone().into();
        let left = self.require_obj_in_c(&sub.left, verify_state)?;
        steps.push_target_requirement(super::success_obj_target_requirement(
            parent.clone(),
            WellDefinednessRequirementRole::BuiltinArgumentMembership { argument_index: 0 },
            left,
        )?);
        let right = self.require_obj_in_c(&sub.right, verify_state)?;
        steps.push_target_requirement(super::success_obj_target_requirement(
            parent,
            WellDefinednessRequirementRole::BuiltinArgumentMembership { argument_index: 1 },
            right,
        )?);
        Ok(steps)
    }

    pub(in crate::verification) fn verify_mul_well_defined_result(
        &mut self,
        mul: &Mul,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        steps.push_child(self.verify_child_obj_well_defined_result(
            &mul.left,
            verify_state,
            WellDefinedObjChildRole::BuiltinArgument { argument_index: 0 },
        )?);
        steps.push_child(self.verify_child_obj_well_defined_result(
            &mul.right,
            verify_state,
            WellDefinedObjChildRole::BuiltinArgument { argument_index: 1 },
        )?);
        let parent: Obj = mul.clone().into();
        let left = self.require_obj_in_c(&mul.left, verify_state)?;
        steps.push_target_requirement(super::success_obj_target_requirement(
            parent.clone(),
            WellDefinednessRequirementRole::BuiltinArgumentMembership { argument_index: 0 },
            left,
        )?);
        let right = self.require_obj_in_c(&mul.right, verify_state)?;
        steps.push_target_requirement(super::success_obj_target_requirement(
            parent,
            WellDefinednessRequirementRole::BuiltinArgumentMembership { argument_index: 1 },
            right,
        )?);
        Ok(steps)
    }

    pub(in crate::verification) fn verify_div_well_defined_result(
        &mut self,
        div: &Div,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        steps.push_child(self.verify_child_obj_well_defined_result(
            &div.left,
            verify_state,
            WellDefinedObjChildRole::BuiltinArgument { argument_index: 0 },
        )?);
        steps.push_child(self.verify_child_obj_well_defined_result(
            &div.right,
            verify_state,
            WellDefinedObjChildRole::BuiltinArgument { argument_index: 1 },
        )?);

        let parent: Obj = div.clone().into();
        let zero: Obj = Number::new("0".to_string()).into();
        let nonzero: AtomicFact = self
            .new_not_equal_fact((*div.right).clone(), zero, default_line_file())
            .into();
        let nonzero_result = self.verify_atomic_fact(&nonzero, verify_state)?;
        if nonzero_result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "divisor `{}` must be non-zero",
                    div.right
                )),
            )));
        }
        steps.push_target_requirement(super::success_obj_target_requirement(
            parent.clone(),
            WellDefinednessRequirementRole::BuiltinArgumentNonzero { argument_index: 1 },
            nonzero_result,
        )?);
        let left = self.require_obj_in_c(&div.left, verify_state)?;
        steps.push_target_requirement(super::success_obj_target_requirement(
            parent.clone(),
            WellDefinednessRequirementRole::BuiltinArgumentMembership { argument_index: 0 },
            left,
        )?);
        let right = self.require_obj_in_c(&div.right, verify_state)?;
        steps.push_target_requirement(super::success_obj_target_requirement(
            parent,
            WellDefinednessRequirementRole::BuiltinArgumentMembership { argument_index: 1 },
            right,
        )?);
        Ok(steps)
    }
}

impl Runtime {
    fn verify_scalar_constructor_steps_result(
        &mut self,
        arguments: &[Obj],
        requirements: Vec<(AtomicFact, String)>,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        for (argument_index, argument) in arguments.iter().enumerate() {
            steps.push_child(self.verify_child_obj_well_defined_result(
                argument,
                verify_state,
                WellDefinedObjChildRole::ConstructorArgument { argument_index },
            )?);
        }
        for (requirement, message) in requirements {
            let result = self.verify_atomic_fact(&requirement, verify_state)?;
            if result.is_unknown() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(message),
                )));
            }
            steps.push_fact_check(super::success_obj_fact_check(result)?);
        }
        Ok(steps)
    }

    pub(in crate::verification) fn verify_mod_well_defined_result(
        &mut self,
        value: &Mod,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let arguments = [(*value.left).clone(), (*value.right).clone()];
        let mut requirements = vec![
            scalar_membership_requirement(
                self,
                &value.left,
                StandardSet::Z,
                "mod dividend must belong to Z",
            ),
            scalar_membership_requirement(
                self,
                &value.right,
                StandardSet::Z,
                "mod modulus must belong to Z",
            ),
        ];
        if !matches!(value.right.as_ref(), Obj::Gcd(_)) {
            requirements.push((
                self.new_not_equal_fact(
                    (*value.right).clone(),
                    Number::new("0".to_string()).into(),
                    default_line_file(),
                )
                .into(),
                format!("modulus `{}` must be non-zero", value.right),
            ));
        }
        self.verify_scalar_constructor_steps_result(&arguments, requirements, verify_state)
    }

    pub(in crate::verification) fn verify_quot_well_defined_result(
        &mut self,
        value: &Quot,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let arguments = [(*value.left).clone(), (*value.right).clone()];
        let requirements = vec![
            scalar_membership_requirement(
                self,
                &value.left,
                StandardSet::Z,
                "quot dividend must belong to Z",
            ),
            scalar_membership_requirement(
                self,
                &value.right,
                StandardSet::NPos,
                "quot divisor must belong to N+",
            ),
        ];
        self.verify_scalar_constructor_steps_result(&arguments, requirements, verify_state)
    }

    pub(in crate::verification) fn verify_gcd_well_defined_result(
        &mut self,
        value: &Gcd,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let arguments = [(*value.left).clone(), (*value.right).clone()];
        let carrier_requirements = vec![
            scalar_membership_requirement(
                self,
                &value.left,
                StandardSet::Z,
                "gcd left argument must belong to Z",
            ),
            scalar_membership_requirement(
                self,
                &value.right,
                StandardSet::Z,
                "gcd right argument must belong to Z",
            ),
        ];
        let mut steps = self.verify_scalar_constructor_steps_result(
            &arguments,
            carrier_requirements,
            verify_state,
        )?;
        let zero: Obj = Number::new("0".to_string()).into();
        let left_nonzero: AtomicFact = self
            .new_not_equal_fact((*value.left).clone(), zero.clone(), default_line_file())
            .into();
        let right_nonzero: AtomicFact = self
            .new_not_equal_fact((*value.right).clone(), zero, default_line_file())
            .into();
        for selected in [&left_nonzero, &right_nonzero] {
            let result = self.verify_atomic_fact(selected, verify_state)?;
            if result.is_success() {
                steps.push_fact_check(super::success_obj_fact_check(result)?);
                return Ok(steps);
            }
        }
        for branches in [
            vec![left_nonzero.clone().into(), right_nonzero.clone().into()],
            vec![right_nonzero.into(), left_nonzero.into()],
        ] {
            let disjunction = self.new_or_fact(branches, default_line_file());
            let result = self.verify_or_fact(&disjunction, verify_state)?;
            if result.is_success() {
                steps.push_fact_check(super::success_obj_fact_check(result)?);
                return Ok(steps);
            }
        }
        Err(RuntimeError::from(WellDefinedRuntimeError(
            RuntimeErrorStruct::new_with_just_msg(format!(
                "{} requires at least one non-zero argument",
                value
            )),
        )))
    }

    pub(in crate::verification) fn verify_lcm_well_defined_result(
        &mut self,
        value: &Lcm,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_scalar_constructor_steps_result(
            &[(*value.left).clone(), (*value.right).clone()],
            vec![
                scalar_membership_requirement(
                    self,
                    &value.left,
                    StandardSet::Z,
                    "lcm left argument must belong to Z",
                ),
                scalar_membership_requirement(
                    self,
                    &value.right,
                    StandardSet::Z,
                    "lcm right argument must belong to Z",
                ),
            ],
            verify_state,
        )
    }

    pub(in crate::verification) fn verify_abs_well_defined_result(
        &mut self,
        value: &Abs,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_unary_scalar_carrier_result(&value.arg, StandardSet::R, "abs", verify_state)
    }

    pub(in crate::verification) fn verify_floor_well_defined_result(
        &mut self,
        value: &Floor,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_unary_scalar_carrier_result(&value.arg, StandardSet::R, "floor", verify_state)
    }

    pub(in crate::verification) fn verify_ceil_well_defined_result(
        &mut self,
        value: &Ceil,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_unary_scalar_carrier_result(&value.arg, StandardSet::R, "ceil", verify_state)
    }

    pub(in crate::verification) fn verify_min_well_defined_result(
        &mut self,
        value: &Min,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_binary_scalar_carrier_result(
            &value.left,
            &value.right,
            StandardSet::R,
            "min",
            verify_state,
        )
    }

    pub(in crate::verification) fn verify_max_well_defined_result(
        &mut self,
        value: &Max,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_binary_scalar_carrier_result(
            &value.left,
            &value.right,
            StandardSet::R,
            "max",
            verify_state,
        )
    }

    pub(in crate::verification) fn verify_exp_well_defined_result(
        &mut self,
        value: &Exp,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_unary_scalar_carrier_result(&value.arg, StandardSet::R, "exp", verify_state)
    }

    pub(in crate::verification) fn verify_ln_well_defined_result(
        &mut self,
        value: &Ln,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_scalar_constructor_steps_result(
            &[(*value.arg).clone()],
            vec![
                scalar_membership_requirement(
                    self,
                    &value.arg,
                    StandardSet::R,
                    "ln argument must belong to R",
                ),
                (
                    self.new_greater_fact(
                        (*value.arg).clone(),
                        Number::new("0".to_string()).into(),
                        default_line_file(),
                    )
                    .into(),
                    "ln: argument must be a positive real".to_string(),
                ),
            ],
            verify_state,
        )
    }

    pub(in crate::verification) fn verify_sign_well_defined_result(
        &mut self,
        value: &Sign,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_unary_scalar_carrier_result(&value.arg, StandardSet::R, "sign", verify_state)
    }

    pub(in crate::verification) fn verify_factorial_well_defined_result(
        &mut self,
        value: &Factorial,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_unary_scalar_carrier_result(
            &value.arg,
            StandardSet::N,
            "factorial",
            verify_state,
        )
    }

    pub(in crate::verification) fn verify_sin_well_defined_result(
        &mut self,
        value: &Sin,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_unary_scalar_carrier_result(&value.arg, StandardSet::R, "sin", verify_state)
    }

    pub(in crate::verification) fn verify_arcsin_well_defined_result(
        &mut self,
        value: &Arcsin,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let line_file = default_line_file();
        self.verify_scalar_constructor_steps_result(
            &[(*value.arg).clone()],
            vec![
                scalar_membership_requirement(
                    self,
                    &value.arg,
                    StandardSet::R,
                    "arcsin argument must belong to R",
                ),
                (
                    self.new_less_equal_fact(
                        Number::new("-1".to_string()).into(),
                        (*value.arg).clone(),
                        line_file.clone(),
                    )
                    .into(),
                    format!(
                        "arcsin argument `{}` must satisfy -1 <= {}",
                        value.arg, value.arg
                    ),
                ),
                (
                    self.new_less_equal_fact(
                        (*value.arg).clone(),
                        Number::new("1".to_string()).into(),
                        line_file,
                    )
                    .into(),
                    format!(
                        "arcsin argument `{}` must satisfy {} <= 1",
                        value.arg, value.arg
                    ),
                ),
            ],
            verify_state,
        )
    }

    pub(in crate::verification) fn verify_cos_well_defined_result(
        &mut self,
        value: &Cos,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_unary_scalar_carrier_result(&value.arg, StandardSet::R, "cos", verify_state)
    }

    pub(in crate::verification) fn verify_tan_well_defined_result(
        &mut self,
        value: &Tan,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let denominator: Obj = Cos::new((*value.arg).clone()).into();
        self.verify_scalar_constructor_steps_result(
            &[(*value.arg).clone()],
            vec![
                scalar_membership_requirement(
                    self,
                    &value.arg,
                    StandardSet::R,
                    "tan argument must belong to R",
                ),
                (
                    self.new_not_equal_fact(
                        denominator.clone(),
                        Number::new("0".to_string()).into(),
                        default_line_file(),
                    )
                    .into(),
                    format!("tan argument `{}` requires {} != 0", value.arg, denominator),
                ),
            ],
            verify_state,
        )
    }

    pub(in crate::verification) fn verify_cot_well_defined_result(
        &mut self,
        value: &Cot,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let denominator: Obj = Sin::new((*value.arg).clone()).into();
        self.verify_scalar_constructor_steps_result(
            &[(*value.arg).clone()],
            vec![
                scalar_membership_requirement(
                    self,
                    &value.arg,
                    StandardSet::R,
                    "cot argument must belong to R",
                ),
                (
                    self.new_not_equal_fact(
                        denominator.clone(),
                        Number::new("0".to_string()).into(),
                        default_line_file(),
                    )
                    .into(),
                    format!("cot argument `{}` requires {} != 0", value.arg, denominator),
                ),
            ],
            verify_state,
        )
    }

    pub(in crate::verification) fn verify_real_part_well_defined_result(
        &mut self,
        value: &RealPart,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_unary_scalar_carrier_result(
            &value.arg,
            StandardSet::C,
            "real_part",
            verify_state,
        )
    }

    pub(in crate::verification) fn verify_imaginary_part_well_defined_result(
        &mut self,
        value: &ImaginaryPart,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_unary_scalar_carrier_result(
            &value.arg,
            StandardSet::C,
            "imaginary_part",
            verify_state,
        )
    }

    pub(in crate::verification) fn verify_complex_abs_well_defined_result(
        &mut self,
        value: &ComplexAbs,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_unary_scalar_carrier_result(
            &value.arg,
            StandardSet::C,
            "complex_abs",
            verify_state,
        )
    }

    pub(in crate::verification) fn verify_sqrt_well_defined_result(
        &mut self,
        value: &Sqrt,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_scalar_constructor_steps_result(
            &[(*value.arg).clone()],
            vec![
                scalar_membership_requirement(
                    self,
                    &value.arg,
                    StandardSet::R,
                    "sqrt argument must belong to R",
                ),
                (
                    self.new_less_equal_fact(
                        Number::new("0".to_string()).into(),
                        (*value.arg).clone(),
                        default_line_file(),
                    )
                    .into(),
                    "sqrt: argument must be >= 0".to_string(),
                ),
            ],
            verify_state,
        )
    }

    pub(in crate::verification) fn verify_log_well_defined_result(
        &mut self,
        value: &Log,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let zero: Obj = Number::new("0".to_string()).into();
        self.verify_scalar_constructor_steps_result(
            &[(*value.base).clone(), (*value.arg).clone()],
            vec![
                scalar_membership_requirement(
                    self,
                    &value.base,
                    StandardSet::R,
                    "log base must belong to R",
                ),
                scalar_membership_requirement(
                    self,
                    &value.arg,
                    StandardSet::R,
                    "log argument must belong to R",
                ),
                (
                    self.new_greater_fact((*value.base).clone(), zero.clone(), default_line_file())
                        .into(),
                    "log: base must be > 0".to_string(),
                ),
                (
                    self.new_greater_fact((*value.arg).clone(), zero, default_line_file())
                        .into(),
                    "log: argument must be > 0".to_string(),
                ),
                (
                    self.new_not_equal_fact(
                        (*value.base).clone(),
                        Number::new("1".to_string()).into(),
                        default_line_file(),
                    )
                    .into(),
                    "log: base must be != 1".to_string(),
                ),
            ],
            verify_state,
        )
    }

    fn verify_unary_scalar_carrier_result(
        &mut self,
        argument: &Obj,
        carrier: StandardSet,
        _constructor: &str,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_scalar_constructor_steps_result(
            &[argument.clone()],
            vec![scalar_membership_requirement(
                self,
                argument,
                carrier,
                &scalar_carrier_failure_message(argument, carrier),
            )],
            verify_state,
        )
    }

    fn verify_binary_scalar_carrier_result(
        &mut self,
        left: &Obj,
        right: &Obj,
        carrier: StandardSet,
        _constructor: &str,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_scalar_constructor_steps_result(
            &[left.clone(), right.clone()],
            vec![
                scalar_membership_requirement(
                    self,
                    left,
                    carrier,
                    &scalar_carrier_failure_message(left, carrier),
                ),
                scalar_membership_requirement(
                    self,
                    right,
                    carrier,
                    &scalar_carrier_failure_message(right, carrier),
                ),
            ],
            verify_state,
        )
    }
}

fn scalar_membership_requirement(
    runtime: &Runtime,
    argument: &Obj,
    carrier: StandardSet,
    message: &str,
) -> (AtomicFact, String) {
    (
        runtime
            .new_in_fact(argument.clone(), carrier.into(), default_line_file())
            .into(),
        message.to_string(),
    )
}

fn scalar_carrier_failure_message(argument: &Obj, carrier: StandardSet) -> String {
    match carrier {
        StandardSet::R => format!("obj {argument} is not in r"),
        StandardSet::Z => format!("obj {argument} is not in z"),
        StandardSet::N => format!("obj {argument} is not in N"),
        _ => format!("obj {argument} is not in {carrier}"),
    }
}
