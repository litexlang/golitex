//! Scalar arithmetic and analytic object well-definedness.

use crate::prelude::*;

impl Runtime {
    pub(in crate::verify) fn push_required_real_object_wd_result(
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
                let fact: AtomicFact =
                    InFact::new(object.clone(), StandardSet::R.into(), default_line_file()).into();
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

    pub(in crate::verify) fn verify_pow_well_defined_result(
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
        let complex_natural = AndChainAtomicFact::AndFact(AndFact::new(
            vec![
                InFact::new(
                    (*value.base).clone(),
                    StandardSet::C.into(),
                    default_line_file(),
                )
                .into(),
                InFact::new(
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

        let nonzero_complex_integer = AndChainAtomicFact::AndFact(AndFact::new(
            vec![
                InFact::new(
                    (*value.base).clone(),
                    StandardSet::C.into(),
                    default_line_file(),
                )
                .into(),
                InFact::new(
                    (*value.exponent).clone(),
                    StandardSet::Z.into(),
                    default_line_file(),
                )
                .into(),
                NotEqualFact::new((*value.base).clone(), zero.clone(), default_line_file()).into(),
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

        let nonnegative_positive_real = AndChainAtomicFact::AndFact(AndFact::new(
            vec![
                LessEqualFact::new(zero.clone(), (*value.base).clone(), default_line_file()).into(),
                InFact::new(
                    (*value.exponent).clone(),
                    StandardSet::R.into(),
                    default_line_file(),
                )
                .into(),
                GreaterFact::new((*value.exponent).clone(), zero.clone(), default_line_file())
                    .into(),
            ],
            default_line_file(),
        ));
        let result = self.verify_and_chain_atomic_fact(&nonnegative_positive_real, verify_state)?;
        if result.is_success() {
            steps.push_fact_check(super::success_obj_fact_check(result)?);
            return Ok(steps);
        }

        let positive_real = AndChainAtomicFact::AndFact(AndFact::new(
            vec![
                GreaterFact::new((*value.base).clone(), zero.clone(), default_line_file()).into(),
                InFact::new(
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

        let zero_positive_real = AndChainAtomicFact::AndFact(AndFact::new(
            vec![
                EqualFact::new((*value.base).clone(), zero.clone(), default_line_file()).into(),
                InFact::new(
                    (*value.exponent).clone(),
                    StandardSet::R.into(),
                    default_line_file(),
                )
                .into(),
                GreaterFact::new((*value.exponent).clone(), zero, default_line_file()).into(),
            ],
            default_line_file(),
        ));
        let result = self.verify_and_chain_atomic_fact(&zero_positive_real, verify_state)?;
        if result.is_success() {
            steps.push_fact_check(super::success_obj_fact_check(result)?);
            return Ok(steps);
        }

        let domain = OrFact::new(
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
    pub(in crate::verify) fn require_obj_in_c(
        &mut self,
        obj: &Obj,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let c_obj = StandardSet::C.into();
        let in_fact = InFact::new(obj.clone(), c_obj, default_line_file());
        let result = self.verify_atomic_fact(&in_fact.into(), verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!("obj {} is not in C", obj)),
            )));
        }
        Ok(result)
    }

    /// Mathematical contract: require the object to be provably real; the
    /// recognized real-valued constructors discharge this through their own
    /// domain contracts.
    pub(in crate::verify) fn require_obj_in_r(
        &mut self,
        obj: &Obj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        if let Obj::Abs(a) = obj {
            return self.require_obj_in_r(&a.arg, verify_state);
        }
        if let Obj::Sqrt(s) = obj {
            return self.verify_sqrt_well_defined(s, verify_state);
        }
        if let Obj::Log(l) = obj {
            self.require_obj_in_r(&l.base, verify_state)?;
            return self.require_obj_in_r(&l.arg, verify_state);
        }
        let r_obj = StandardSet::R.into();
        let element = obj.clone();
        let in_fact = InFact::new(element, r_obj, default_line_file());
        let atomic_fact = AtomicFact::InFact(in_fact);
        let result = self.verify_atomic_fact(&atomic_fact, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "obj {} is not in r",
                    obj.to_string()
                )),
            )));
        }
        Ok(())
    }
}

impl Runtime {
    pub(in crate::verify) fn verify_add_well_defined_result(
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

    pub(in crate::verify) fn verify_sub_well_defined_result(
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

    pub(in crate::verify) fn verify_mul_well_defined_result(
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

    pub(in crate::verify) fn verify_div_well_defined_result(
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
        let nonzero: AtomicFact =
            NotEqualFact::new((*div.right).clone(), zero, default_line_file()).into();
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

    pub(in crate::verify) fn verify_mod_well_defined_result(
        &mut self,
        value: &Mod,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let arguments = [(*value.left).clone(), (*value.right).clone()];
        let mut requirements = vec![
            scalar_membership_requirement(
                &value.left,
                StandardSet::Z,
                "mod dividend must belong to Z",
            ),
            scalar_membership_requirement(
                &value.right,
                StandardSet::Z,
                "mod modulus must belong to Z",
            ),
        ];
        if !matches!(value.right.as_ref(), Obj::Gcd(_)) {
            requirements.push((
                NotEqualFact::new(
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

    pub(in crate::verify) fn verify_quot_well_defined_result(
        &mut self,
        value: &Quot,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let arguments = [(*value.left).clone(), (*value.right).clone()];
        let requirements = vec![
            scalar_membership_requirement(
                &value.left,
                StandardSet::Z,
                "quot dividend must belong to Z",
            ),
            scalar_membership_requirement(
                &value.right,
                StandardSet::NPos,
                "quot divisor must belong to N+",
            ),
        ];
        self.verify_scalar_constructor_steps_result(&arguments, requirements, verify_state)
    }

    pub(in crate::verify) fn verify_gcd_well_defined_result(
        &mut self,
        value: &Gcd,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let arguments = [(*value.left).clone(), (*value.right).clone()];
        let carrier_requirements = vec![
            scalar_membership_requirement(
                &value.left,
                StandardSet::Z,
                "gcd left argument must belong to Z",
            ),
            scalar_membership_requirement(
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
        let left_nonzero: AtomicFact =
            NotEqualFact::new((*value.left).clone(), zero.clone(), default_line_file()).into();
        let right_nonzero: AtomicFact =
            NotEqualFact::new((*value.right).clone(), zero, default_line_file()).into();
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
            let disjunction = OrFact::new(branches, default_line_file());
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

    pub(in crate::verify) fn verify_lcm_well_defined_result(
        &mut self,
        value: &Lcm,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_scalar_constructor_steps_result(
            &[(*value.left).clone(), (*value.right).clone()],
            vec![
                scalar_membership_requirement(
                    &value.left,
                    StandardSet::Z,
                    "lcm left argument must belong to Z",
                ),
                scalar_membership_requirement(
                    &value.right,
                    StandardSet::Z,
                    "lcm right argument must belong to Z",
                ),
            ],
            verify_state,
        )
    }

    pub(in crate::verify) fn verify_abs_well_defined_result(
        &mut self,
        value: &Abs,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_unary_scalar_carrier_result(&value.arg, StandardSet::R, "abs", verify_state)
    }

    pub(in crate::verify) fn verify_floor_well_defined_result(
        &mut self,
        value: &Floor,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_unary_scalar_carrier_result(&value.arg, StandardSet::R, "floor", verify_state)
    }

    pub(in crate::verify) fn verify_ceil_well_defined_result(
        &mut self,
        value: &Ceil,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_unary_scalar_carrier_result(&value.arg, StandardSet::R, "ceil", verify_state)
    }

    pub(in crate::verify) fn verify_min_well_defined_result(
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

    pub(in crate::verify) fn verify_max_well_defined_result(
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

    pub(in crate::verify) fn verify_exp_well_defined_result(
        &mut self,
        value: &Exp,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_unary_scalar_carrier_result(&value.arg, StandardSet::R, "exp", verify_state)
    }

    pub(in crate::verify) fn verify_ln_well_defined_result(
        &mut self,
        value: &Ln,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_scalar_constructor_steps_result(
            &[(*value.arg).clone()],
            vec![
                scalar_membership_requirement(
                    &value.arg,
                    StandardSet::R,
                    "ln argument must belong to R",
                ),
                (
                    GreaterFact::new(
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

    pub(in crate::verify) fn verify_sign_well_defined_result(
        &mut self,
        value: &Sign,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_unary_scalar_carrier_result(&value.arg, StandardSet::R, "sign", verify_state)
    }

    pub(in crate::verify) fn verify_factorial_well_defined_result(
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

    pub(in crate::verify) fn verify_sin_well_defined_result(
        &mut self,
        value: &Sin,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_unary_scalar_carrier_result(&value.arg, StandardSet::R, "sin", verify_state)
    }

    pub(in crate::verify) fn verify_arcsin_well_defined_result(
        &mut self,
        value: &Arcsin,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let line_file = default_line_file();
        self.verify_scalar_constructor_steps_result(
            &[(*value.arg).clone()],
            vec![
                scalar_membership_requirement(
                    &value.arg,
                    StandardSet::R,
                    "arcsin argument must belong to R",
                ),
                (
                    LessEqualFact::new(
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
                    LessEqualFact::new(
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

    pub(in crate::verify) fn verify_cos_well_defined_result(
        &mut self,
        value: &Cos,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_unary_scalar_carrier_result(&value.arg, StandardSet::R, "cos", verify_state)
    }

    pub(in crate::verify) fn verify_tan_well_defined_result(
        &mut self,
        value: &Tan,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let denominator: Obj = Cos::new((*value.arg).clone()).into();
        self.verify_scalar_constructor_steps_result(
            &[(*value.arg).clone()],
            vec![
                scalar_membership_requirement(
                    &value.arg,
                    StandardSet::R,
                    "tan argument must belong to R",
                ),
                (
                    NotEqualFact::new(
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

    pub(in crate::verify) fn verify_cot_well_defined_result(
        &mut self,
        value: &Cot,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let denominator: Obj = Sin::new((*value.arg).clone()).into();
        self.verify_scalar_constructor_steps_result(
            &[(*value.arg).clone()],
            vec![
                scalar_membership_requirement(
                    &value.arg,
                    StandardSet::R,
                    "cot argument must belong to R",
                ),
                (
                    NotEqualFact::new(
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

    pub(in crate::verify) fn verify_real_part_well_defined_result(
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

    pub(in crate::verify) fn verify_imaginary_part_well_defined_result(
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

    pub(in crate::verify) fn verify_complex_abs_well_defined_result(
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

    pub(in crate::verify) fn verify_sqrt_well_defined_result(
        &mut self,
        value: &Sqrt,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_scalar_constructor_steps_result(
            &[(*value.arg).clone()],
            vec![
                scalar_membership_requirement(
                    &value.arg,
                    StandardSet::R,
                    "sqrt argument must belong to R",
                ),
                (
                    LessEqualFact::new(
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

    pub(in crate::verify) fn verify_log_well_defined_result(
        &mut self,
        value: &Log,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let zero: Obj = Number::new("0".to_string()).into();
        self.verify_scalar_constructor_steps_result(
            &[(*value.base).clone(), (*value.arg).clone()],
            vec![
                scalar_membership_requirement(
                    &value.base,
                    StandardSet::R,
                    "log base must belong to R",
                ),
                scalar_membership_requirement(
                    &value.arg,
                    StandardSet::R,
                    "log argument must belong to R",
                ),
                (
                    GreaterFact::new((*value.base).clone(), zero.clone(), default_line_file())
                        .into(),
                    "log: base must be > 0".to_string(),
                ),
                (
                    GreaterFact::new((*value.arg).clone(), zero, default_line_file()).into(),
                    "log: argument must be > 0".to_string(),
                ),
                (
                    NotEqualFact::new(
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
                    left,
                    carrier,
                    &scalar_carrier_failure_message(left, carrier),
                ),
                scalar_membership_requirement(
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
    argument: &Obj,
    carrier: StandardSet,
    message: &str,
) -> (AtomicFact, String) {
    (
        InFact::new(argument.clone(), carrier.into(), default_line_file()).into(),
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

impl Runtime {
    /// Mathematical contract: require the object to be provably integral.
    pub(in crate::verify) fn require_obj_in_z(
        &mut self,
        obj: &Obj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        let z_obj = StandardSet::Z.into();
        let element = obj.clone();
        let in_fact = InFact::new(element, z_obj, default_line_file());
        let atomic_fact = AtomicFact::InFact(in_fact);
        let result = self.verify_atomic_fact(&atomic_fact, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "obj {} is not in z",
                    obj.to_string()
                )),
            )));
        }
        Ok(())
    }

    /// Mathematical contract: require the object to be provably natural.
    pub(in crate::verify) fn require_obj_in_n(
        &mut self,
        obj: &Obj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        let in_fact: AtomicFact =
            InFact::new(obj.clone(), StandardSet::N.into(), default_line_file()).into();
        let result = self.verify_atomic_fact(&in_fact, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!("obj {obj} is not in N")),
            )));
        }
        Ok(())
    }

    /// Mathematical contract: require `left <= right` to be provable in the
    /// current context; checking the obligation does not assume or store it.
    pub(in crate::verify) fn require_less_equal_verified(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: &VerifyState,
        err_detail: String,
    ) -> Result<(), RuntimeError> {
        let f: AtomicFact =
            LessEqualFact::new(left.clone(), right.clone(), default_line_file()).into();
        let r = self.verify_atomic_fact(&f, verify_state)?;
        if r.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(err_detail),
            )));
        }
        Ok(())
    }

    /// Mathematical contract: `a + b` is meaningful when both operands are
    /// well-defined complex scalars.
    pub(in crate::verify) fn verify_add_well_defined(
        &mut self,
        add: &Add,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &add.left,
            verify_state,
            WellDefinedObjChildRole::BuiltinArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &add.right,
            verify_state,
            WellDefinedObjChildRole::BuiltinArgument { argument_index: 1 },
        )?;
        self.require_obj_in_c(&add.left, verify_state)?;
        self.require_obj_in_c(&add.right, verify_state)?;
        Ok(())
    }

    /// Mathematical contract: `a - b` is meaningful when both operands are
    /// well-defined complex scalars.
    pub(in crate::verify) fn verify_sub_well_defined(
        &mut self,
        sub: &Sub,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &sub.left,
            verify_state,
            WellDefinedObjChildRole::BuiltinArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &sub.right,
            verify_state,
            WellDefinedObjChildRole::BuiltinArgument { argument_index: 1 },
        )?;
        self.require_obj_in_c(&sub.left, verify_state)?;
        self.require_obj_in_c(&sub.right, verify_state)?;
        Ok(())
    }

    /// Mathematical contract: `a * b` is meaningful when both operands are
    /// well-defined complex scalars.
    pub(in crate::verify) fn verify_mul_well_defined(
        &mut self,
        mul: &Mul,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &mul.left,
            verify_state,
            WellDefinedObjChildRole::BuiltinArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &mul.right,
            verify_state,
            WellDefinedObjChildRole::BuiltinArgument { argument_index: 1 },
        )?;
        self.require_obj_in_c(&mul.left, verify_state)?;
        self.require_obj_in_c(&mul.right, verify_state)?;
        Ok(())
    }

    /// Mathematical contract: `a / b` is meaningful when `a,b in C` and the
    /// divisor `b` is provably nonzero.
    pub(in crate::verify) fn verify_div_well_defined(
        &mut self,
        div: &Div,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &div.left,
            verify_state,
            WellDefinedObjChildRole::BuiltinArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &div.right,
            verify_state,
            WellDefinedObjChildRole::BuiltinArgument { argument_index: 1 },
        )?;

        let zero: Obj = Number::new("0".to_string()).into();
        let not_equal_fact = NotEqualFact::new((*div.right).clone(), zero, default_line_file());
        let atomic_fact = AtomicFact::NotEqualFact(not_equal_fact);
        let result = self.verify_atomic_fact(&atomic_fact, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "divisor `{}` must be non-zero",
                    div.right.to_string()
                )),
            )));
        }
        self.require_obj_in_c(&div.left, verify_state)?;
        self.require_obj_in_c(&div.right, verify_state)?;
        Ok(())
    }

    /// Mathematical contract: `a mod b` is meaningful for integral operands
    /// with a provably nonzero modulus; a well-defined gcd is already nonzero.
    pub(in crate::verify) fn verify_mod_well_defined(
        &mut self,
        m: &Mod,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &m.left,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &m.right,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
        self.require_obj_in_z(&m.left, verify_state)?;
        self.require_obj_in_z(&m.right, verify_state)?;
        if matches!(m.right.as_ref(), Obj::Gcd(_)) {
            return Ok(());
        }
        let zero: Obj = Number::new("0".to_string()).into();
        let not_equal_fact = NotEqualFact::new((*m.right).clone(), zero, default_line_file());
        let atomic_fact = AtomicFact::NotEqualFact(not_equal_fact);
        let result = self.verify_atomic_fact(&atomic_fact, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "modulus `{}` must be non-zero",
                    m.right.to_string()
                )),
            )));
        }
        Ok(())
    }

    /// Mathematical contract: `quot(a,d)` is the Euclidean integer quotient
    /// for an integer dividend and a positive natural divisor.
    pub(in crate::verify) fn verify_quot_well_defined(
        &mut self,
        quot: &Quot,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &quot.left,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &quot.right,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
        self.require_obj_in_z(&quot.left, verify_state)?;

        let divisor_in_n_pos: AtomicFact = InFact::new(
            (*quot.right).clone(),
            StandardSet::NPos.into(),
            default_line_file(),
        )
        .into();
        let result = self.verify_atomic_fact(&divisor_in_n_pos, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "quot divisor `{}` must be in N+",
                    quot.right
                )),
            )));
        }
        Ok(())
    }

    /// Mathematical contract: `gcd(a,b)` is meaningful for integers when at
    /// least one of `a` and `b` is provably nonzero.
    pub(in crate::verify) fn verify_gcd_well_defined(
        &mut self,
        gcd: &Gcd,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &gcd.left,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &gcd.right,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
        self.require_obj_in_z(&gcd.left, verify_state)?;
        self.require_obj_in_z(&gcd.right, verify_state)?;

        let zero: Obj = Number::new("0".to_string()).into();
        let left_nonzero: AtomicFact =
            NotEqualFact::new((*gcd.left).clone(), zero.clone(), default_line_file()).into();
        let right_nonzero: AtomicFact =
            NotEqualFact::new((*gcd.right).clone(), zero, default_line_file()).into();
        if self
            .verify_atomic_fact(&left_nonzero, verify_state)?
            .is_success()
            || self
                .verify_atomic_fact(&right_nonzero, verify_state)?
                .is_success()
        {
            return Ok(());
        }

        let non_all_zero = OrFact::new(
            vec![
                AndChainAtomicFact::AtomicFact(left_nonzero.clone()),
                AndChainAtomicFact::AtomicFact(right_nonzero.clone()),
            ],
            default_line_file(),
        );
        if self
            .verify_or_fact(&non_all_zero, verify_state)?
            .is_success()
        {
            return Ok(());
        }
        let reversed_non_all_zero = OrFact::new(
            vec![
                AndChainAtomicFact::AtomicFact(right_nonzero),
                AndChainAtomicFact::AtomicFact(left_nonzero),
            ],
            default_line_file(),
        );
        if self
            .verify_or_fact(&reversed_non_all_zero, verify_state)?
            .is_success()
        {
            return Ok(());
        }

        Err(RuntimeError::from(WellDefinedRuntimeError(
            RuntimeErrorStruct::new_with_just_msg(format!(
                "{} requires at least one non-zero argument",
                gcd
            )),
        )))
    }

    /// Mathematical contract: real absolute value `abs(x)` requires a
    /// well-defined real argument.
    pub(in crate::verify) fn verify_abs_well_defined(
        &mut self,
        abs: &Abs,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &abs.arg,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.require_obj_in_r(&abs.arg, verify_state)?;
        Ok(())
    }

    /// Mathematical contract: `lcm(a,b)` is meaningful for well-defined
    /// integer operands, including the all-zero case.
    pub(in crate::verify) fn verify_lcm_well_defined(
        &mut self,
        lcm: &Lcm,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &lcm.left,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &lcm.right,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
        self.require_obj_in_z(&lcm.left, verify_state)?;
        self.require_obj_in_z(&lcm.right, verify_state)
    }

    /// Mathematical contract: `floor(x)` requires a well-defined real `x`.
    pub(in crate::verify) fn verify_floor_well_defined(
        &mut self,
        floor: &Floor,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &floor.arg,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.require_obj_in_r(&floor.arg, verify_state)
    }

    /// Mathematical contract: `ceil(x)` requires a well-defined real `x`.
    pub(in crate::verify) fn verify_ceil_well_defined(
        &mut self,
        ceil: &Ceil,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &ceil.arg,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.require_obj_in_r(&ceil.arg, verify_state)
    }

    /// Mathematical contract: `min(a,b)` requires two well-defined reals.
    pub(in crate::verify) fn verify_min_well_defined(
        &mut self,
        min: &Min,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &min.left,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &min.right,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
        self.require_obj_in_r(&min.left, verify_state)?;
        self.require_obj_in_r(&min.right, verify_state)
    }

    /// Mathematical contract: `max(a,b)` requires two well-defined reals.
    pub(in crate::verify) fn verify_max_well_defined(
        &mut self,
        max: &Max,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &max.left,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &max.right,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
        self.require_obj_in_r(&max.left, verify_state)?;
        self.require_obj_in_r(&max.right, verify_state)
    }

    /// Mathematical contract: real exponential `exp(x)` requires a
    /// well-defined real exponent.
    pub(in crate::verify) fn verify_exp_well_defined(
        &mut self,
        exp: &Exp,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &exp.arg,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.require_obj_in_r(&exp.arg, verify_state)
    }

    /// Mathematical contract: `ln(x)` requires a well-defined positive real
    /// argument.
    pub(in crate::verify) fn verify_ln_well_defined(
        &mut self,
        ln: &Ln,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &ln.arg,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.require_obj_in_r(&ln.arg, verify_state)?;
        let positive: AtomicFact = GreaterFact::new(
            (*ln.arg).clone(),
            Number::new("0".to_string()).into(),
            default_line_file(),
        )
        .into();
        if self
            .verify_atomic_fact(&positive, verify_state)?
            .is_unknown()
        {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(
                    "ln: argument must be a positive real".to_string(),
                ),
            )));
        }
        Ok(())
    }

    /// Mathematical contract: `sign(x)` requires a well-defined real `x`.
    pub(in crate::verify) fn verify_sign_well_defined(
        &mut self,
        sign: &Sign,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &sign.arg,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.require_obj_in_r(&sign.arg, verify_state)
    }

    /// Mathematical contract: `factorial(n)` requires a well-defined natural
    /// number `n`.
    pub(in crate::verify) fn verify_factorial_well_defined(
        &mut self,
        factorial: &Factorial,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &factorial.arg,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.require_obj_in_n(&factorial.arg, verify_state)
    }

    /// Mathematical contract: `sin(x)` requires a well-defined real `x`.
    pub(in crate::verify) fn verify_sin_well_defined(
        &mut self,
        sin: &Sin,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &sin.arg,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.require_obj_in_r(&sin.arg, verify_state)
    }

    /// Mathematical contract: `cos(x)` requires a well-defined real `x`.
    pub(in crate::verify) fn verify_cos_well_defined(
        &mut self,
        cos: &Cos,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &cos.arg,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.require_obj_in_r(&cos.arg, verify_state)
    }

    /// Mathematical contract: `tan(x)` requires a well-defined real `x` and
    /// a provably nonzero denominator `cos(x)`.
    pub(in crate::verify) fn verify_tan_well_defined(
        &mut self,
        tan: &Tan,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &tan.arg,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.require_obj_in_r(&tan.arg, verify_state)?;
        let denominator: Obj = Cos::new((*tan.arg).clone()).into();
        let zero: Obj = Number::new("0".to_string()).into();
        let fact: AtomicFact =
            NotEqualFact::new(denominator.clone(), zero, default_line_file()).into();
        let result = self.verify_atomic_fact(&fact, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "tan argument `{}` requires {} != 0",
                    tan.arg, denominator
                )),
            )));
        }
        Ok(())
    }

    /// Mathematical contract: `cot(x)` requires a well-defined real `x` and
    /// a provably nonzero denominator `sin(x)`.
    pub(in crate::verify) fn verify_cot_well_defined(
        &mut self,
        cot: &Cot,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &cot.arg,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.require_obj_in_r(&cot.arg, verify_state)?;
        let denominator: Obj = Sin::new((*cot.arg).clone()).into();
        let zero: Obj = Number::new("0".to_string()).into();
        let fact: AtomicFact =
            NotEqualFact::new(denominator.clone(), zero, default_line_file()).into();
        let result = self.verify_atomic_fact(&fact, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "cot argument `{}` requires {} != 0",
                    cot.arg, denominator
                )),
            )));
        }
        Ok(())
    }

    /// Mathematical contract: `real_part(z)` requires a well-defined complex
    /// argument.
    pub(in crate::verify) fn verify_real_part_well_defined(
        &mut self,
        real_part: &RealPart,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &real_part.arg,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.require_obj_in_c(&real_part.arg, verify_state)?;
        Ok(())
    }

    /// Mathematical contract: `imaginary_part(z)` requires a well-defined
    /// complex argument.
    pub(in crate::verify) fn verify_imaginary_part_well_defined(
        &mut self,
        imaginary_part: &ImaginaryPart,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &imaginary_part.arg,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.require_obj_in_c(&imaginary_part.arg, verify_state)?;
        Ok(())
    }

    /// Mathematical contract: complex modulus requires a well-defined complex
    /// argument.
    pub(in crate::verify) fn verify_complex_abs_well_defined(
        &mut self,
        complex_abs: &ComplexAbs,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &complex_abs.arg,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.require_obj_in_c(&complex_abs.arg, verify_state)?;
        Ok(())
    }

    /// Mathematical contract: real `sqrt(x)` requires a well-defined real
    /// argument with a provable lower bound `0 <= x`.
    pub(in crate::verify) fn verify_sqrt_well_defined(
        &mut self,
        sqrt: &Sqrt,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &sqrt.arg,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.require_obj_in_r(&sqrt.arg, verify_state)?;
        let zero: Obj = Number::new("0".to_string()).into();
        let nonnegative: AtomicFact =
            LessEqualFact::new(zero, (*sqrt.arg).clone(), default_line_file()).into();
        let result = self.verify_atomic_fact(&nonnegative, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "sqrt: argument must be >= 0".to_string(),
                    default_line_file(),
                ),
            )));
        }
        Ok(())
    }

    /// Mathematical contract: `log(base,arg)` requires real operands,
    /// `base > 0`, `base != 1`, and `arg > 0`.
    pub(in crate::verify) fn verify_log_well_defined(
        &mut self,
        log: &Log,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &log.base,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &log.arg,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
        self.require_obj_in_r(&log.base, verify_state)?;
        self.require_obj_in_r(&log.arg, verify_state)?;
        let zero: Obj = Number::new("0".to_string()).into();
        let one: Obj = Number::new("1".to_string()).into();
        let lf = default_line_file();
        let checks: [(&str, AtomicFact); 3] = [
            (
                "log: base must be > 0",
                GreaterFact::new((*log.base).clone(), zero.clone(), lf.clone()).into(),
            ),
            (
                "log: argument must be > 0",
                GreaterFact::new((*log.arg).clone(), zero.clone(), lf.clone()).into(),
            ),
            (
                "log: base must be != 1",
                NotEqualFact::new((*log.base).clone(), one, lf.clone()).into(),
            ),
        ];
        for (msg, atomic) in checks {
            let result = self.verify_atomic_fact(&atomic, verify_state)?;
            if result.is_unknown() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(msg.to_string(), lf.clone()),
                )));
            }
        }
        Ok(())
    }

    /// Mathematical contract: exponentiation is defined on the explicit
    /// complex-natural, nonzero-complex-integer, and real-power domains below.
    // Complex and real pow domain (well-defined check): every complex base has natural powers;
    // a nonzero complex base has integer powers. Existing real-power branches stay available.
    // Example: `i^2` and `z^(-3)` for `z C, z != 0` are defined, while `0^(-1)` is not.
    // Real pow domain: base>=0 and exp in R with exp>0
    // (e.g. x^(1/2) under x>=0); base>0 and exp in R; or base=0, exp in R and exp>0
    // (so 0^(non-positive real non-integers) is out); or exp in Z and base != 0
    // (integer powers for nonzero bases); or base in R and exp in N, including 0^0 = 1.
    // Negative base with non-integer real exp stays out. Uses Z + base!=0 instead of exp mod 2 so
    // rational exponents do not pull Mod(...) into every Or disjunct's well-defined pass.
    /// Mathematical contract implementation: accept exactly the power-domain
    /// alternatives documented immediately above.
    pub(in crate::verify) fn verify_pow_well_defined(
        &mut self,
        pow: &Pow,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &pow.base,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &pow.exponent,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
        let zero_obj: Obj = Number::new("0".to_string()).into();

        let complex_base_and_natural_exponent = AndChainAtomicFact::AndFact(AndFact::new(
            vec![
                InFact::new(
                    (*pow.base).clone(),
                    StandardSet::C.into(),
                    default_line_file(),
                )
                .into(),
                InFact::new(
                    (*pow.exponent).clone(),
                    StandardSet::N.into(),
                    default_line_file(),
                )
                .into(),
            ],
            default_line_file(),
        ));
        if self
            .verify_and_chain_atomic_fact(&complex_base_and_natural_exponent, verify_state)?
            .is_success()
        {
            return Ok(());
        }

        let nonzero_complex_base_and_integer_exponent = AndChainAtomicFact::AndFact(AndFact::new(
            vec![
                InFact::new(
                    (*pow.base).clone(),
                    StandardSet::C.into(),
                    default_line_file(),
                )
                .into(),
                InFact::new(
                    (*pow.exponent).clone(),
                    StandardSet::Z.into(),
                    default_line_file(),
                )
                .into(),
                NotEqualFact::new((*pow.base).clone(), zero_obj.clone(), default_line_file())
                    .into(),
            ],
            default_line_file(),
        ));
        if self
            .verify_and_chain_atomic_fact(&nonzero_complex_base_and_integer_exponent, verify_state)?
            .is_success()
        {
            return Ok(());
        }

        if self.require_obj_in_r(&pow.base, verify_state).is_err() {
            let pow_display = Obj::Pow(pow.clone()).to_string();
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "base and exponent do not satisfy the pow domain: {}",
                    pow_display
                )),
            )));
        }

        let nonnegative_base_and_positive_real_exponent =
            AndChainAtomicFact::AndFact(AndFact::new(
                vec![
                    LessEqualFact::new(zero_obj.clone(), (*pow.base).clone(), default_line_file())
                        .into(),
                    InFact::new(
                        (*pow.exponent).clone(),
                        StandardSet::R.into(),
                        default_line_file(),
                    )
                    .into(),
                    GreaterFact::new(
                        (*pow.exponent).clone(),
                        zero_obj.clone(),
                        default_line_file(),
                    )
                    .into(),
                ],
                default_line_file(),
            ));

        let result = self.verify_and_chain_atomic_fact(
            &nonnegative_base_and_positive_real_exponent,
            verify_state,
        )?;
        if result.is_success() {
            return Ok(());
        }

        let positive_base_and_real_exponent = AndChainAtomicFact::AndFact(AndFact::new(
            vec![
                GreaterFact::new((*pow.base).clone(), zero_obj.clone(), default_line_file()).into(),
                InFact::new(
                    (*pow.exponent).clone(),
                    StandardSet::R.into(),
                    default_line_file(),
                )
                .into(),
            ],
            default_line_file(),
        ));

        let result =
            self.verify_and_chain_atomic_fact(&positive_base_and_real_exponent, verify_state)?;

        if result.is_success() {
            return Ok(());
        }

        let zero_base_and_positive_real_exponent = AndChainAtomicFact::AndFact(AndFact::new(
            vec![
                EqualFact::new((*pow.base).clone(), zero_obj.clone(), default_line_file()).into(),
                InFact::new(
                    (*pow.exponent).clone(),
                    StandardSet::R.into(),
                    default_line_file(),
                )
                .into(),
                GreaterFact::new(
                    (*pow.exponent).clone(),
                    zero_obj.clone(),
                    default_line_file(),
                )
                .into(),
            ],
            default_line_file(),
        ));

        let result =
            self.verify_and_chain_atomic_fact(&zero_base_and_positive_real_exponent, verify_state)?;
        if result.is_success() {
            return Ok(());
        }

        let pow_domain_or_fact = OrFact::new(
            vec![
                nonnegative_base_and_positive_real_exponent,
                positive_base_and_real_exponent,
                zero_base_and_positive_real_exponent,
            ],
            default_line_file(),
        );

        let result = self.verify_or_fact(&pow_domain_or_fact, verify_state)?;
        if result.is_success() {
            return Ok(());
        }

        let pow_display = Obj::Pow(pow.clone()).to_string();
        return Err(RuntimeError::from(WellDefinedRuntimeError(
            RuntimeErrorStruct::new_with_just_msg(format!(
                "base and exponent do not satisfy the pow domain: {}",
                pow_display
            )),
        )));
    }
}
