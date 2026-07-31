use crate::prelude::*;

impl Runtime {
    pub(in crate::verify) fn require_obj_in_c(
        &mut self,
        obj: &Obj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        let c_obj = StandardSet::C.into();
        let in_fact = InFact::new(obj.clone(), c_obj, default_line_file());
        let result = self.verify_atomic_fact(&in_fact.into(), verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!("obj {} is not in C", obj)),
            )));
        }
        Ok(())
    }

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

    /// Require `left <= right` to be verifiable; does not store the fact.
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

    pub(in crate::verify) fn verify_add_well_defined(
        &mut self,
        add: &Add,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&add.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&add.right, verify_state)?;
        self.require_obj_in_c(&add.left, verify_state)?;
        self.require_obj_in_c(&add.right, verify_state)?;
        Ok(())
    }

    pub(in crate::verify) fn verify_sub_well_defined(
        &mut self,
        sub: &Sub,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&sub.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&sub.right, verify_state)?;
        self.require_obj_in_c(&sub.left, verify_state)?;
        self.require_obj_in_c(&sub.right, verify_state)?;
        Ok(())
    }

    pub(in crate::verify) fn verify_mul_well_defined(
        &mut self,
        mul: &Mul,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&mul.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&mul.right, verify_state)?;
        self.require_obj_in_c(&mul.left, verify_state)?;
        self.require_obj_in_c(&mul.right, verify_state)?;
        Ok(())
    }

    pub(in crate::verify) fn verify_div_well_defined(
        &mut self,
        div: &Div,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&div.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&div.right, verify_state)?;

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

    pub(in crate::verify) fn verify_mod_well_defined(
        &mut self,
        m: &Mod,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&m.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&m.right, verify_state)?;
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

    pub(in crate::verify) fn verify_gcd_well_defined(
        &mut self,
        gcd: &Gcd,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&gcd.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&gcd.right, verify_state)?;
        self.require_obj_in_z(&gcd.left, verify_state)?;
        self.require_obj_in_z(&gcd.right, verify_state)?;

        let zero: Obj = Number::new("0".to_string()).into();
        let left_nonzero: AtomicFact =
            NotEqualFact::new((*gcd.left).clone(), zero.clone(), default_line_file()).into();
        let right_nonzero: AtomicFact =
            NotEqualFact::new((*gcd.right).clone(), zero, default_line_file()).into();
        if self
            .verify_atomic_fact(&left_nonzero, verify_state)?
            .is_true()
            || self
                .verify_atomic_fact(&right_nonzero, verify_state)?
                .is_true()
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
        if self.verify_or_fact(&non_all_zero, verify_state)?.is_true() {
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
            .is_true()
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

    pub(in crate::verify) fn verify_abs_well_defined(
        &mut self,
        abs: &Abs,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&abs.arg, verify_state)?;
        self.require_obj_in_r(&abs.arg, verify_state)?;
        Ok(())
    }

    pub(in crate::verify) fn verify_lcm_well_defined(
        &mut self,
        lcm: &Lcm,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&lcm.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&lcm.right, verify_state)?;
        self.require_obj_in_z(&lcm.left, verify_state)?;
        self.require_obj_in_z(&lcm.right, verify_state)
    }

    pub(in crate::verify) fn verify_floor_well_defined(
        &mut self,
        floor: &Floor,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&floor.arg, verify_state)?;
        self.require_obj_in_r(&floor.arg, verify_state)
    }

    pub(in crate::verify) fn verify_ceil_well_defined(
        &mut self,
        ceil: &Ceil,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&ceil.arg, verify_state)?;
        self.require_obj_in_r(&ceil.arg, verify_state)
    }

    pub(in crate::verify) fn verify_min_well_defined(
        &mut self,
        min: &Min,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&min.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&min.right, verify_state)?;
        self.require_obj_in_r(&min.left, verify_state)?;
        self.require_obj_in_r(&min.right, verify_state)
    }

    pub(in crate::verify) fn verify_max_well_defined(
        &mut self,
        max: &Max,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&max.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&max.right, verify_state)?;
        self.require_obj_in_r(&max.left, verify_state)?;
        self.require_obj_in_r(&max.right, verify_state)
    }

    pub(in crate::verify) fn verify_exp_well_defined(
        &mut self,
        exp: &Exp,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&exp.arg, verify_state)?;
        self.require_obj_in_r(&exp.arg, verify_state)
    }

    pub(in crate::verify) fn verify_ln_well_defined(
        &mut self,
        ln: &Ln,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&ln.arg, verify_state)?;
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

    pub(in crate::verify) fn verify_sign_well_defined(
        &mut self,
        sign: &Sign,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&sign.arg, verify_state)?;
        self.require_obj_in_r(&sign.arg, verify_state)
    }

    pub(in crate::verify) fn verify_factorial_well_defined(
        &mut self,
        factorial: &Factorial,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&factorial.arg, verify_state)?;
        self.require_obj_in_n(&factorial.arg, verify_state)
    }

    pub(in crate::verify) fn verify_sin_well_defined(
        &mut self,
        sin: &Sin,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&sin.arg, verify_state)?;
        self.require_obj_in_r(&sin.arg, verify_state)
    }

    pub(in crate::verify) fn verify_cos_well_defined(
        &mut self,
        cos: &Cos,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&cos.arg, verify_state)?;
        self.require_obj_in_r(&cos.arg, verify_state)
    }

    pub(in crate::verify) fn verify_tan_well_defined(
        &mut self,
        tan: &Tan,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&tan.arg, verify_state)?;
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

    pub(in crate::verify) fn verify_cot_well_defined(
        &mut self,
        cot: &Cot,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&cot.arg, verify_state)?;
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

    pub(in crate::verify) fn verify_real_part_well_defined(
        &mut self,
        real_part: &RealPart,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&real_part.arg, verify_state)?;
        self.require_obj_in_c(&real_part.arg, verify_state)?;
        Ok(())
    }

    pub(in crate::verify) fn verify_imaginary_part_well_defined(
        &mut self,
        imaginary_part: &ImaginaryPart,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&imaginary_part.arg, verify_state)?;
        self.require_obj_in_c(&imaginary_part.arg, verify_state)?;
        Ok(())
    }

    pub(in crate::verify) fn verify_complex_abs_well_defined(
        &mut self,
        complex_abs: &ComplexAbs,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&complex_abs.arg, verify_state)?;
        self.require_obj_in_c(&complex_abs.arg, verify_state)?;
        Ok(())
    }

    pub(in crate::verify) fn verify_sqrt_well_defined(
        &mut self,
        sqrt: &Sqrt,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&sqrt.arg, verify_state)?;
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

    pub(in crate::verify) fn verify_log_well_defined(
        &mut self,
        log: &Log,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&log.base, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&log.arg, verify_state)?;
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

    // Complex and real pow domain (well-defined check): every complex base has natural powers;
    // a nonzero complex base has integer powers. Existing real-power branches stay available.
    // Example: `i^2` and `z^(-3)` for `z C, z != 0` are defined, while `0^(-1)` is not.
    // Real pow domain: base>=0 and exp in R with exp>0
    // (e.g. x^(1/2) under x>=0); base>0 and exp in R; or base=0, exp in R and exp>0
    // (so 0^(non-positive real non-integers) is out); or exp in Z and base != 0
    // (integer powers for nonzero bases); or base in R and exp in N, including 0^0 = 1.
    // Negative base with non-integer real exp stays out. Uses Z + base!=0 instead of exp mod 2 so
    // rational exponents do not pull Mod(...) into every Or disjunct's well-defined pass.
    pub(in crate::verify) fn verify_pow_well_defined(
        &mut self,
        pow: &Pow,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&pow.base, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&pow.exponent, verify_state)?;
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
            .is_true()
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
            .is_true()
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
        if result.is_true() {
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

        if result.is_true() {
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
        if result.is_true() {
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
        if result.is_true() {
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
