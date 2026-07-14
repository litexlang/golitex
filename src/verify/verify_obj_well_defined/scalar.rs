use crate::prelude::*;

impl Runtime {
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
        if let Obj::Max(m) = obj {
            self.require_obj_in_r(&m.left, verify_state)?;
            return self.require_obj_in_r(&m.right, verify_state);
        }
        if let Obj::Min(m) = obj {
            self.require_obj_in_r(&m.left, verify_state)?;
            return self.require_obj_in_r(&m.right, verify_state);
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

    /// When both endpoints normalize to numbers, require a verifiable order (concrete intervals).
    /// Skip for purely symbolic bounds (e.g. `closed_range(a, b)` under `forall a, b Z` in axioms).
    pub(in crate::verify) fn range_endpoints_are_numeric_for_interval_order_check(
        &self,
        start: &Obj,
        end: &Obj,
    ) -> bool {
        self.resolve_obj_to_number(start).is_some() && self.resolve_obj_to_number(end).is_some()
    }

    pub(in crate::verify) fn verify_add_well_defined(
        &mut self,
        add: &Add,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&add.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&add.right, verify_state)?;
        self.require_obj_in_r(&add.left, verify_state)?;
        self.require_obj_in_r(&add.right, verify_state)?;
        Ok(())
    }

    pub(in crate::verify) fn verify_sub_well_defined(
        &mut self,
        sub: &Sub,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&sub.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&sub.right, verify_state)?;
        self.require_obj_in_r(&sub.left, verify_state)?;
        self.require_obj_in_r(&sub.right, verify_state)?;
        Ok(())
    }

    pub(in crate::verify) fn verify_mul_well_defined(
        &mut self,
        mul: &Mul,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&mul.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&mul.right, verify_state)?;
        self.require_obj_in_r(&mul.left, verify_state)?;
        self.require_obj_in_r(&mul.right, verify_state)?;
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

        self.require_obj_in_r(&div.left, verify_state)?;
        self.require_obj_in_r(&div.right, verify_state)?;
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

    pub(in crate::verify) fn verify_abs_well_defined(
        &mut self,
        abs: &Abs,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&abs.arg, verify_state)?;
        self.require_obj_in_r(&abs.arg, verify_state)?;
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

    pub(in crate::verify) fn verify_max_well_defined(
        &mut self,
        max: &Max,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&max.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&max.right, verify_state)?;
        self.require_obj_in_r(&max.left, verify_state)?;
        self.require_obj_in_r(&max.right, verify_state)?;
        Ok(())
    }

    pub(in crate::verify) fn verify_min_well_defined(
        &mut self,
        min: &Min,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&min.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&min.right, verify_state)?;
        self.require_obj_in_r(&min.left, verify_state)?;
        self.require_obj_in_r(&min.right, verify_state)?;
        Ok(())
    }

    // Real pow domain (well-defined check): base>=0 and exp in R with exp>0
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

        let nonzero_base_integer_exponent = AndChainAtomicFact::AndFact(AndFact::new(
            vec![
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

        let real_base_and_natural_exponent = AndChainAtomicFact::AndFact(AndFact::new(
            vec![
                InFact::new(
                    (*pow.base).clone(),
                    StandardSet::R.into(),
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

        let pow_domain_or_fact = OrFact::new(
            vec![
                nonnegative_base_and_positive_real_exponent,
                positive_base_and_real_exponent,
                zero_base_and_positive_real_exponent,
                nonzero_base_integer_exponent,
                real_base_and_natural_exponent,
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
