use crate::prelude::*;

impl Runtime {
    fn verify_obj_well_defined_from_cache_if_known(&self, obj: &Obj) -> Option<()> {
        let key = obj.to_string();
        if self.cache_well_defined_obj_contains(&key) {
            Some(())
        } else {
            None
        }
    }

    pub fn verify_obj_well_defined_and_store_cache(
        &mut self,
        obj: &Obj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        if self
            .verify_obj_well_defined_from_cache_if_known(obj)
            .is_some()
        {
            return Ok(());
        }

        match obj {
            Obj::Atom(AtomObj::Identifier(identifier)) => {
                self.verify_identifier_well_defined(identifier)
            }
            Obj::Atom(AtomObj::IdentifierWithMod(x)) => {
                self.verify_identifier_with_mod_well_defined(x)
            }
            Obj::FnObj(fn_obj) => self.verify_fn_obj_well_defined(fn_obj, verify_state),
            Obj::Number(_) => Ok(()),
            Obj::Add(add) => self.verify_add_well_defined(add, verify_state),
            Obj::Sub(sub) => self.verify_sub_well_defined(sub, verify_state),
            Obj::Mul(mul) => self.verify_mul_well_defined(mul, verify_state),
            Obj::Div(div) => self.verify_div_well_defined(div, verify_state),
            Obj::Mod(m) => self.verify_mod_well_defined(m, verify_state),
            Obj::Pow(pow) => self.verify_pow_well_defined(pow, verify_state),
            Obj::Abs(abs) => self.verify_abs_well_defined(abs, verify_state),
            Obj::Log(log) => self.verify_log_well_defined(log, verify_state),
            Obj::Max(max) => self.verify_max_well_defined(max, verify_state),
            Obj::Min(min) => self.verify_min_well_defined(min, verify_state),
            Obj::Union(x) => self.verify_union_well_defined(x, verify_state),
            Obj::Intersect(x) => self.verify_intersect_well_defined(x, verify_state),
            Obj::SetMinus(x) => self.verify_set_minus_well_defined(x, verify_state),
            Obj::SetDiff(x) => self.verify_set_diff_well_defined(x, verify_state),
            Obj::Cup(x) => self.verify_cup_well_defined(x, verify_state),
            Obj::Cap(x) => self.verify_cap_well_defined(x, verify_state),
            Obj::ListSet(x) => self.verify_list_set_well_defined(x, verify_state),
            Obj::SetBuilder(x) => {
                self.run_in_local_env(|rt| rt.verify_set_builder_well_defined(x, verify_state))
            }
            Obj::FnSet(x) => {
                self.run_in_local_env(|rt| rt.verify_fn_set_well_defined(x, verify_state))
            }
            Obj::AnonymousFn(x) => self.verify_anonymous_fn_well_defined(x, verify_state),
            Obj::StandardSet(StandardSet::NPos) => self.verify_n_pos_obj_well_defined(),
            Obj::StandardSet(StandardSet::N) => self.verify_n_obj_well_defined(),
            Obj::StandardSet(StandardSet::Q) => self.verify_q_obj_well_defined(),
            Obj::StandardSet(StandardSet::Z) => self.verify_z_obj_well_defined(),
            Obj::StandardSet(StandardSet::R) => self.verify_r_obj_well_defined(),
            Obj::Cart(x) => self.verify_cart_well_defined(x, verify_state),
            Obj::CartDim(x) => self.verify_cart_dim_well_defined(x, verify_state),
            Obj::Proj(x) => self.verify_proj_well_defined(x, verify_state),
            Obj::TupleDim(x) => self.verify_dim_well_defined(x, verify_state),
            Obj::Tuple(x) => self.verify_tuple_well_defined(x, verify_state),
            Obj::Count(x) => self.verify_count_well_defined(x, verify_state),
            Obj::Sum(x) => self.verify_sum_obj_well_defined(x, verify_state),
            Obj::Product(x) => self.verify_product_obj_well_defined(x, verify_state),
            Obj::Range(x) => self.verify_range_well_defined(x, verify_state),
            Obj::ClosedRange(x) => self.verify_closed_range_well_defined(x, verify_state),
            Obj::FiniteSeqSet(x) => self.verify_finite_seq_set_well_defined(x, verify_state),
            Obj::SeqSet(x) => self.verify_seq_set_well_defined(x, verify_state),
            Obj::FiniteSeqListObj(x) => {
                self.verify_finite_seq_list_obj_well_defined(x, verify_state)
            }
            Obj::MatrixSet(x) => self.verify_matrix_set_well_defined(x, verify_state),
            Obj::MatrixListObj(x) => self.verify_matrix_list_obj_well_defined(x, verify_state),
            Obj::MatrixAdd(x) => self.verify_matrix_add_well_defined(x, verify_state),
            Obj::MatrixSub(x) => self.verify_matrix_sub_well_defined(x, verify_state),
            Obj::MatrixMul(x) => self.verify_matrix_mul_well_defined(x, verify_state),
            Obj::MatrixScalarMul(x) => self.verify_matrix_scalar_mul_well_defined(x, verify_state),
            Obj::MatrixPow(x) => self.verify_matrix_pow_well_defined(x, verify_state),
            Obj::PowerSet(x) => self.verify_power_set_well_defined(x, verify_state),
            Obj::Choose(x) => self.verify_choose_well_defined(x, verify_state),
            Obj::ObjAtIndex(x) => self.verify_obj_at_index_well_defined(x, verify_state),
            Obj::StandardSet(StandardSet::QPos) => self.verify_q_pos_well_defined(),
            Obj::StandardSet(StandardSet::RPos) => self.verify_r_pos_well_defined(),
            Obj::StandardSet(StandardSet::QNeg) => self.verify_q_neg_well_defined(),
            Obj::StandardSet(StandardSet::ZNeg) => self.verify_z_neg_well_defined(),
            Obj::StandardSet(StandardSet::RNeg) => self.verify_r_neg_well_defined(),
            Obj::StandardSet(StandardSet::QNz) => self.verify_q_nz_well_defined(),
            Obj::StandardSet(StandardSet::ZNz) => self.verify_z_nz_well_defined(),
            Obj::StandardSet(StandardSet::RNz) => self.verify_r_nz_well_defined(),
            Obj::FamilyObj(family) => {
                self.verify_param_type_family_well_defined(family, verify_state)
            }
            Obj::Atom(AtomObj::Forall(_)) => Ok(()),
            Obj::Atom(AtomObj::Def(_)) => Ok(()),
            Obj::Atom(AtomObj::Exist(_)) => Ok(()),
            Obj::Atom(AtomObj::SetBuilder(_)) => Ok(()),
            Obj::Atom(AtomObj::FnSet(_)) => Ok(()),
            Obj::Atom(AtomObj::Induc(_)) => Ok(()),
            Obj::Atom(AtomObj::DefAlgo(_)) => Ok(()),
        }?;

        self.store_well_defined_obj_cache(obj);

        Ok(())
    }

    fn verify_identifier_well_defined(&self, identifier: &Identifier) -> Result<(), RuntimeError> {
        if self.is_name_used_for_identifier_and_field_access(&identifier.name) {
            Ok(())
        } else {
            Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "identifier `{}` not defined",
                    identifier.to_string()
                )),
            )))
        }
    }

    fn verify_identifier_with_mod_well_defined(
        &self,
        x: &IdentifierWithMod,
    ) -> Result<(), RuntimeError> {
        let _ = x;
        unreachable!()
    }

    fn verify_fn_obj_well_defined(
        &mut self,
        fn_obj: &FnObj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        let mut space = match fn_obj.head.as_ref() {
            FnObjHead::AnonymousFnLiteral(a) => {
                self.verify_anonymous_fn_well_defined(a.as_ref(), verify_state)
                    .map_err(|well_defined_error| {
                        RuntimeError::from(WellDefinedRuntimeError(RuntimeErrorStruct::new_with_msg_and_cause(format!(
                                "object {} is not well-defined: anonymous function head is not well-defined",
                                fn_obj.to_string()
                            ), well_defined_error)))
                    })?;
                FnSetSpace::Anon((**a).clone())
            }
            _ => {
                let function_name_obj: Obj = (*fn_obj.head).clone().into();
                let body = self
                    .get_object_in_fn_set_or_restrict(&function_name_obj)
                    .ok_or_else(|| {
                        RuntimeError::from(WellDefinedRuntimeError(
                            RuntimeErrorStruct::new_with_just_msg(todo_error_message(format!(
                                "`{}` is not a defined function",
                                fn_obj.head.to_string()
                            ))),
                        ))
                    })?
                    .clone();
                FnSetSpace::Set(FnSet::from_body(body))
            }
        };

        for (i, args) in fn_obj.body.iter().enumerate() {
            self.verify_fn_obj_well_defined_against_fn_like_space(
                args,
                space.params(),
                space.dom(),
                space.binding(),
                verify_state,
            )
            .map_err(|well_defined_error| {
                RuntimeError::from(WellDefinedRuntimeError(RuntimeErrorStruct::new_with_msg_and_cause(format!(
                        "object {} is not well-defined, failed to verify arguments satisfy function domain.",
                        fn_obj.to_string()
                    ), well_defined_error)))
            })?;

            let set_where_the_next_fn_obj_is_in = space.ret_set_obj();

            let fn_obj_prefix_body: Vec<Vec<Box<Obj>>> =
                fn_obj.body[..=i].iter().cloned().collect();
            let fn_obj_prefix_as_obj: Obj =
                FnObj::new(*fn_obj.head.clone(), fn_obj_prefix_body).into();
            let intermediate_in_fact = InFact::new(
                fn_obj_prefix_as_obj,
                set_where_the_next_fn_obj_is_in,
                default_line_file(),
            );
            let intermediate_atomic_fact = AtomicFact::InFact(intermediate_in_fact);
            self.store_atomic_fact_without_well_defined_verified_and_infer(
                intermediate_atomic_fact,
            )
            .map_err(|store_fact_error| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!(
                        "failed to store intermediate fn-obj membership fact while verifying `{}`",
                        fn_obj.to_string()
                    ),
                        store_fact_error,
                    ),
                ))
            })?;

            if i == fn_obj.body.len() - 1 {
                break;
            }

            space = FnSetSpace::from_ret_obj(space.ret_set_obj())?;
        }

        Ok(())
    }

    fn verify_fn_obj_well_defined_against_fn_like_space(
        &mut self,
        args: &Vec<Box<Obj>>,
        params_def_with_set: &Vec<ParamGroupWithSet>,
        dom_facts: &Vec<OrAndChainAtomicFact>,
        param_binding: ParamObjType,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        let param_count = ParamGroupWithSet::number_of_params(params_def_with_set);
        if args.len() != param_count {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "number of args ({}) does not match fn set with dom param count ({})",
                    args.len(),
                    param_count
                )),
            )));
        }

        for arg in args.iter() {
            self.verify_obj_well_defined_and_store_cache(arg, verify_state)?;
        }

        let mut args_as_obj: Vec<Obj> = Vec::with_capacity(args.len());
        for arg in args.iter() {
            args_as_obj.push((**arg).clone());
        }

        let args_satisfy_fn_set_params_set_facts =
            ParamGroupWithSet::facts_for_args_satisfy_param_def_with_set_vec(
                self,
                params_def_with_set,
                &args_as_obj,
                param_binding,
            )
            .map_err(|stmt_error| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!("failed to build facts for args satisfy fn set parameter sets"),
                        stmt_error,
                    ),
                ))
            })?;

        for fact in args_satisfy_fn_set_params_set_facts.iter() {
            let verify_result =
                self.verify_atomic_fact(fact, verify_state)
                    .map_err(|verify_error| {
                        RuntimeError::from(WellDefinedRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_cause(
                                format!(
                                    "failed to verify arg satisfy fn set parameter set: {}",
                                    fact
                                ),
                                verify_error,
                            ),
                        ))
                    })?;
            if verify_result.is_unknown() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "arg does not satisfy fn set parameter set, the fact is unknown: {}",
                        fact
                    )),
                )));
            }
        }

        let param_to_arg_map = ParamGroupWithSet::param_defs_and_args_to_param_to_arg_map(
            params_def_with_set,
            &args_as_obj,
        );
        for dom_fact in dom_facts.iter() {
            let instantiated_dom_fact = self
                .inst_or_and_chain_atomic_fact(dom_fact, &param_to_arg_map, param_binding, None)
                .map_err(|e| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!("failed to instantiate function domain fact: {}", e),
                            e,
                        ),
                    ))
                })?;
            let verify_result = self
                .verify_or_and_chain_atomic_fact(&instantiated_dom_fact, verify_state)
                .map_err(|verify_error| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!(
                                "failed to verify function domain fact:\n{}",
                                instantiated_dom_fact
                            ),
                            verify_error,
                        ),
                    ))
                })?;
            if verify_result.is_unknown() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "failed to verify function domain fact:\n{}",
                        instantiated_dom_fact
                    )),
                )));
            }
        }

        Ok(())
    }

    fn require_obj_in_r(
        &mut self,
        obj: &Obj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        if let Obj::Abs(a) = obj {
            return self.require_obj_in_r(&a.arg, verify_state);
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

    fn require_obj_in_z(
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
    fn require_less_equal_verified(
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
    fn range_endpoints_are_numeric_for_interval_order_check(&self, start: &Obj, end: &Obj) -> bool {
        self.resolve_obj_to_number(start).is_some() && self.resolve_obj_to_number(end).is_some()
    }

    fn verify_add_well_defined(
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

    fn verify_sub_well_defined(
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

    fn verify_mul_well_defined(
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

    fn verify_div_well_defined(
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

    fn verify_mod_well_defined(
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

    fn verify_abs_well_defined(
        &mut self,
        abs: &Abs,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&abs.arg, verify_state)?;
        self.require_obj_in_r(&abs.arg, verify_state)?;
        Ok(())
    }

    fn verify_log_well_defined(
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

    fn verify_max_well_defined(
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

    fn verify_min_well_defined(
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

    // Real pow domain (well-defined check): base>0 and exp in R; or base=0, exp in R and exp>0
    // (so 0^0 and 0^(non-positive) are out); or exp in Z and base != 0 (integer powers, x^0=1);
    // or exp in N_pos (positive integer), any base (e.g. 0^3, (h+i)^2 without proving base != 0).
    // Negative base with non-integer real exp stays out. Uses Z + base!=0 instead of exp mod 2 so
    // rational exponents do not pull Mod(...) into every Or disjunct's well-defined pass.
    fn verify_pow_well_defined(
        &mut self,
        pow: &Pow,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&pow.base, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&pow.exponent, verify_state)?;

        let zero_obj: Obj = Number::new("0".to_string()).into();

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

        let exponent_in_n_pos = AndChainAtomicFact::AtomicFact(
            InFact::new(
                (*pow.exponent).clone(),
                StandardSet::NPos.into(),
                default_line_file(),
            )
            .into(),
        );

        let pow_domain_or_fact = OrFact::new(
            vec![
                positive_base_and_real_exponent,
                zero_base_and_positive_real_exponent,
                nonzero_base_integer_exponent,
                exponent_in_n_pos,
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

    fn verify_union_well_defined(
        &mut self,
        x: &Union,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.right, verify_state)?;
        Ok(())
    }

    fn verify_intersect_well_defined(
        &mut self,
        x: &Intersect,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.right, verify_state)?;
        Ok(())
    }

    fn verify_set_minus_well_defined(
        &mut self,
        x: &SetMinus,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.right, verify_state)?;
        Ok(())
    }

    fn verify_set_diff_well_defined(
        &mut self,
        x: &SetDiff,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.right, verify_state)?;
        Ok(())
    }

    fn verify_cup_well_defined(
        &mut self,
        x: &Cup,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.left, verify_state)?;
        Ok(())
    }

    fn verify_cap_well_defined(
        &mut self,
        x: &Cap,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.left, verify_state)?;
        Ok(())
    }

    fn verify_list_set_well_defined(
        &mut self,
        x: &ListSet,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        for obj in &x.list {
            self.verify_obj_well_defined_and_store_cache(obj, verify_state)?;
        }

        let next_verify_state = verify_state.make_state_with_req_ok_set_to_true();
        let len = x.list.len();
        let mut i = 0;
        while i < len {
            let left_obj = match x.list.get(i) {
                Some(left_obj) => (**left_obj).clone(),
                None => break,
            };
            let mut j = i + 1;
            while j < len {
                let right_obj = match x.list.get(j) {
                    Some(right_obj) => (**right_obj).clone(),
                    None => break,
                };
                let not_equal_atomic_fact =
                    NotEqualFact::new(left_obj.clone(), right_obj, default_line_file()).into();
                let verify_result = self
                    .verify_atomic_fact(&not_equal_atomic_fact, &next_verify_state)
                    .map_err(|previous_error| {
                        RuntimeError::from(WellDefinedRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_cause(
                                format!(
                                    "failed to verify list set elements are pairwise not equal: {}",
                                    not_equal_atomic_fact
                                ),
                                previous_error,
                            ),
                        ))
                    })?;
                if verify_result.is_unknown() {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(RuntimeErrorStruct::new_with_just_msg(format!("list set elements must be pairwise not equal, but it is not provable: {}", not_equal_atomic_fact)))));
                }
                j += 1;
            }
            i += 1;
        }

        Ok(())
    }

    fn verify_set_builder_well_defined(
        &mut self,
        x: &SetBuilder,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        // Must use `ParamObjType::SetBuilder` here, not `define_params_with_set` (FnSet).
        // Parsed set-builder facts use SetBuilder-tagged bound vars; a mismatched tag means
        // e.g. `x $in N` is never found when checking `b ^ x`, so pow domain fails.
        // Run in local env so param binding and body facts do not leak into the outer scope.
        self.run_in_local_env(|rt| {
            if let Err(well_defined_error) = rt
                .verify_obj_well_defined_and_store_cache(&x.param_set, &VerifyState::new(0, false))
            {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!(
                            "failed to verify well-defined of set builder {}",
                            x.to_string()
                        ),
                        well_defined_error,
                    ),
                )));
            }
            if let Err(e) =
                rt.store_free_param_or_identifier_name(&x.param, ParamObjType::SetBuilder)
            {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!(
                            "failed to verify well-defined of set builder {}",
                            x.to_string()
                        ),
                        e,
                    ),
                )));
            }
            let param_in_set: Fact = InFact::new(
                obj_for_bound_param_in_scope(x.param.clone(), ParamObjType::SetBuilder),
                (*x.param_set).clone(),
                default_line_file(),
            )
            .into();
            if let Err(e) =
                rt.verify_well_defined_and_store_and_infer_with_default_verify_state(param_in_set)
            {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!(
                            "failed to verify well-defined of set builder {}",
                            x.to_string()
                        ),
                        e,
                    ),
                )));
            }

            for fact in x.facts.iter() {
                if let Err(e) = rt.verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                    fact,
                    verify_state,
                ) {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!(
                                "failed to verify well-defined of set builder {}",
                                x.to_string()
                            ),
                            e,
                        ),
                    )));
                }
            }

            Ok(())
        })
    }

    fn verify_fn_set_well_defined(
        &mut self,
        x: &FnSet,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        for param_def_with_set in x.body.params_def_with_set.iter() {
            if let Err(e) = self.define_params_with_set(param_def_with_set) {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!(
                            "failed to verify well-defined of fn set with dom {}",
                            x.to_string()
                        ),
                        e,
                    ),
                )));
            }
        }

        for fact in x.body.dom_facts.iter() {
            if let Err(e) = self.verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                fact,
                verify_state,
            ) {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!(
                            "failed to verify well-defined of fn set with dom {}",
                            x.to_string()
                        ),
                        e,
                    ),
                )));
            }
        }

        if let Err(e) = self.verify_obj_well_defined_and_store_cache(&x.body.ret_set, verify_state)
        {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_cause(
                    format!(
                        "failed to verify well-defined of fn set with dom {}",
                        x.to_string()
                    ),
                    e,
                ),
            )));
        }

        Ok(())
    }

    fn verify_anonymous_fn_well_defined(
        &mut self,
        x: &AnonymousFn,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.run_in_local_env(|rt| {
            for param_def_with_set in x.body.params_def_with_set.iter() {
                if let Err(e) =
                    rt.define_params_with_set_in_scope(param_def_with_set, ParamObjType::FnSet)
                {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!(
                                "failed to verify well-defined of anonymous fn {}",
                                x.to_string()
                            ),
                            e,
                        ),
                    )));
                }
            }

            for fact in x.body.dom_facts.iter() {
                if let Err(e) = rt.verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                    fact,
                    verify_state,
                ) {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!(
                                "failed to verify well-defined of anonymous fn {}",
                                x.to_string()
                            ),
                            e,
                        ),
                    )));
                }
            }

            if let Err(e) =
                rt.verify_obj_well_defined_and_store_cache(&x.body.ret_set, verify_state)
            {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!(
                            "failed to verify well-defined of anonymous fn {}",
                            x.to_string()
                        ),
                        e,
                    ),
                )));
            }

            if let Err(e) = rt.verify_obj_well_defined_and_store_cache(&x.equal_to, verify_state) {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!(
                            "failed to verify well-defined of anonymous fn {}",
                            x.to_string()
                        ),
                        e,
                    ),
                )));
            }

            Ok(())
        })
    }

    fn verify_n_pos_obj_well_defined(&mut self) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn verify_n_obj_well_defined(&mut self) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn verify_q_obj_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn verify_z_obj_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn verify_r_obj_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn verify_cart_well_defined(
        &mut self,
        x: &Cart,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        for obj in &x.args {
            self.verify_obj_well_defined_and_store_cache(obj, verify_state)?;
        }
        Ok(())
    }

    fn verify_cart_dim_well_defined(
        &mut self,
        x: &CartDim,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.set, verify_state)?;

        let is_cart_fact = IsCartFact::new((*x.set).clone(), default_line_file()).into();
        let result = self.verify_atomic_fact(&is_cart_fact, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "set {} is not a cart",
                    x.set.to_string()
                )),
            )));
        }

        Ok(())
    }

    fn verify_proj_well_defined(
        &mut self,
        x: &Proj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.set, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.dim, verify_state)?;

        let projection_dimension_number = self.resolve_obj_to_number(&x.dim).ok_or_else(|| {
            RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "projection dimension {} is not a number",
                    x.dim
                )),
            ))
        })?;
        let projection_dimension_obj: Obj =
            Number::new(projection_dimension_number.normalized_value).into();

        let projection_dimension_is_positive_integer_fact = InFact::new(
            projection_dimension_obj.clone(),
            StandardSet::NPos.into(),
            default_line_file(),
        )
        .into();
        let projection_dimension_is_positive_integer_result =
            self.verify_atomic_fact(&projection_dimension_is_positive_integer_fact, verify_state)?;
        if projection_dimension_is_positive_integer_result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "projection dimension {} is not a positive integer",
                    projection_dimension_obj
                )),
            )));
        }

        let left_set_is_cart_fact = IsCartFact::new((*x.set).clone(), default_line_file()).into();
        let left_set_is_cart_result =
            self.verify_atomic_fact(&left_set_is_cart_fact, verify_state)?;
        if left_set_is_cart_result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "projection left side {} is not a cart",
                    x.set
                )),
            )));
        }

        let left_set_cart_dim_obj: Obj = CartDim::new((*x.set).clone()).into();

        let proj_index_not_larger_than_cart_dim = LessEqualFact::new(
            projection_dimension_obj.clone(),
            left_set_cart_dim_obj.clone(),
            default_line_file(),
        )
        .into();
        let left_set_cart_dim_less_equal_projection_dimension_result =
            self.verify_atomic_fact(&proj_index_not_larger_than_cart_dim, verify_state)?;
        if left_set_cart_dim_less_equal_projection_dimension_result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{} <= {} is unknown",
                    projection_dimension_obj, left_set_cart_dim_obj
                )),
            )));
        }

        Ok(())
    }

    fn verify_dim_well_defined(
        &mut self,
        x: &TupleDim,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.arg, verify_state)?;

        let is_tuple_fact = IsTupleFact::new((*x.arg).clone(), default_line_file()).into();
        let result = self.verify_atomic_fact(&is_tuple_fact, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "`{}` is unknown, `dim` object requires its argument to be a tuple",
                    is_tuple_fact
                )),
            )));
        }

        Ok(())
    }

    fn verify_tuple_well_defined(
        &mut self,
        x: &Tuple,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        for obj in &x.args {
            self.verify_obj_well_defined_and_store_cache(obj, verify_state)?;
        }
        Ok(())
    }

    fn verify_count_well_defined(
        &mut self,
        x: &Count,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        // 必须 is_finite_set
        let is_finite_set_fact = IsFiniteSetFact::new((*x.set).clone(), default_line_file()).into();
        let result = self.verify_atomic_fact(&is_finite_set_fact, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "set {} is not a finite set",
                    x.set.to_string()
                )),
            )));
        }
        Ok(())
    }

    fn verify_sum_obj_well_defined(
        &mut self,
        x: &Sum,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.start, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.end, verify_state)?;
        self.require_obj_in_z(&x.start, verify_state)?;
        self.require_obj_in_z(&x.end, verify_state)?;
        if self.range_endpoints_are_numeric_for_interval_order_check(&x.start, &x.end) {
            self.require_less_equal_verified(
                &x.start,
                &x.end,
                verify_state,
                "sum: cannot verify start <= end for the summation range".to_string(),
            )?;
        }
        self.verify_obj_well_defined_and_store_cache(&x.func, verify_state)?;
        self.verify_iterated_op_summand_under_integer_index_interval(
            &x.func,
            x.start.as_ref(),
            x.end.as_ref(),
            verify_state,
            "sum",
        )
    }

    fn verify_product_obj_well_defined(
        &mut self,
        x: &Product,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.start, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.end, verify_state)?;
        self.require_obj_in_z(&x.start, verify_state)?;
        self.require_obj_in_z(&x.end, verify_state)?;
        if self.range_endpoints_are_numeric_for_interval_order_check(&x.start, &x.end) {
            self.require_less_equal_verified(
                &x.start,
                &x.end,
                verify_state,
                "product: cannot verify start <= end for the product range".to_string(),
            )?;
        }
        self.verify_obj_well_defined_and_store_cache(&x.func, verify_state)?;
        self.verify_iterated_op_summand_under_integer_index_interval(
            &x.func,
            x.start.as_ref(),
            x.end.as_ref(),
            verify_state,
            "product",
        )
    }

    /// Resolve the set `S` in `pname S` for the unary param from `params_def_with_set`.
    fn unary_param_set_from_params_def(
        params_def: &[ParamGroupWithSet],
        pname: &str,
    ) -> Option<Obj> {
        for g in params_def {
            if g.params.iter().any(|n| n == pname) {
                return Some(g.set.clone());
            }
        }
        None
    }

    /// For a closed range `[a,b]` with explicit integer endpoints, require each integer in the range
    /// to be in the index parameter's declared set (e.g. `Z_neg` disallows 1,2,3 in `1..3`).
    fn verify_closed_range_each_integer_satisfies_unary_param_set(
        &mut self,
        start: &Obj,
        end: &Obj,
        param_set: &Obj,
        verify_state: &VerifyState,
        op: &str,
    ) -> Result<(), RuntimeError> {
        let Some(a_num) = self.resolve_obj_to_number(start) else {
            return Ok(());
        };
        let Some(b_num) = self.resolve_obj_to_number(end) else {
            return Ok(());
        };
        let as_ = a_num.normalized_value.trim();
        let bs = b_num.normalized_value.trim();
        if !is_number_string_literally_integer_without_dot(as_.to_string())
            || !is_number_string_literally_integer_without_dot(bs.to_string())
        {
            return Ok(());
        }
        let Some(ai) = as_.parse::<i128>().ok() else {
            return Ok(());
        };
        let Some(bi) = bs.parse::<i128>().ok() else {
            return Ok(());
        };
        if ai > bi {
            return Ok(());
        }
        for k in ai..=bi {
            let k_obj: Obj = Number::new(k.to_string()).into();
            let in_fact = InFact::new(k_obj, param_set.clone(), default_line_file());
            let atomic_fact = AtomicFact::InFact(in_fact);
            let result = self.verify_atomic_fact(&atomic_fact, verify_state)?;
            if result.is_unknown() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                            "{op}: each integer in the closed range from {} to {} must belong to the index parameter's type; not satisfied at index {}",
                            start, end, k
                        )),
                )));
            }
        }
        Ok(())
    }

    fn verify_iterated_op_summand_with_stored_fn_set_body(
        &mut self,
        fs_body: FnSetBody,
        start: &Obj,
        end: &Obj,
        verify_state: &VerifyState,
        op: &str,
    ) -> Result<(), RuntimeError> {
        if ParamGroupWithSet::number_of_params(&fs_body.params_def_with_set) != 1 {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{op}: the function in the function set must be unary (one index)"
                )),
            )));
        }
        let param_names = ParamGroupWithSet::collect_param_names(&fs_body.params_def_with_set);
        let pname = param_names[0].clone();
        let Some(param_set_for_index) =
            Self::unary_param_set_from_params_def(&fs_body.params_def_with_set, &pname)
        else {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{op}: could not find index parameter in params_def_with_set"
                )),
            )));
        };
        self.verify_closed_range_each_integer_satisfies_unary_param_set(
            start,
            end,
            &param_set_for_index,
            verify_state,
            op,
        )?;
        let start_c = start.clone();
        let end_c = end.clone();
        self.run_in_local_env(|rt| {
            for g in fs_body.params_def_with_set.iter() {
                rt.define_params_with_set_in_scope(g, ParamObjType::FnSet)
                    .map_err(|e| {
                        RuntimeError::from(WellDefinedRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_cause(
                                format!(
                                    "{op}: could not bind index parameter in local well-defined check"
                                ),
                                e,
                            ),
                        ))
                    })?;
            }
            let k: Obj = Identifier::new(pname).into();
            let le_lo = OrAndChainAtomicFact::AtomicFact(
                LessEqualFact::new(start_c.clone(), k.clone(), default_line_file()).into(),
            );
            let le_hi = OrAndChainAtomicFact::AtomicFact(
                LessEqualFact::new(k, end_c.clone(), default_line_file()).into(),
            );
            rt.store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(le_lo)
                .map_err(|e| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!("{op}: could not add lower bound in local check"),
                            e,
                        ),
                    ))
                })?;
            rt.store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(le_hi)
                .map_err(|e| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!("{op}: could not add upper bound in local check"),
                            e,
                        ),
                    ))
                })?;
            for df in fs_body.dom_facts.iter() {
                rt.verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                    df,
                    verify_state,
                )
                .map_err(|e| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!("{op}: function set dom in local check failed"),
                            e,
                        ),
                    ))
                })?;
            }
            rt.verify_obj_well_defined_and_store_cache(&fs_body.ret_set, verify_state)
                .map_err(|e| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!("{op}: return set not well-defined on the integer range"),
                            e,
                        ),
                    ))
                })
        })
    }

    fn verify_iterated_op_summand_under_integer_index_interval(
        &mut self,
        func: &Obj,
        start: &Obj,
        end: &Obj,
        verify_state: &VerifyState,
        op: &str,
    ) -> Result<(), RuntimeError> {
        if let Some(af) = Self::summand_as_unary_anonymous_fn(func) {
            return self.verify_unary_iterated_anonymous_in_interval(
                af,
                start,
                end,
                verify_state,
                op,
            );
        }
        if let Obj::FnObj(fo) = func {
            if !fo.body.is_empty() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "{op}: expected a bare function as summand, not a function application"
                    )),
                )));
            }
            let function_name_obj: Obj = (*fo.head).clone().into();
            let Some(fs_body) = self
                .get_object_in_fn_set_or_restrict(&function_name_obj)
                .cloned()
            else {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "{op}: summand must be a unary anonymous function, or a name with a stored function set; got {}",
                        func
                    )),
                )));
            };
            return self.verify_iterated_op_summand_with_stored_fn_set_body(
                fs_body,
                start,
                end,
                verify_state,
                op,
            );
        }
        if let Some(fs_body) = self.get_cloned_object_in_fn_set_or_restrict(func) {
            return self.verify_iterated_op_summand_with_stored_fn_set_body(
                fs_body,
                start,
                end,
                verify_state,
                op,
            );
        }
        Err(RuntimeError::from(WellDefinedRuntimeError(
            RuntimeErrorStruct::new_with_just_msg(format!(
                "{op}: summand must be a unary anonymous function, or a defined unary function in a function set; got {}",
                func
            )),
        )))
    }

    fn summand_as_unary_anonymous_fn(obj: &Obj) -> Option<&AnonymousFn> {
        match obj {
            Obj::AnonymousFn(af) => Some(af),
            Obj::FnObj(fo) => {
                if !fo.body.is_empty() {
                    return None;
                }
                match fo.head.as_ref() {
                    FnObjHead::AnonymousFnLiteral(a) => Some(a.as_ref()),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn verify_unary_iterated_anonymous_in_interval(
        &mut self,
        af: &AnonymousFn,
        start: &Obj,
        end: &Obj,
        verify_state: &VerifyState,
        op: &str,
    ) -> Result<(), RuntimeError> {
        if ParamGroupWithSet::number_of_params(&af.body.params_def_with_set) != 1 {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{op}: summation/product index function must be unary (one parameter)"
                )),
            )));
        }
        let param_names = ParamGroupWithSet::collect_param_names(&af.body.params_def_with_set);
        let pname = param_names[0].clone();
        let Some(param_set_for_index) =
            Self::unary_param_set_from_params_def(&af.body.params_def_with_set, &pname)
        else {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{op}: could not find index parameter in params_def_with_set"
                )),
            )));
        };
        self.verify_closed_range_each_integer_satisfies_unary_param_set(
            start,
            end,
            &param_set_for_index,
            verify_state,
            op,
        )?;
        self.run_in_local_env(|rt| {
            for g in af.body.params_def_with_set.iter() {
                rt.define_params_with_set_in_scope(g, ParamObjType::FnSet)
                    .map_err(|e| {
                        RuntimeError::from(WellDefinedRuntimeError(RuntimeErrorStruct::new_with_msg_and_cause(format!("{op}: could not bind index parameter in local well-defined check"), e)))
                    })?;
            }
            let k: Obj = Identifier::new(pname).into();
            let le_lo = OrAndChainAtomicFact::AtomicFact(
                LessEqualFact::new(start.clone(), k.clone(), default_line_file()).into(),
            );
            let le_hi = OrAndChainAtomicFact::AtomicFact(
                LessEqualFact::new(k, end.clone(), default_line_file()).into(),
            );
            rt.store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(le_lo)
                .map_err(|e| {
                    RuntimeError::from(WellDefinedRuntimeError(RuntimeErrorStruct::new_with_msg_and_cause(format!("{op}: could not add lower bound in local check"), e)))
                })?;
            rt.store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(le_hi)
                .map_err(|e| {
                    RuntimeError::from(WellDefinedRuntimeError(RuntimeErrorStruct::new_with_msg_and_cause(format!("{op}: could not add upper bound in local check"), e)))
                })?;
            for df in af.body.dom_facts.iter() {
                rt.verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                    df,
                    verify_state,
                )
                .map_err(|e| {
                    RuntimeError::from(WellDefinedRuntimeError(RuntimeErrorStruct::new_with_msg_and_cause(format!("{op}: local dom of anonymous summand in integer range check failed"), e)))
                })?;
            }
            rt.verify_obj_well_defined_and_store_cache(&af.body.ret_set, verify_state)
                .map_err(|e| {
                    RuntimeError::from(WellDefinedRuntimeError(RuntimeErrorStruct::new_with_msg_and_cause(format!("{op}: return set not well-defined on the integer range"), e)))
                })?;
            rt.verify_obj_well_defined_and_store_cache(&af.equal_to, verify_state)
                .map_err(|e| {
                    RuntimeError::from(WellDefinedRuntimeError(RuntimeErrorStruct::new_with_msg_and_cause(format!("{op}: expression body not well-defined on the integer range"), e)))
                })
        })
    }

    fn verify_range_well_defined(
        &mut self,
        x: &Range,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.start, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.end, verify_state)?;
        self.require_obj_in_z(&x.start, verify_state)?;
        self.require_obj_in_z(&x.end, verify_state)?;
        if self.range_endpoints_are_numeric_for_interval_order_check(&x.start, &x.end) {
            self.require_less_equal_verified(
                &x.start,
                &x.end,
                verify_state,
                format!(
                    "range: cannot verify {} <= {} (numeric half-open interval needs lower <= upper)",
                    x.start, x.end
                ),
            )?;
        }
        Ok(())
    }

    fn verify_closed_range_well_defined(
        &mut self,
        x: &ClosedRange,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.start, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.end, verify_state)?;
        self.require_obj_in_z(&x.start, verify_state)?;
        self.require_obj_in_z(&x.end, verify_state)?;
        if self.range_endpoints_are_numeric_for_interval_order_check(&x.start, &x.end) {
            self.require_less_equal_verified(
                &x.start,
                &x.end,
                verify_state,
                format!(
                    "closed_range: cannot verify {} <= {} (numeric closed interval needs lower <= upper)",
                    x.start, x.end
                ),
            )?;
        }
        Ok(())
    }

    fn verify_finite_seq_set_well_defined(
        &mut self,
        x: &FiniteSeqSet,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.set, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.n, verify_state)?;
        let is_set_fact = IsSetFact::new((*x.set).clone(), default_line_file()).into();
        let set_ok = self.verify_atomic_fact(&is_set_fact, verify_state)?;
        if set_ok.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "finite_seq_set: first argument {} is not a set",
                    x.set
                )),
            )));
        }
        let n_in_n_pos = InFact::new(
            (*x.n).clone(),
            StandardSet::NPos.into(),
            default_line_file(),
        )
        .into();
        let n_ok = self.verify_atomic_fact(&n_in_n_pos, verify_state)?;
        if n_ok.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "finite_seq_set: length argument {} is not verified in N_pos",
                    x.n
                )),
            )));
        }
        Ok(())
    }

    fn verify_seq_set_well_defined(
        &mut self,
        x: &SeqSet,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.set, verify_state)?;
        let is_set_fact = IsSetFact::new((*x.set).clone(), default_line_file()).into();
        let set_ok = self.verify_atomic_fact(&is_set_fact, verify_state)?;
        if set_ok.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "seq: argument {} is not a set",
                    x.set
                )),
            )));
        }
        Ok(())
    }

    fn verify_finite_seq_list_obj_well_defined(
        &mut self,
        x: &FiniteSeqListObj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        for o in x.objs.iter() {
            self.verify_obj_well_defined_and_store_cache(o, verify_state)?;
        }
        Ok(())
    }

    fn verify_matrix_set_well_defined(
        &mut self,
        x: &MatrixSet,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.set, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.row_len, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.col_len, verify_state)?;
        let is_set_fact = IsSetFact::new((*x.set).clone(), default_line_file()).into();
        let set_ok = self.verify_atomic_fact(&is_set_fact, verify_state)?;
        if set_ok.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "matrix: first argument {} is not a set",
                    x.set
                )),
            )));
        }
        for (label, len_obj) in [("row_len", &x.row_len), ("col_len", &x.col_len)] {
            let in_n_pos = InFact::new(
                (**len_obj).clone(),
                StandardSet::NPos.into(),
                default_line_file(),
            )
            .into();
            let ok = self.verify_atomic_fact(&in_n_pos, verify_state)?;
            if ok.is_unknown() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "matrix: {} argument {} is not verified in N_pos",
                        label, len_obj
                    )),
                )));
            }
        }
        Ok(())
    }

    fn verify_matrix_list_obj_well_defined(
        &mut self,
        x: &MatrixListObj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        if !x.rows.is_empty() {
            let col_len = x.rows[0].len();
            for row in x.rows.iter() {
                if row.len() != col_len {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "matrix literal: row length {} differs from first row length {}",
                            row.len(),
                            col_len
                        )),
                    )));
                }
            }
        }
        for row in x.rows.iter() {
            for o in row.iter() {
                self.verify_obj_well_defined_and_store_cache(o, verify_state)?;
            }
        }
        Ok(())
    }

    fn verify_matrix_add_well_defined(
        &mut self,
        ma: &MatrixAdd,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&ma.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&ma.right, verify_state)?;
        let shape_left = Self::matrix_value_shape(self, &ma.left)?;
        let shape_right = Self::matrix_value_shape(self, &ma.right)?;
        if shape_left != shape_right {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "matrix ++: shape {:?} and {:?} do not match",
                    shape_left, shape_right
                )),
            )));
        }
        Ok(())
    }

    fn verify_matrix_sub_well_defined(
        &mut self,
        ms: &MatrixSub,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&ms.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&ms.right, verify_state)?;
        let shape_left = Self::matrix_value_shape(self, &ms.left)?;
        let shape_right = Self::matrix_value_shape(self, &ms.right)?;
        if shape_left != shape_right {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "matrix --: shape {:?} and {:?} do not match",
                    shape_left, shape_right
                )),
            )));
        }
        Ok(())
    }

    fn verify_matrix_mul_well_defined(
        &mut self,
        mm: &MatrixMul,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&mm.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&mm.right, verify_state)?;
        let shape_left = Self::matrix_value_shape(self, &mm.left)?;
        let shape_right = Self::matrix_value_shape(self, &mm.right)?;
        if shape_left.1 != shape_right.0 {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "matrix **: left columns {} != right rows {}",
                    shape_left.1, shape_right.0
                )),
            )));
        }
        Ok(())
    }

    fn verify_matrix_scalar_mul_well_defined(
        &mut self,
        m: &MatrixScalarMul,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&m.scalar, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&m.matrix, verify_state)?;
        let _ = Self::matrix_value_shape(self, &m.matrix)?;
        Ok(())
    }

    fn verify_matrix_pow_well_defined(
        &mut self,
        m: &MatrixPow,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&m.base, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&m.exponent, verify_state)?;
        let shape_base = Self::matrix_value_shape(self, &m.base)?;
        if shape_base.0 != shape_base.1 {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "matrix ^^: base must be square, got {}x{}",
                    shape_base.0, shape_base.1
                )),
            )));
        }
        let exp_in_n_pos = InFact::new(
            (*m.exponent).clone(),
            StandardSet::NPos.into(),
            default_line_file(),
        )
        .into();
        let ok = self.verify_atomic_fact(&exp_in_n_pos, verify_state)?;
        if ok.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "matrix ^^: exponent {} is not verified in N_pos",
                    m.exponent
                )),
            )));
        }
        Ok(())
    }

    /// Dimensions of a matrix-valued expression (literal, known name, or matrix operators).
    fn matrix_value_shape(rt: &Runtime, obj: &Obj) -> Result<(usize, usize), RuntimeError> {
        match obj {
            Obj::MatrixListObj(m) => Self::rectangular_shape_of_matrix_list_obj(m),
            Obj::Atom(AtomObj::Identifier(id)) => {
                Self::matrix_list_shape_for_name_known_as_matrix_list(rt, &id.name)
            }
            Obj::MatrixAdd(inner) => Self::matrix_value_shape(rt, &inner.left),
            Obj::MatrixSub(inner) => Self::matrix_value_shape(rt, &inner.left),
            Obj::MatrixMul(inner) => {
                let sl = Self::matrix_value_shape(rt, &inner.left)?;
                let sr = Self::matrix_value_shape(rt, &inner.right)?;
                if sl.1 != sr.0 {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "matrix **: left columns {} != right rows {}",
                            sl.1, sr.0
                        )),
                    )));
                }
                Ok((sl.0, sr.1))
            }
            Obj::MatrixScalarMul(inner) => Self::matrix_value_shape(rt, &inner.matrix),
            Obj::MatrixPow(inner) => {
                let s = Self::matrix_value_shape(rt, &inner.base)?;
                if s.0 != s.1 {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "matrix ^^: base must be square, got {}x{}",
                            s.0, s.1
                        )),
                    )));
                }
                Ok(s)
            }
            _ => Self::matrix_list_shape_for_name_known_as_matrix_list(rt, &obj.to_string()),
        }
    }

    /// Shape of a matrix list stored under `key` in `known_objs_equal_to_matrix_list`.
    /// When the entry carries a `MatrixSet`, resolved `row_len` / `col_len` must match the list shape.
    fn matrix_list_shape_for_name_known_as_matrix_list(
        rt: &Runtime,
        key: &str,
    ) -> Result<(usize, usize), RuntimeError> {
        let Some(known) = rt.get_obj_equal_to_matrix_list(key) else {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "`{}` is not known as a matrix list value",
                    key
                )),
            )));
        };
        let shape = Self::rectangular_shape_of_matrix_list_obj(&known)?;
        if let Some(ms) = rt.get_matrix_set_for_obj_equal_to_matrix_list(key) {
            Self::ensure_matrix_list_matches_matrix_set(rt, &known, &ms)?;
        }
        Ok(shape)
    }

    fn ensure_matrix_list_matches_matrix_set(
        rt: &Runtime,
        m: &MatrixListObj,
        ms: &MatrixSet,
    ) -> Result<(), RuntimeError> {
        let (rows, cols) = Self::rectangular_shape_of_matrix_list_obj(m)?;
        let row_expect = rt
            .resolve_obj_to_number(ms.row_len.as_ref())
            .ok_or_else(|| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "matrix: cannot resolve row_len {} of matrix type for list shape check",
                        ms.row_len
                    )),
                ))
            })?;
        let col_expect = rt
            .resolve_obj_to_number(ms.col_len.as_ref())
            .ok_or_else(|| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "matrix: cannot resolve col_len {} of matrix type for list shape check",
                        ms.col_len
                    )),
                ))
            })?;
        let r = row_expect.normalized_value.parse::<usize>().map_err(|_| {
            RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "matrix: row_len `{}` is not a valid size",
                    row_expect.normalized_value
                )),
            ))
        })?;
        let c = col_expect.normalized_value.parse::<usize>().map_err(|_| {
            RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "matrix: col_len `{}` is not a valid size",
                    col_expect.normalized_value
                )),
            ))
        })?;
        if r != rows || c != cols {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "matrix list has shape {}x{} but matrix type expects {}x{}",
                    rows, cols, r, c
                )),
            )));
        }
        Ok(())
    }

    fn rectangular_shape_of_matrix_list_obj(
        m: &MatrixListObj,
    ) -> Result<(usize, usize), RuntimeError> {
        let rows = m.rows.len();
        let cols = if rows == 0 { 0 } else { m.rows[0].len() };
        for row in m.rows.iter() {
            if row.len() != cols {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(
                        "matrix list is not rectangular (row lengths differ)".to_string(),
                    ),
                )));
            }
        }
        Ok((rows, cols))
    }

    fn verify_power_set_well_defined(
        &mut self,
        x: &PowerSet,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.set, verify_state)?;
        Ok(())
    }

    fn verify_choose_well_defined(
        &mut self,
        _x: &Choose,
        _verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        let choose_from = *_x.set.clone();

        let choose_from_is_nonempty_set_fact = AtomicFact::IsNonemptySetFact(
            IsNonemptySetFact::new(choose_from.clone(), default_line_file()),
        );
        let choose_from_is_nonempty_set_result =
            self.verify_atomic_fact(&choose_from_is_nonempty_set_fact, _verify_state)?;
        if choose_from_is_nonempty_set_result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "set {} is not a nonempty set",
                    choose_from.to_string()
                )),
            )));
        }

        let random_param = self.generate_random_unused_name();

        let nonempty_set_fact = IsNonemptySetFact::new(
            obj_for_bound_param_in_scope(random_param.clone(), ParamObjType::Forall),
            default_line_file(),
        );

        let forall_x_in_choose_from_x_is_nonempty = ForallFact::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![random_param.clone().to_string()],
                ParamType::Obj(choose_from),
            )]),
            vec![],
            vec![nonempty_set_fact.into()],
            default_line_file(),
        )?
        .into();

        self.verify_fact(&forall_x_in_choose_from_x_is_nonempty, _verify_state)?;

        Ok(())
    }

    fn verify_obj_at_index_well_defined(
        &mut self,
        x: &ObjAtIndex,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.obj, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.index, verify_state)?;

        let index_calculated_number = self.resolve_obj_to_number(&x.index).ok_or_else(|| {
            RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "index {} is not a number",
                    x.index.to_string()
                )),
            ))
        })?;
        let index_calculated_obj: Obj =
            Number::new(index_calculated_number.normalized_value).into();

        let index_is_positive_integer_in_z_pos_fact = InFact::new(
            index_calculated_obj.clone(),
            StandardSet::NPos.into(),
            default_line_file(),
        )
        .into();
        let index_is_positive_integer_result =
            self.verify_atomic_fact(&index_is_positive_integer_in_z_pos_fact, verify_state)?;
        if index_is_positive_integer_result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "index {} is not a positive integer",
                    index_calculated_obj
                )),
            )));
        }

        let target_obj_is_tuple_fact =
            IsTupleFact::new((*x.obj).clone(), default_line_file()).into();
        let target_obj_is_tuple_result =
            self.verify_atomic_fact(&target_obj_is_tuple_fact, verify_state)?;
        if target_obj_is_tuple_result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "index target {} is not a tuple",
                    x.obj
                )),
            )));
        }

        let target_tuple_dim_obj: Obj = TupleDim::new((*x.obj).clone()).into();
        let index_not_larger_than_tuple_dim_fact = LessEqualFact::new(
            index_calculated_obj.clone(),
            target_tuple_dim_obj.clone(),
            default_line_file(),
        )
        .into();
        let index_not_larger_than_tuple_dim_result =
            self.verify_atomic_fact(&index_not_larger_than_tuple_dim_fact, verify_state)?;
        if index_not_larger_than_tuple_dim_result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{} <= {} is unknown",
                    index_calculated_obj, target_tuple_dim_obj
                )),
            )));
        }

        Ok(())
    }

    fn verify_q_pos_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn verify_r_pos_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn verify_q_neg_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn verify_z_neg_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn verify_r_neg_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn verify_q_nz_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn verify_z_nz_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn verify_r_nz_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }
}

impl Runtime {
    pub fn verify_param_type_well_defined(
        &mut self,
        param_type: &ParamType,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        match param_type {
            ParamType::Set(_) => Ok(()),
            ParamType::NonemptySet(_) => Ok(()),
            ParamType::FiniteSet(_) => Ok(()),
            ParamType::Restrictive(fs) => {
                self.verify_obj_well_defined_and_store_cache(&Obj::FnSet(fs.clone()), verify_state)
            }
            ParamType::Obj(obj) => match obj {
                Obj::FamilyObj(family) => {
                    self.verify_param_type_family_well_defined(family, verify_state)
                }
                _ => self.verify_obj_well_defined_and_store_cache(obj, verify_state),
            },
        }
    }

    fn verify_param_type_family_well_defined(
        &mut self,
        family_param_type: &FamilyObj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        let family_name = family_param_type.name.to_string();
        let def = match self.get_cloned_family_definition_by_name(&family_name) {
            Some(d) => d,
            None => {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "family `{}` is not defined",
                        family_name
                    )),
                )));
            }
        };

        let expected_count = def.params_def_with_type.number_of_params();
        if family_param_type.params.len() != expected_count {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "family `{}` expects {} parameter(s), got {}",
                    family_name,
                    expected_count,
                    family_param_type.params.len()
                )),
            )));
        }

        for arg in family_param_type.params.iter() {
            self.verify_obj_well_defined_and_store_cache(arg, verify_state)?;
        }

        let args_param_types = self
            .verify_args_satisfy_param_def_flat_types(
                &def.params_def_with_type,
                &family_param_type.params,
                verify_state,
                ParamObjType::DefHeader,
            )
            .map_err(|runtime_error| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!(
                            "failed to verify family `{}` arguments satisfy parameter types",
                            family_name
                        ),
                        runtime_error,
                    ),
                ))
            })?;
        if args_param_types.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "failed to verify family `{}` arguments satisfy parameter types",
                    family_name
                )),
            )));
        }

        let param_to_arg_map = def
            .params_def_with_type
            .param_defs_and_args_to_param_to_arg_map(family_param_type.params.as_slice());

        for dom_fact in def.dom_facts.iter() {
            let instantiated_dom_fact = self
                .inst_or_and_chain_atomic_fact(
                    dom_fact,
                    &param_to_arg_map,
                    ParamObjType::DefHeader,
                    None,
                )
                .map_err(|e| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!(
                                "failed to instantiate family `{}` domain fact: {}",
                                family_name, e
                            ),
                            e,
                        ),
                    ))
                })?;
            let verify_result = self
                .verify_or_and_chain_atomic_fact(&instantiated_dom_fact, verify_state)
                .map_err(|verify_error| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!(
                                "failed to verify family `{}` domain fact:\n{}",
                                family_name, instantiated_dom_fact
                            ),
                            verify_error,
                        ),
                    ))
                })?;
            if verify_result.is_unknown() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "failed to verify family `{}` domain fact:\n{}",
                        family_name, instantiated_dom_fact
                    )),
                )));
            }
        }

        let instantiated_equal_to = self
            .inst_obj(&def.equal_to, &param_to_arg_map, ParamObjType::DefHeader)
            .map_err(|e| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!(
                            "failed to instantiate family `{}` member set: {}",
                            family_name, e
                        ),
                        e,
                    ),
                ))
            })?;
        self.verify_obj_well_defined_and_store_cache(&instantiated_equal_to, verify_state)?;

        Ok(())
    }
}
