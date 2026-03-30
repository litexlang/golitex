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
    ) -> Result<(), WellDefinedError> {
        if self
            .verify_obj_well_defined_from_cache_if_known(obj)
            .is_some()
        {
            return Ok(());
        }

        let use_cache = !matches!(obj, Obj::FnSetWithParams(_) | Obj::SetBuilder(_));

        match obj {
            Obj::Identifier(identifier) => self.verify_identifier_well_defined(identifier),
            Obj::IdentifierWithMod(x) => self.verify_identifier_with_mod_well_defined(x),
            Obj::FieldAccess(x) => self.verify_field_access_well_defined(x),
            Obj::FieldAccessWithMod(x) => self.verify_field_access_with_mod_well_defined(x),
            Obj::FnObj(fn_obj) => self.verify_fn_obj_well_defined(fn_obj, verify_state),
            Obj::Number(_) => Ok(()),
            Obj::Add(add) => self.verify_add_well_defined(add, verify_state),
            Obj::Sub(sub) => self.verify_sub_well_defined(sub, verify_state),
            Obj::Mul(mul) => self.verify_mul_well_defined(mul, verify_state),
            Obj::Div(div) => self.verify_div_well_defined(div, verify_state),
            Obj::Mod(m) => self.verify_mod_well_defined(m, verify_state),
            Obj::Pow(pow) => self.verify_pow_well_defined(pow, verify_state),
            Obj::Union(x) => self.verify_union_well_defined(x, verify_state),
            Obj::Intersect(x) => self.verify_intersect_well_defined(x, verify_state),
            Obj::SetMinus(x) => self.verify_set_minus_well_defined(x, verify_state),
            Obj::SetDiff(x) => self.verify_set_diff_well_defined(x, verify_state),
            Obj::Cup(x) => self.verify_cup_well_defined(x, verify_state),
            Obj::Cap(x) => self.verify_cap_well_defined(x, verify_state),
            Obj::ListSet(x) => self.verify_list_set_well_defined(x, verify_state),
            Obj::SetBuilder(x) => self.verify_set_builder_well_defined(x, verify_state),
            Obj::FnSetWithoutParams(x) => {
                self.verify_fn_set_without_dom_well_defined(x, verify_state)
            }
            Obj::FnSetWithParams(x) => self.verify_fn_set_with_dom_well_defined(x, verify_state),
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
            Obj::Range(x) => self.verify_range_well_defined(x, verify_state),
            Obj::ClosedRange(x) => self.verify_closed_range_well_defined(x, verify_state),
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
        }?;

        if use_cache {
            self.top_level_env()
                .cache_well_defined_obj
                .insert(obj.to_string(), ());
        }
        Ok(())
    }

    fn verify_identifier_well_defined(
        &self,
        identifier: &Identifier,
    ) -> Result<(), WellDefinedError> {
        if self.is_name_used_for_identifier_and_field_access(&identifier.name) {
            Ok(())
        } else {
            Err(WellDefinedError::new(
                format!("identifier `{}` not defined", identifier.to_string()),
                None,
                DEFAULT_LINE_FILE.clone(),
            ))
        }
    }

    fn verify_identifier_with_mod_well_defined(
        &self,
        x: &IdentifierWithMod,
    ) -> Result<(), WellDefinedError> {
        let _ = x;
        unreachable!()
    }

    fn verify_field_access_well_defined(&self, x: &FieldAccess) -> Result<(), WellDefinedError> {
        let key = x.to_string();
        if self.is_name_used_for_identifier_and_field_access(&key) {
            return Ok(());
        }

        return Err(WellDefinedError::new(
            format!("field access `{}` not defined", x.to_string()),
            None,
            DEFAULT_LINE_FILE.clone(),
        ));
    }

    fn verify_field_access_with_mod_well_defined(
        &self,
        x: &FieldAccessWithMod,
    ) -> Result<(), WellDefinedError> {
        let _ = x;
        unreachable!()
    }

    fn verify_fn_obj_well_defined(
        &mut self,
        fn_obj: &FnObj,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        let mut the_set_where_current_fn_obj_is_in = self
            .get_fn_set_where_fn_belongs_to(&fn_obj.head)
            .ok_or_else(|| {
                WellDefinedError::new(
                    todo_error_message(format!(
                        "`{}` is not a defined function",
                        fn_obj.head.to_string()
                    )),
                    None,
                    DEFAULT_LINE_FILE.clone(),
                )
            })?
            .clone();

        for (i, args) in fn_obj.body.iter().enumerate() {
            match &the_set_where_current_fn_obj_is_in {
                FnSetObj::FnSetWithDom(fn_set_with_dom) => {
                    self.verify_fn_obj_well_defined_against_fn_set_with_dom(args, &fn_set_with_dom, verify_state).map_err(|well_defined_error| WellDefinedError::new(
                        format!("object {} is not well-defined, failed to verify arguments satisfy function domain.", fn_obj.to_string()),
                        Some(RuntimeError::WellDefinedError(well_defined_error)),
                        DEFAULT_LINE_FILE.clone(),
                    ))?;
                }
                FnSetObj::FnSetWithoutParams(fn_set_without_dom) => {
                    self.verify_fn_obj_args_well_defined_against_fn_set_without_dom(
                        args,
                        &fn_set_without_dom,
                        verify_state,
                    )?;
                }
            }

            let set_where_the_next_fn_obj_is_in = the_set_where_current_fn_obj_is_in.ret_set();

            // Store: after applying current argument group i,
            // the intermediate prefix application fn_obj_prefix (e.g. f(a))
            // must be in the current function set's return set.
            //
            // Example: input is f(a)(b), body = [[a], [b]]
            // at i=0 we store: f(a) in ret_set_of_f
            let fn_obj_prefix_body: Vec<Vec<Box<Obj>>> =
                fn_obj.body[..=i].iter().cloned().collect();
            let fn_obj_prefix = FnObj {
                head: fn_obj.head.clone(),
                body: fn_obj_prefix_body,
            };
            let fn_obj_prefix_as_obj = Obj::FnObj(fn_obj_prefix);
            let set_where_the_next_fn_obj_is_in_obj =
                (*set_where_the_next_fn_obj_is_in.clone()).clone();
            let intermediate_in_fact = InFact::new(
                fn_obj_prefix_as_obj,
                set_where_the_next_fn_obj_is_in_obj,
                DEFAULT_LINE_FILE.clone(),
            );
            let intermediate_atomic_fact = AtomicFact::InFact(intermediate_in_fact);
            self.store_fact_without_well_defined_verified_and_infer(&Fact::AtomicFact(
                intermediate_atomic_fact,
            ))
            .map_err(|store_fact_error| {
                WellDefinedError::new(
                    format!(
                        "failed to store intermediate fn-obj membership fact while verifying `{}`",
                        fn_obj.to_string()
                    ),
                    Some(store_fact_error.into()),
                    DEFAULT_LINE_FILE.clone(),
                )
            })?;

            if i == fn_obj.body.len() - 1 {
                break;
            }

            the_set_where_current_fn_obj_is_in = match *set_where_the_next_fn_obj_is_in {
                Obj::FnSetWithParams(e) => FnSetObj::FnSetWithDom(e),
                Obj::FnSetWithoutParams(e) => FnSetObj::FnSetWithoutParams(e),
                _ => {
                    return Err(WellDefinedError::new(
                        format!(
                            "expect return set of {} to be a fn_set object.",
                            the_set_where_current_fn_obj_is_in.to_string()
                        ),
                        None,
                        DEFAULT_LINE_FILE.clone(),
                    ));
                }
            };
        }

        Ok(())
    }

    /// Verify that the given FnObj is well-defined with respect to a FnSetWithDom definition.
    fn verify_fn_obj_well_defined_against_fn_set_with_dom(
        &mut self,
        args: &Vec<Box<Obj>>,
        fn_set_with_dom: &FnSetWithParams,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        let param_count =
            ParamDefWithParamSet::number_of_params(&fn_set_with_dom.params_def_with_set);
        if args.len() != param_count {
            return Err(WellDefinedError::new(
                format!(
                    "number of args ({}) does not match fn set with dom param count ({})",
                    args.len(),
                    param_count
                ),
                None,
                DEFAULT_LINE_FILE.clone(),
            ));
        }

        for arg in args.iter() {
            self.verify_obj_well_defined_and_store_cache(arg, verify_state)?;
        }

        let mut args_as_obj: Vec<Obj> = Vec::with_capacity(args.len());
        for arg in args.iter() {
            args_as_obj.push((**arg).clone());
        }

        let args_satisfy_fn_set_params_set_facts =
            ParamDefWithParamSet::facts_for_args_satisfy_param_def_with_set_vec(
                &fn_set_with_dom.params_def_with_set,
                &args_as_obj,
            )
            .map_err(|stmt_error| {
                WellDefinedError::new(
                    format!("failed to build facts for args satisfy fn set parameter sets"),
                    Some(stmt_error),
                    DEFAULT_LINE_FILE.clone(),
                )
            })?;

        for fact in args_satisfy_fn_set_params_set_facts.iter() {
            let verify_result =
                self.verify_atomic_fact(fact, verify_state)
                    .map_err(|verify_error| {
                        WellDefinedError::new(
                            format!(
                                "failed to verify arg satisfy fn set parameter set: {}",
                                fact
                            ),
                            Some(RuntimeError::VerifyError(verify_error)),
                            DEFAULT_LINE_FILE.clone(),
                        )
                    })?;
            if verify_result.is_unknown() {
                return Err(WellDefinedError::new(
                    format!("arg does not satisfy fn set parameter set: {}", fact),
                    None,
                    DEFAULT_LINE_FILE.clone(),
                ));
            }
        }

        let param_to_arg_map = ParamDefWithParamSet::param_defs_and_args_to_param_to_arg_map(
            &fn_set_with_dom.params_def_with_set,
            &args_as_obj,
        );
        for dom_fact in fn_set_with_dom.dom_facts.iter() {
            let instantiated_dom_fact = dom_fact.instantiate(&param_to_arg_map);
            let verify_result = self
                .verify_or_and_chain_atomic_fact(&instantiated_dom_fact, verify_state)
                .map_err(|verify_error| {
                    WellDefinedError::new(
                        format!(
                            "failed to verify function domain fact:\n{}",
                            instantiated_dom_fact
                        ),
                        Some(RuntimeError::VerifyError(verify_error)),
                        DEFAULT_LINE_FILE.clone(),
                    )
                })?;
            if verify_result.is_unknown() {
                return Err(WellDefinedError::new(
                    format!(
                        "failed to verify function domain fact:\n{}",
                        instantiated_dom_fact
                    ),
                    None,
                    DEFAULT_LINE_FILE.clone(),
                ));
            }
        }

        Ok(())
    }

    /// Verify that the given FnObj is well-defined with respect to a FnSetWithoutDom definition.
    fn verify_fn_obj_args_well_defined_against_fn_set_without_dom(
        &mut self,
        args: &Vec<Box<Obj>>,
        fn_set_without_dom: &FnSetWithoutParams,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        let param_count = fn_set_without_dom.param_sets.len();
        if args.len() != param_count {
            return Err(WellDefinedError::new(
                format!(
                    "number of args ({}) does not match fn set without dom param count ({})",
                    args.len(),
                    param_count
                ),
                None,
                DEFAULT_LINE_FILE.clone(),
            ));
        }

        for (index, arg) in args.iter().enumerate() {
            self.verify_obj_well_defined_and_store_cache(arg, verify_state)?;
            let param_set = &fn_set_without_dom.param_sets[index];
            let in_fact = InFact::new(
                (**arg).clone(),
                (**param_set).clone(),
                DEFAULT_LINE_FILE.clone(),
            );
            let atomic_fact = AtomicFact::InFact(in_fact);
            let result = self.verify_atomic_fact(&atomic_fact, verify_state)?;
            if result.is_unknown() {
                return Err(WellDefinedError::new(
                    format!(
                        "arg {} is not in param set {}",
                        (**arg).to_string(),
                        (**param_set).to_string()
                    ),
                    None,
                    DEFAULT_LINE_FILE.clone(),
                ));
            }
        }

        Ok(())
    }

    fn require_obj_in_r(
        &mut self,
        obj: &Obj,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        let r_obj = Obj::StandardSet(StandardSet::R);
        let in_fact = InFact::new(obj.clone(), r_obj, DEFAULT_LINE_FILE.clone());
        let atomic_fact = AtomicFact::InFact(in_fact);
        let result = self.verify_atomic_fact(&atomic_fact, verify_state)?;
        if result.is_unknown() {
            return Err(WellDefinedError::new(
                format!("obj {} is not in r", obj.to_string()),
                None,
                DEFAULT_LINE_FILE.clone(),
            ));
        }
        Ok(())
    }

    fn require_obj_in_z(
        &mut self,
        obj: &Obj,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        let z_obj = Obj::StandardSet(StandardSet::Z);
        let in_fact = InFact::new(obj.clone(), z_obj, DEFAULT_LINE_FILE.clone());
        let atomic_fact = AtomicFact::InFact(in_fact);
        let result = self.verify_atomic_fact(&atomic_fact, verify_state)?;
        if result.is_unknown() {
            return Err(WellDefinedError::new(
                format!("obj {} is not in z", obj.to_string()),
                None,
                DEFAULT_LINE_FILE.clone(),
            ));
        }
        Ok(())
    }

    fn verify_add_well_defined(
        &mut self,
        add: &Add,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
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
    ) -> Result<(), WellDefinedError> {
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
    ) -> Result<(), WellDefinedError> {
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
    ) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&div.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&div.right, verify_state)?;

        let zero = Obj::Number(Number::new("0".to_string()));
        let not_equal_fact =
            NotEqualFact::new((*div.right).clone(), zero, DEFAULT_LINE_FILE.clone());
        let atomic_fact = AtomicFact::NotEqualFact(not_equal_fact);
        let result = self.verify_atomic_fact(&atomic_fact, verify_state)?;
        if result.is_unknown() {
            return Err(WellDefinedError::new(
                format!("divisor `{}` must be non-zero", div.right.to_string()),
                None,
                DEFAULT_LINE_FILE.clone(),
            ));
        }

        self.require_obj_in_r(&div.left, verify_state)?;
        self.require_obj_in_r(&div.right, verify_state)?;
        Ok(())
    }

    fn verify_mod_well_defined(
        &mut self,
        m: &Mod,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&m.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&m.right, verify_state)?;
        self.require_obj_in_z(&m.left, verify_state)?;
        self.require_obj_in_z(&m.right, verify_state)?;
        let zero = Obj::Number(Number::new("0".to_string()));
        let not_equal_fact = NotEqualFact::new((*m.right).clone(), zero, DEFAULT_LINE_FILE.clone());
        let atomic_fact = AtomicFact::NotEqualFact(not_equal_fact);
        let result = self.verify_atomic_fact(&atomic_fact, verify_state)?;
        if result.is_unknown() {
            return Err(WellDefinedError::new(
                format!("modulus `{}` must be non-zero", m.right.to_string()),
                None,
                DEFAULT_LINE_FILE.clone(),
            ));
        }
        Ok(())
    }

    fn verify_pow_well_defined(
        &mut self,
        pow: &Pow,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&pow.base, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&pow.exponent, verify_state)?;

        let zero_obj = Obj::Number(Number::new("0".to_string()));
        let two_obj = Obj::Number(Number::new("2".to_string()));
        let exponent_mod_two_obj = Obj::Mod(Mod::new((*pow.exponent).clone(), two_obj));

        let positive_base_and_real_exponent = AndChainAtomicFact::AndFact(AndFact::new(
            vec![
                AtomicFact::GreaterFact(GreaterFact::new(
                    (*pow.base).clone(),
                    zero_obj.clone(),
                    DEFAULT_LINE_FILE,
                )),
                AtomicFact::InFact(InFact::new(
                    (*pow.exponent).clone(),
                    Obj::StandardSet(StandardSet::R),
                    DEFAULT_LINE_FILE,
                )),
            ],
            DEFAULT_LINE_FILE,
        ));

        let zero_base_and_positive_real_exponent = AndChainAtomicFact::AndFact(AndFact::new(
            vec![
                AtomicFact::EqualFact(EqualFact::new(
                    (*pow.base).clone(),
                    zero_obj.clone(),
                    DEFAULT_LINE_FILE,
                )),
                AtomicFact::InFact(InFact::new(
                    (*pow.exponent).clone(),
                    Obj::StandardSet(StandardSet::R),
                    DEFAULT_LINE_FILE,
                )),
                AtomicFact::GreaterFact(GreaterFact::new(
                    (*pow.exponent).clone(),
                    zero_obj.clone(),
                    DEFAULT_LINE_FILE,
                )),
            ],
            DEFAULT_LINE_FILE,
        ));

        let even_integer_exponent = AndChainAtomicFact::AndFact(AndFact::new(
            vec![
                AtomicFact::InFact(InFact::new(
                    (*pow.exponent).clone(),
                    Obj::StandardSet(StandardSet::Z),
                    DEFAULT_LINE_FILE,
                )),
                AtomicFact::EqualFact(EqualFact::new(
                    exponent_mod_two_obj,
                    zero_obj,
                    DEFAULT_LINE_FILE,
                )),
            ],
            DEFAULT_LINE_FILE,
        ));

        let exponent_is_positive_integer =
            AndChainAtomicFact::AtomicFact(AtomicFact::InFact(InFact::new(
                (*pow.exponent).clone(),
                Obj::StandardSet(StandardSet::NPos),
                DEFAULT_LINE_FILE,
            )));

        let pow_domain_or_fact = OrFact::new(
            vec![
                positive_base_and_real_exponent,
                zero_base_and_positive_real_exponent,
                even_integer_exponent,
                exponent_is_positive_integer,
            ],
            DEFAULT_LINE_FILE,
        );

        let result = self.verify_or_fact(&pow_domain_or_fact, verify_state)?;
        if result.is_unknown() {
            return Err(WellDefinedError::new(
                format!("base and exponent do not satisfy the pow domain"),
                None,
                DEFAULT_LINE_FILE.clone(),
            ));
        }
        Ok(())
    }

    fn verify_union_well_defined(
        &mut self,
        x: &Union,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&x.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.right, verify_state)?;
        Ok(())
    }

    fn verify_intersect_well_defined(
        &mut self,
        x: &Intersect,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&x.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.right, verify_state)?;
        Ok(())
    }

    fn verify_set_minus_well_defined(
        &mut self,
        x: &SetMinus,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&x.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.right, verify_state)?;
        Ok(())
    }

    fn verify_set_diff_well_defined(
        &mut self,
        x: &SetDiff,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&x.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.right, verify_state)?;
        Ok(())
    }

    fn verify_cup_well_defined(
        &mut self,
        x: &Cup,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&x.left, verify_state)?;
        Ok(())
    }

    fn verify_cap_well_defined(
        &mut self,
        x: &Cap,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&x.left, verify_state)?;
        Ok(())
    }

    fn verify_list_set_well_defined(
        &mut self,
        x: &ListSet,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
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
                let not_equal_atomic_fact = AtomicFact::NotEqualFact(NotEqualFact::new(
                    left_obj.clone(),
                    right_obj,
                    DEFAULT_LINE_FILE.clone(),
                ));
                let verify_result = self
                    .verify_atomic_fact(&not_equal_atomic_fact, &next_verify_state)
                    .map_err(|previous_error| {
                        WellDefinedError::new(
                            format!(
                                "failed to verify list set elements are pairwise not equal: {}",
                                not_equal_atomic_fact
                            ),
                            Some(RuntimeError::VerifyError(previous_error)),
                            DEFAULT_LINE_FILE.clone(),
                        )
                    })?;
                if verify_result.is_unknown() {
                    return Err(WellDefinedError::new(
                        format!("list set elements must be pairwise not equal, but it is not provable: {}", not_equal_atomic_fact),
                        None,
                        DEFAULT_LINE_FILE.clone(),
                    ));
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
    ) -> Result<(), WellDefinedError> {
        self.push_env();
        let result = self.verify_set_builder_well_defined_body(x, verify_state);
        self.pop_env();
        result
    }

    fn verify_set_builder_well_defined_body(
        &mut self,
        x: &SetBuilder,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        if let Err(e) = self.define_params_with_set(&ParamDefWithParamSet::new(
            vec![x.param.clone()],
            *x.param_set.clone(),
        )) {
            return Err(WellDefinedError::new(
                format!(
                    "failed to verify well-defined of set builder {}",
                    x.to_string()
                ),
                Some(RuntimeError::DefineParamsError(e)),
                DEFAULT_LINE_FILE.clone(),
            ));
        }

        for fact in x.facts.iter() {
            if let Err(e) = self.verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                fact,
                verify_state,
            ) {
                return Err(WellDefinedError::new(
                    format!(
                        "failed to verify well-defined of set builder {}",
                        x.to_string()
                    ),
                    Some(RuntimeError::ExecStmtError(e)),
                    DEFAULT_LINE_FILE.clone(),
                ));
            }
        }

        Ok(())
    }

    fn verify_fn_set_without_dom_well_defined(
        &mut self,
        x: &FnSetWithoutParams,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        for obj in &x.param_sets {
            self.verify_obj_well_defined_and_store_cache(obj, verify_state)?;
        }
        self.verify_obj_well_defined_and_store_cache(&x.ret_set, verify_state)?;
        Ok(())
    }

    fn verify_fn_set_with_dom_well_defined(
        &mut self,
        x: &FnSetWithParams,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        self.push_env();
        let result = self.verify_fn_set_with_dom_well_defined_body(x, verify_state);
        self.pop_env();
        result
    }

    fn verify_fn_set_with_dom_well_defined_body(
        &mut self,
        x: &FnSetWithParams,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        if let Err(e) = self.verify_obj_well_defined_and_store_cache(&x.ret_set, verify_state) {
            return Err(WellDefinedError::new(
                format!(
                    "failed to verify well-defined of fn set with dom {}",
                    x.to_string()
                ),
                Some(RuntimeError::WellDefinedError(e)),
                DEFAULT_LINE_FILE.clone(),
            ));
        }

        for param_def_with_set in x.params_def_with_set.iter() {
            if let Err(e) = self.define_params_with_set(param_def_with_set) {
                return Err(WellDefinedError::new(
                    format!(
                        "failed to verify well-defined of fn set with dom {}",
                        x.to_string()
                    ),
                    Some(RuntimeError::DefineParamsError(e)),
                    DEFAULT_LINE_FILE.clone(),
                ));
            }
        }

        for fact in x.dom_facts.iter() {
            if let Err(e) = self.verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                fact,
                verify_state,
            ) {
                return Err(WellDefinedError::new(
                    format!(
                        "failed to verify well-defined of fn set with dom {}",
                        x.to_string()
                    ),
                    Some(RuntimeError::ExecStmtError(e)),
                    DEFAULT_LINE_FILE.clone(),
                ));
            }
        }

        Ok(())
    }

    fn verify_n_pos_obj_well_defined(&mut self) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_n_obj_well_defined(&mut self) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_q_obj_well_defined(&self) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_z_obj_well_defined(&self) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_r_obj_well_defined(&self) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_cart_well_defined(
        &mut self,
        x: &Cart,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        for obj in &x.args {
            self.verify_obj_well_defined_and_store_cache(obj, verify_state)?;
        }
        Ok(())
    }

    fn verify_cart_dim_well_defined(
        &mut self,
        x: &CartDim,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&x.set, verify_state)?;

        let is_cart_fact =
            AtomicFact::IsCartFact(IsCartFact::new((*x.set).clone(), DEFAULT_LINE_FILE.clone()));
        let result = self.verify_atomic_fact(&is_cart_fact, verify_state)?;
        if result.is_unknown() {
            return Err(WellDefinedError::new(
                format!("set {} is not a cart", x.set.to_string()),
                None,
                DEFAULT_LINE_FILE.clone(),
            ));
        }

        Ok(())
    }

    fn verify_proj_well_defined(
        &mut self,
        x: &Proj,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&x.set, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.dim, verify_state)?;

        let projection_dimension_number = self.resolve_obj_to_number(&x.dim).ok_or_else(|| {
            WellDefinedError::new(
                format!("projection dimension {} is not a number", x.dim),
                None,
                DEFAULT_LINE_FILE.clone(),
            )
        })?;
        let projection_dimension_obj =
            Obj::Number(Number::new(projection_dimension_number.normalized_value));

        let projection_dimension_is_positive_integer_fact = AtomicFact::InFact(InFact::new(
            projection_dimension_obj.clone(),
            Obj::StandardSet(StandardSet::NPos),
            DEFAULT_LINE_FILE.clone(),
        ));
        let projection_dimension_is_positive_integer_result =
            self.verify_atomic_fact(&projection_dimension_is_positive_integer_fact, verify_state)?;
        if projection_dimension_is_positive_integer_result.is_unknown() {
            return Err(WellDefinedError::new(
                format!(
                    "projection dimension {} is not a positive integer",
                    projection_dimension_obj
                ),
                None,
                DEFAULT_LINE_FILE.clone(),
            ));
        }

        let left_set_is_cart_fact =
            AtomicFact::IsCartFact(IsCartFact::new((*x.set).clone(), DEFAULT_LINE_FILE.clone()));
        let left_set_is_cart_result =
            self.verify_atomic_fact(&left_set_is_cart_fact, verify_state)?;
        if left_set_is_cart_result.is_unknown() {
            return Err(WellDefinedError::new(
                format!("projection left side {} is not a cart", x.set),
                None,
                DEFAULT_LINE_FILE.clone(),
            ));
        }

        let left_set_cart_dim_obj = Obj::CartDim(CartDim::new((*x.set).clone()));

        let proj_index_not_larger_than_cart_dim = AtomicFact::LessEqualFact(LessEqualFact::new(
            projection_dimension_obj.clone(),
            left_set_cart_dim_obj.clone(),
            DEFAULT_LINE_FILE.clone(),
        ));
        let left_set_cart_dim_less_equal_projection_dimension_result =
            self.verify_atomic_fact(&proj_index_not_larger_than_cart_dim, verify_state)?;
        if left_set_cart_dim_less_equal_projection_dimension_result.is_unknown() {
            return Err(WellDefinedError::new(
                format!(
                    "{} <= {} is unknown",
                    projection_dimension_obj, left_set_cart_dim_obj
                ),
                None,
                DEFAULT_LINE_FILE.clone(),
            ));
        }

        Ok(())
    }

    fn verify_dim_well_defined(
        &mut self,
        x: &TupleDim,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&x.arg, verify_state)?;

        let is_tuple_fact = AtomicFact::IsTupleFact(IsTupleFact::new(
            (*x.arg).clone(),
            DEFAULT_LINE_FILE.clone(),
        ));
        let result = self.verify_atomic_fact(&is_tuple_fact, verify_state)?;
        if result.is_unknown() {
            return Err(WellDefinedError::new(
                format!(
                    "`{}` is unknown, `dim` object requires its argument to be a tuple",
                    is_tuple_fact
                ),
                None,
                DEFAULT_LINE_FILE.clone(),
            ));
        }

        Ok(())
    }

    fn verify_tuple_well_defined(
        &mut self,
        x: &Tuple,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        for obj in &x.args {
            self.verify_obj_well_defined_and_store_cache(obj, verify_state)?;
        }
        Ok(())
    }

    fn verify_count_well_defined(
        &mut self,
        x: &Count,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        // 必须 is_finite_set
        let is_finite_set_fact = AtomicFact::IsFiniteSetFact(IsFiniteSetFact::new(
            (*x.set).clone(),
            DEFAULT_LINE_FILE.clone(),
        ));
        let result = self.verify_atomic_fact(&is_finite_set_fact, verify_state)?;
        if result.is_unknown() {
            return Err(WellDefinedError::new(
                format!("set {} is not a finite set", x.set.to_string()),
                None,
                DEFAULT_LINE_FILE.clone(),
            ));
        }
        Ok(())
    }

    fn verify_range_well_defined(
        &mut self,
        x: &Range,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&x.start, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.end, verify_state)?;
        self.require_obj_in_z(&x.start, verify_state)?;
        self.require_obj_in_z(&x.end, verify_state)?;
        Ok(())
    }

    fn verify_closed_range_well_defined(
        &mut self,
        x: &ClosedRange,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&x.start, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.end, verify_state)?;
        self.require_obj_in_z(&x.start, verify_state)?;
        self.require_obj_in_z(&x.end, verify_state)?;
        Ok(())
    }

    fn verify_power_set_well_defined(
        &mut self,
        x: &PowerSet,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&x.set, verify_state)?;
        Ok(())
    }

    fn verify_choose_well_defined(
        &mut self,
        _x: &Choose,
        _verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        unimplemented!()
    }

    fn verify_obj_at_index_well_defined(
        &mut self,
        x: &ObjAtIndex,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&x.obj, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.index, verify_state)?;

        let index_calculated_number = self.resolve_obj_to_number(&x.index).ok_or_else(|| {
            WellDefinedError::new(
                format!("index {} is not a number", x.index.to_string()),
                None,
                DEFAULT_LINE_FILE.clone(),
            )
        })?;
        let index_calculated_obj =
            Obj::Number(Number::new(index_calculated_number.normalized_value));

        let index_is_positive_integer_in_z_pos_fact = AtomicFact::InFact(InFact::new(
            index_calculated_obj.clone(),
            Obj::StandardSet(StandardSet::NPos),
            DEFAULT_LINE_FILE.clone(),
        ));
        let index_is_positive_integer_result =
            self.verify_atomic_fact(&index_is_positive_integer_in_z_pos_fact, verify_state)?;
        if index_is_positive_integer_result.is_unknown() {
            return Err(WellDefinedError::new(
                format!("index {} is not a positive integer", index_calculated_obj),
                None,
                DEFAULT_LINE_FILE.clone(),
            ));
        }

        let target_obj_is_tuple_fact = AtomicFact::IsTupleFact(IsTupleFact::new(
            (*x.obj).clone(),
            DEFAULT_LINE_FILE.clone(),
        ));
        let target_obj_is_tuple_result =
            self.verify_atomic_fact(&target_obj_is_tuple_fact, verify_state)?;
        if target_obj_is_tuple_result.is_unknown() {
            return Err(WellDefinedError::new(
                format!("index target {} is not a tuple", x.obj),
                None,
                DEFAULT_LINE_FILE.clone(),
            ));
        }

        let target_tuple_dim_obj = Obj::TupleDim(TupleDim::new((*x.obj).clone()));
        let index_not_larger_than_tuple_dim_fact = AtomicFact::LessEqualFact(LessEqualFact::new(
            index_calculated_obj.clone(),
            target_tuple_dim_obj.clone(),
            DEFAULT_LINE_FILE.clone(),
        ));
        let index_not_larger_than_tuple_dim_result =
            self.verify_atomic_fact(&index_not_larger_than_tuple_dim_fact, verify_state)?;
        if index_not_larger_than_tuple_dim_result.is_unknown() {
            return Err(WellDefinedError::new(
                format!(
                    "{} <= {} is unknown",
                    index_calculated_obj, target_tuple_dim_obj
                ),
                None,
                DEFAULT_LINE_FILE.clone(),
            ));
        }

        Ok(())
    }

    fn verify_q_pos_well_defined(&self) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_r_pos_well_defined(&self) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_q_neg_well_defined(&self) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_z_neg_well_defined(&self) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_r_neg_well_defined(&self) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_q_nz_well_defined(&self) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_z_nz_well_defined(&self) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_r_nz_well_defined(&self) -> Result<(), WellDefinedError> {
        Ok(())
    }
}

impl Runtime {
    pub fn verify_param_type_well_defined(
        &mut self,
        param_type: &ParamType,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        match param_type {
            ParamType::Set(_) => Ok(()),
            ParamType::NonemptySet(_) => Ok(()),
            ParamType::FiniteSet(_) => Ok(()),
            ParamType::Obj(obj) => self.verify_obj_well_defined_and_store_cache(obj, verify_state),
            ParamType::InstantiatedStruct(_) => {
                unimplemented!("instantiated struct param type is not supported yet");
            }
        }
    }
}
