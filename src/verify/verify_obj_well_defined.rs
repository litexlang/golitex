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
    ) -> Result<(), RuntimeError> {
        if self.is_name_used_for_identifier_and_field_access(&identifier.name) {
            Ok(())
        } else {
            Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                format!("identifier `{}` not defined", identifier.to_string()),
                None,
                default_line_file(),
            ))
        }
    }

    fn verify_identifier_with_mod_well_defined(
        &self,
        x: &IdentifierWithMod,
    ) -> Result<(), RuntimeError> {
        let _ = x;
        unreachable!()
    }

    fn verify_field_access_well_defined(&self, x: &FieldAccess) -> Result<(), RuntimeError> {
        let Some(def) = self.get_definition_of_struct_where_object_satisfies(&IdentifierOrIdentifierWithMod::Identifier(Identifier::new(x.name.to_string()))) else {
            return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                format!("field access `{}` unknown, `{}` is not a struct", x.to_string(), x.name.to_string()),
                None,
                default_line_file(),
            ));
        };

        for field in def.fields.iter() {
            if field.0 == x.field.to_string() {
                return Ok(());
            }
        }

        return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
            format!("field access `{}` unknown, {} does not contain field `{}`", x.to_string(), x.name.to_string(), x.field.to_string()),
            None,
            default_line_file(),
        ));
    }

    fn verify_field_access_with_mod_well_defined(
        &self,
        x: &FieldAccessWithMod,
    ) -> Result<(), RuntimeError> {
        let _ = x;
        unreachable!()
    }

    fn verify_fn_obj_well_defined(
        &mut self,
        fn_obj: &FnObj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        let function_name_obj = Obj::Identifier(Identifier::new(fn_obj.head.to_string()));
        let mut the_set_where_current_fn_obj_is_in = self
            .get_fn_set_where_fn_belongs_to(&function_name_obj)
            .ok_or_else(|| {
                RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                    todo_error_message(format!(
                        "`{}` is not a defined function",
                        fn_obj.head.to_string()
                    )),
                    None,
                    default_line_file(),
                )
            })?
            .clone();

        for (i, args) in fn_obj.body.iter().enumerate() {
            self.verify_fn_obj_well_defined_against_fn_set_with_dom(
                args,
                &the_set_where_current_fn_obj_is_in,
                verify_state,
            )
            .map_err(|well_defined_error| {
                RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                    format!(
                        "object {} is not well-defined, failed to verify arguments satisfy function domain.",
                        fn_obj.to_string()
                    ),
                    Some(well_defined_error.into()),
                    default_line_file(),
                )
            })?;

            let set_where_the_next_fn_obj_is_in = the_set_where_current_fn_obj_is_in.ret_set.clone();

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
                default_line_file(),
            );
            let intermediate_atomic_fact = AtomicFact::InFact(intermediate_in_fact);
            self.store_fact_without_well_defined_verified_and_infer(Fact::AtomicFact(
                intermediate_atomic_fact,
            ))
            .map_err(|store_fact_error| {
                RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                    format!(
                        "failed to store intermediate fn-obj membership fact while verifying `{}`",
                        fn_obj.to_string()
                    ),
                    Some(store_fact_error.into()),
                    default_line_file(),
                )
            })?;

            if i == fn_obj.body.len() - 1 {
                break;
            }

            the_set_where_current_fn_obj_is_in = match *set_where_the_next_fn_obj_is_in {
                Obj::FnSetWithParams(e) => e,
                _ => {
                    return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                        format!(
                            "expect return set of {} to be a fn_set object.",
                            the_set_where_current_fn_obj_is_in.to_string()
                        ),
                        None,
                        default_line_file(),
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
    ) -> Result<(), RuntimeError> {
        let param_count =
            ParamDefWithParamSet::number_of_params(&fn_set_with_dom.params_def_with_set);
        if args.len() != param_count {
            return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                format!(
                    "number of args ({}) does not match fn set with dom param count ({})",
                    args.len(),
                    param_count
                ),
                None,
                default_line_file(),
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
                self,
                &fn_set_with_dom.params_def_with_set,
                &args_as_obj,
            )
            .map_err(|stmt_error| {
                RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                    format!("failed to build facts for args satisfy fn set parameter sets"),
                    Some(stmt_error),
                    default_line_file(),
                )
            })?;

        for fact in args_satisfy_fn_set_params_set_facts.iter() {
            let verify_result =
                self.verify_atomic_fact(fact, verify_state)
                    .map_err(|verify_error| {
                        RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                            format!(
                                "failed to verify arg satisfy fn set parameter set: {}",
                                fact
                            ),
                            Some(RuntimeError::from(verify_error)),
                            default_line_file(),
                        )
                    })?;
            if verify_result.is_unknown() {
                return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                    format!("arg does not satisfy fn set parameter set: {}", fact),
                    None,
                    default_line_file(),
                ));
            }
        }

        let param_to_arg_map = ParamDefWithParamSet::param_defs_and_args_to_param_to_arg_map(
            &fn_set_with_dom.params_def_with_set,
            &args_as_obj,
        );
        for dom_fact in fn_set_with_dom.dom_facts.iter() {
            let instantiated_dom_fact =
                self.inst_or_and_chain_atomic_fact(dom_fact, &param_to_arg_map)
                    .map_err(|e| {
                        RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                            format!("failed to instantiate function domain fact: {}", e),
                            Some(e),
                            default_line_file(),
                        )
                    })?;
            let verify_result = self
                .verify_or_and_chain_atomic_fact(&instantiated_dom_fact, verify_state)
                .map_err(|verify_error| {
                    RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                        format!(
                            "failed to verify function domain fact:\n{}",
                            instantiated_dom_fact
                        ),
                        Some(RuntimeError::from(verify_error)),
                        default_line_file(),
                    )
                })?;
            if verify_result.is_unknown() {
                return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                    format!(
                        "failed to verify function domain fact:\n{}",
                        instantiated_dom_fact
                    ),
                    None,
                    default_line_file(),
                ));
            }
        }

        Ok(())
    }

    fn require_obj_in_r(
        &mut self,
        obj: &Obj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        let r_obj = Obj::StandardSet(StandardSet::R);
        let in_fact = InFact::new(obj.clone(), r_obj, default_line_file());
        let atomic_fact = AtomicFact::InFact(in_fact);
        let result = self.verify_atomic_fact(&atomic_fact, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                format!("obj {} is not in r", obj.to_string()),
                None,
                default_line_file(),
            ));
        }
        Ok(())
    }

    fn require_obj_in_z(
        &mut self,
        obj: &Obj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        let z_obj = Obj::StandardSet(StandardSet::Z);
        let in_fact = InFact::new(obj.clone(), z_obj, default_line_file());
        let atomic_fact = AtomicFact::InFact(in_fact);
        let result = self.verify_atomic_fact(&atomic_fact, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                format!("obj {} is not in z", obj.to_string()),
                None,
                default_line_file(),
            ));
        }
        Ok(())
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

        let zero = Obj::Number(Number::new("0".to_string()));
        let not_equal_fact =
            NotEqualFact::new((*div.right).clone(), zero, default_line_file());
        let atomic_fact = AtomicFact::NotEqualFact(not_equal_fact);
        let result = self.verify_atomic_fact(&atomic_fact, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                format!("divisor `{}` must be non-zero", div.right.to_string()),
                None,
                default_line_file(),
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
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&m.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&m.right, verify_state)?;
        self.require_obj_in_z(&m.left, verify_state)?;
        self.require_obj_in_z(&m.right, verify_state)?;
        let zero = Obj::Number(Number::new("0".to_string()));
        let not_equal_fact = NotEqualFact::new((*m.right).clone(), zero, default_line_file());
        let atomic_fact = AtomicFact::NotEqualFact(not_equal_fact);
        let result = self.verify_atomic_fact(&atomic_fact, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                format!("modulus `{}` must be non-zero", m.right.to_string()),
                None,
                default_line_file(),
            ));
        }
        Ok(())
    }

    fn verify_pow_well_defined(
        &mut self,
        pow: &Pow,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
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
                    default_line_file(),
                )),
                AtomicFact::InFact(InFact::new(
                    (*pow.exponent).clone(),
                    Obj::StandardSet(StandardSet::R),
                    default_line_file(),
                )),
            ],
            default_line_file(),
        ));

        let zero_base_and_positive_real_exponent = AndChainAtomicFact::AndFact(AndFact::new(
            vec![
                AtomicFact::EqualFact(EqualFact::new(
                    (*pow.base).clone(),
                    zero_obj.clone(),
                    default_line_file(),
                )),
                AtomicFact::InFact(InFact::new(
                    (*pow.exponent).clone(),
                    Obj::StandardSet(StandardSet::R),
                    default_line_file(),
                )),
                AtomicFact::GreaterFact(GreaterFact::new(
                    (*pow.exponent).clone(),
                    zero_obj.clone(),
                    default_line_file(),
                )),
            ],
            default_line_file(),
        ));

        let even_integer_exponent = AndChainAtomicFact::AndFact(AndFact::new(
            vec![
                AtomicFact::InFact(InFact::new(
                    (*pow.exponent).clone(),
                    Obj::StandardSet(StandardSet::Z),
                    default_line_file(),
                )),
                AtomicFact::EqualFact(EqualFact::new(
                    exponent_mod_two_obj,
                    zero_obj,
                    default_line_file(),
                )),
            ],
            default_line_file(),
        ));

        let exponent_is_positive_integer =
            AndChainAtomicFact::AtomicFact(AtomicFact::InFact(InFact::new(
                (*pow.exponent).clone(),
                Obj::StandardSet(StandardSet::NPos),
                default_line_file(),
            )));

        let pow_domain_or_fact = OrFact::new(
            vec![
                positive_base_and_real_exponent,
                zero_base_and_positive_real_exponent,
                even_integer_exponent,
                exponent_is_positive_integer,
            ],
            default_line_file(),
        );

        let result = self.verify_or_fact(&pow_domain_or_fact, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                format!("base and exponent do not satisfy the pow domain"),
                None,
                default_line_file(),
            ));
        }
        Ok(())
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
                let not_equal_atomic_fact = AtomicFact::NotEqualFact(NotEqualFact::new(
                    left_obj.clone(),
                    right_obj,
                    default_line_file(),
                ));
                let verify_result = self
                    .verify_atomic_fact(&not_equal_atomic_fact, &next_verify_state)
                    .map_err(|previous_error| {
                        RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                            format!(
                                "failed to verify list set elements are pairwise not equal: {}",
                                not_equal_atomic_fact
                            ),
                            Some(RuntimeError::from(previous_error)),
                            default_line_file(),
                        )
                    })?;
                if verify_result.is_unknown() {
                    return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                        format!("list set elements must be pairwise not equal, but it is not provable: {}", not_equal_atomic_fact),
                        None,
                        default_line_file(),
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
    ) -> Result<(), RuntimeError> {
        self.push_env();
        let result = self.verify_set_builder_well_defined_body(x, verify_state);
        self.pop_env();
        result
    }

    fn verify_set_builder_well_defined_body(
        &mut self,
        x: &SetBuilder,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        if let Err(e) = self.define_params_with_set(&ParamDefWithParamSet::new(
            vec![x.param.clone()],
            *x.param_set.clone(),
        )) {
            return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                format!(
                    "failed to verify well-defined of set builder {}",
                    x.to_string()
                ),
                Some(e),
                default_line_file(),
            ));
        }

        for fact in x.facts.iter() {
            if let Err(e) = self.verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                fact,
                verify_state,
            ) {
                return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                    format!(
                        "failed to verify well-defined of set builder {}",
                        x.to_string()
                    ),
                    Some(RuntimeError::from(e)),
                    default_line_file(),
                ));
            }
        }

        Ok(())
    }

    fn verify_fn_set_with_dom_well_defined(
        &mut self,
        x: &FnSetWithParams,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.push_env();
        let result = self.verify_fn_set_with_dom_well_defined_body(x, verify_state);
        self.pop_env();
        result
    }

    fn verify_fn_set_with_dom_well_defined_body(
        &mut self,
        x: &FnSetWithParams,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        if let Err(e) = self.verify_obj_well_defined_and_store_cache(&x.ret_set, verify_state) {
            return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                format!(
                    "failed to verify well-defined of fn set with dom {}",
                    x.to_string()
                ),
                Some(e.into()),
                default_line_file(),
            ));
        }

        for param_def_with_set in x.params_def_with_set.iter() {
            if let Err(e) = self.define_params_with_set(param_def_with_set) {
                return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                    format!(
                        "failed to verify well-defined of fn set with dom {}",
                        x.to_string()
                    ),
                    Some(e),
                    default_line_file(),
                ));
            }
        }

        for fact in x.dom_facts.iter() {
            if let Err(e) = self.verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                fact,
                verify_state,
            ) {
                return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                    format!(
                        "failed to verify well-defined of fn set with dom {}",
                        x.to_string()
                    ),
                    Some(RuntimeError::from(e)),
                    default_line_file(),
                ));
            }
        }

        Ok(())
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

        let is_cart_fact =
            AtomicFact::IsCartFact(IsCartFact::new((*x.set).clone(), default_line_file()));
        let result = self.verify_atomic_fact(&is_cart_fact, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                format!("set {} is not a cart", x.set.to_string()),
                None,
                default_line_file(),
            ));
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
            RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                format!("projection dimension {} is not a number", x.dim),
                None,
                default_line_file(),
            )
        })?;
        let projection_dimension_obj =
            Obj::Number(Number::new(projection_dimension_number.normalized_value));

        let projection_dimension_is_positive_integer_fact = AtomicFact::InFact(InFact::new(
            projection_dimension_obj.clone(),
            Obj::StandardSet(StandardSet::NPos),
            default_line_file(),
        ));
        let projection_dimension_is_positive_integer_result =
            self.verify_atomic_fact(&projection_dimension_is_positive_integer_fact, verify_state)?;
        if projection_dimension_is_positive_integer_result.is_unknown() {
            return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                format!(
                    "projection dimension {} is not a positive integer",
                    projection_dimension_obj
                ),
                None,
                default_line_file(),
            ));
        }

        let left_set_is_cart_fact =
            AtomicFact::IsCartFact(IsCartFact::new((*x.set).clone(), default_line_file()));
        let left_set_is_cart_result =
            self.verify_atomic_fact(&left_set_is_cart_fact, verify_state)?;
        if left_set_is_cart_result.is_unknown() {
            return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                format!("projection left side {} is not a cart", x.set),
                None,
                default_line_file(),
            ));
        }

        let left_set_cart_dim_obj = Obj::CartDim(CartDim::new((*x.set).clone()));

        let proj_index_not_larger_than_cart_dim = AtomicFact::LessEqualFact(LessEqualFact::new(
            projection_dimension_obj.clone(),
            left_set_cart_dim_obj.clone(),
            default_line_file(),
        ));
        let left_set_cart_dim_less_equal_projection_dimension_result =
            self.verify_atomic_fact(&proj_index_not_larger_than_cart_dim, verify_state)?;
        if left_set_cart_dim_less_equal_projection_dimension_result.is_unknown() {
            return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                format!(
                    "{} <= {} is unknown",
                    projection_dimension_obj, left_set_cart_dim_obj
                ),
                None,
                default_line_file(),
            ));
        }

        Ok(())
    }

    fn verify_dim_well_defined(
        &mut self,
        x: &TupleDim,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.arg, verify_state)?;

        let is_tuple_fact = AtomicFact::IsTupleFact(IsTupleFact::new(
            (*x.arg).clone(),
            default_line_file(),
        ));
        let result = self.verify_atomic_fact(&is_tuple_fact, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                format!(
                    "`{}` is unknown, `dim` object requires its argument to be a tuple",
                    is_tuple_fact
                ),
                None,
                default_line_file(),
            ));
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
        let is_finite_set_fact = AtomicFact::IsFiniteSetFact(IsFiniteSetFact::new(
            (*x.set).clone(),
            default_line_file(),
        ));
        let result = self.verify_atomic_fact(&is_finite_set_fact, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                format!("set {} is not a finite set", x.set.to_string()),
                None,
                default_line_file(),
            ));
        }
        Ok(())
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
        Ok(())
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
        unimplemented!()
    }

    fn verify_obj_at_index_well_defined(
        &mut self,
        x: &ObjAtIndex,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.obj, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.index, verify_state)?;

        let index_calculated_number = self.resolve_obj_to_number(&x.index).ok_or_else(|| {
            RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                format!("index {} is not a number", x.index.to_string()),
                None,
                default_line_file(),
            )
        })?;
        let index_calculated_obj =
            Obj::Number(Number::new(index_calculated_number.normalized_value));

        let index_is_positive_integer_in_z_pos_fact = AtomicFact::InFact(InFact::new(
            index_calculated_obj.clone(),
            Obj::StandardSet(StandardSet::NPos),
            default_line_file(),
        ));
        let index_is_positive_integer_result =
            self.verify_atomic_fact(&index_is_positive_integer_in_z_pos_fact, verify_state)?;
        if index_is_positive_integer_result.is_unknown() {
            return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                format!("index {} is not a positive integer", index_calculated_obj),
                None,
                default_line_file(),
            ));
        }

        let target_obj_is_tuple_fact = AtomicFact::IsTupleFact(IsTupleFact::new(
            (*x.obj).clone(),
            default_line_file(),
        ));
        let target_obj_is_tuple_result =
            self.verify_atomic_fact(&target_obj_is_tuple_fact, verify_state)?;
        if target_obj_is_tuple_result.is_unknown() {
            return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                format!("index target {} is not a tuple", x.obj),
                None,
                default_line_file(),
            ));
        }

        let target_tuple_dim_obj = Obj::TupleDim(TupleDim::new((*x.obj).clone()));
        let index_not_larger_than_tuple_dim_fact = AtomicFact::LessEqualFact(LessEqualFact::new(
            index_calculated_obj.clone(),
            target_tuple_dim_obj.clone(),
            default_line_file(),
        ));
        let index_not_larger_than_tuple_dim_result =
            self.verify_atomic_fact(&index_not_larger_than_tuple_dim_fact, verify_state)?;
        if index_not_larger_than_tuple_dim_result.is_unknown() {
            return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                format!(
                    "{} <= {} is unknown",
                    index_calculated_obj, target_tuple_dim_obj
                ),
                None,
                default_line_file(),
            ));
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
            ParamType::Obj(obj) => self.verify_obj_well_defined_and_store_cache(obj, verify_state),
            ParamType::Family(family) => {
                return self.verify_param_type_family_well_defined(
                    family,
                    verify_state,
                )
            }
            ParamType::Struct(struct_ty) => {
                return self.verify_param_type_struct_well_defined(
                    struct_ty,
                    verify_state,
                )
            }
        }
    }

    fn verify_param_type_family_well_defined(
        &mut self,
        family_param_type: &FamilyParamType,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        let family_name = family_param_type.name.to_string();
        let def = match self.get_cloned_family_definition_by_name(&family_name) {
            Some(d) => d,
            None => {
                return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                    format!("family `{}` is not defined", family_name),
                    None,
                    default_line_file(),
                ));
            }
        };

        let expected_count = ParamDefWithParamTypeTuple::number_of_params(&def.params_def_with_type);
        if family_param_type.params.len() != expected_count {
            return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                format!(
                    "family `{}` expects {} parameter(s), got {}",
                    family_name,
                    expected_count,
                    family_param_type.params.len()
                ),
                None,
                default_line_file(),
            ));
        }

        for arg in family_param_type.params.iter() {
            self.verify_obj_well_defined_and_store_cache(arg, verify_state)?;
        }

        let _: InferResult = self
            .verify_args_satisfy_param_def_flat_types(
                &def.params_def_with_type,
                &family_param_type.params,
                verify_state,
            )
            .map_err(|runtime_error| {
                RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                    format!(
                        "failed to verify family `{}` arguments satisfy parameter types",
                        family_name
                    ),
                    Some(runtime_error),
                    default_line_file(),
                )
            })?;

        let param_to_arg_map = ParamDefWithParamTypeTuple::param_defs_and_args_to_param_to_arg_map(
            &def.params_def_with_type,
            &family_param_type.params,
        );

        for dom_fact in def.dom_facts.iter() {
            let instantiated_dom_fact =
                self.inst_or_and_chain_atomic_fact(dom_fact, &param_to_arg_map)
                    .map_err(|e| {
                        RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                            format!("failed to instantiate family `{}` domain fact: {}", family_name, e),
                            Some(e),
                            default_line_file(),
                        )
                    })?;
            let verify_result = self
                .verify_or_and_chain_atomic_fact(&instantiated_dom_fact, verify_state)
                .map_err(|verify_error| {
                    RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                        format!(
                            "failed to verify family `{}` domain fact:\n{}",
                            family_name, instantiated_dom_fact
                        ),
                        Some(RuntimeError::from(verify_error)),
                        default_line_file(),
                    )
                })?;
            if verify_result.is_unknown() {
                return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                    format!(
                        "failed to verify family `{}` domain fact:\n{}",
                        family_name, instantiated_dom_fact
                    ),
                    None,
                    default_line_file(),
                ));
            }
        }

        let instantiated_equal_to = self.inst_obj(&def.equal_to, &param_to_arg_map).map_err(
            |e| {
                RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                    format!("failed to instantiate family `{}` member set: {}", family_name, e),
                    Some(e),
                    default_line_file(),
                )
            },
        )?;
        self.verify_obj_well_defined_and_store_cache(&instantiated_equal_to, verify_state)?;

        Ok(())
    }

    fn verify_param_type_struct_well_defined(
        &mut self,
        struct_ty: &StructParamType,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        let struct_name = struct_ty.name.to_string();
        let def = match self.get_cloned_definition_of_struct(&struct_name) {
            Some(d) => d,
            None => {
                return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                    format!("struct `{}` is not defined", struct_name),
                    None,
                    default_line_file(),
                ));
            }
        };

        let expected_count = ParamDefWithStructFieldTypeTuple::number_of_params(&def.param_defs);
        if struct_ty.args.len() != expected_count {
            return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                format!(
                    "struct `{}` expects {} parameter(s), got {}",
                    struct_name,
                    expected_count,
                    struct_ty.args.len()
                ),
                None,
                default_line_file(),
            ));
        }

        for arg in struct_ty.args.iter() {
            self.verify_obj_well_defined_and_store_cache(arg, verify_state)?;
        }

        let param_defs_pt =
            ParamDefWithStructFieldTypeTuple::to_param_defs_with_param_type(&def.param_defs);
        let _: InferResult = self
            .verify_args_satisfy_param_def_flat_types(
                &param_defs_pt,
                &struct_ty.args,
                verify_state,
            )
            .map_err(|runtime_error| {
                RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                    format!(
                        "failed to verify struct `{}` arguments satisfy parameter types",
                        struct_name
                    ),
                    Some(runtime_error),
                    default_line_file(),
                )
            })?;

        let param_to_arg_map = ParamDefWithStructFieldTypeTuple::param_defs_and_args_to_param_to_arg_map(
            &def.param_defs,
            &struct_ty.args,
        );

        for dom_fact in def.dom_facts.iter() {
            let instantiated_dom_fact =
                self.inst_or_and_chain_atomic_fact(dom_fact, &param_to_arg_map)
                    .map_err(|e| {
                        RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                            format!(
                                "failed to instantiate struct `{}` domain fact: {}",
                                struct_name, e
                            ),
                            Some(e),
                            default_line_file(),
                        )
                    })?;
            let verify_result = self
                .verify_or_and_chain_atomic_fact(&instantiated_dom_fact, verify_state)
                .map_err(|verify_error| {
                    RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                        format!(
                            "failed to verify struct `{}` domain fact:\n{}",
                            struct_name, instantiated_dom_fact
                        ),
                        Some(RuntimeError::from(verify_error)),
                        default_line_file(),
                    )
                })?;
            if verify_result.is_unknown() {
                return Err(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                    format!(
                        "failed to verify struct `{}` domain fact:\n{}",
                        struct_name, instantiated_dom_fact
                    ),
                    None,
                    default_line_file(),
                ));
            }
        }

        Ok(())
    }
}
