use crate::prelude::*;

impl Runtime {
    pub(in crate::verify) fn verify_power_set_well_defined(
        &mut self,
        x: &PowerSet,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.set, verify_state)?;
        Ok(())
    }

    pub(in crate::verify) fn verify_general_cart_well_defined(
        &mut self,
        x: &GeneralCart,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.index_set, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.family_set, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.family_fn, verify_state)?;

        let index_is_set: Fact = IsSetFact::new((*x.index_set).clone(), default_line_file()).into();
        self.verify_fact_return_err_if_not_true(&index_is_set, verify_state)
            .map_err(|e| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!("failed to verify well-defined of {}", x),
                        e,
                    ),
                ))
            })?;

        let family_is_nonempty: Fact =
            IsNonemptySetFact::new((*x.family_set).clone(), default_line_file()).into();
        self.verify_fact_return_err_if_not_true(&family_is_nonempty, verify_state)
            .map_err(|e| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!("failed to verify well-defined of {}", x),
                        e,
                    ),
                ))
            })?;

        let family_fn_set: Obj = FnSet::new(
            vec![ParamGroupWithSet::new(
                vec!["x".to_string()],
                (*x.index_set).clone(),
            )],
            vec![],
            (*x.family_set).clone(),
        )?
        .into();
        let family_fn_type: Fact =
            InFact::new((*x.family_fn).clone(), family_fn_set, default_line_file()).into();
        self.verify_fact_return_err_if_not_true(&family_fn_type, verify_state)
            .map_err(|e| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!("failed to verify well-defined of {}", x),
                        e,
                    ),
                ))
            })?;

        Ok(())
    }

    pub(in crate::verify) fn verify_obj_at_index_well_defined(
        &mut self,
        x: &ObjAtIndex,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.obj, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.index, verify_state)?;

        let index_calculated_obj: Obj =
            if let Some(index_calculated_number) = self.resolve_obj_to_number(&x.index) {
                Number::new(index_calculated_number.normalized_value).into()
            } else {
                (*x.index).clone()
            };

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

        self.store_fn_obj_cart_return_facts_if_available(&x.obj, default_line_file())?;

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

    pub(in crate::verify) fn store_fn_obj_cart_return_facts_if_available(
        &mut self,
        obj: &Obj,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        let Obj::FnObj(fn_obj) = obj else {
            return Ok(());
        };
        let Some(ret_set) = self.fn_obj_return_set_after_application(fn_obj)? else {
            return Ok(());
        };
        let Obj::Cart(cart) = ret_set else {
            return Ok(());
        };
        if cart.args.len() < 2 {
            return Ok(());
        }

        self.store_tuple_obj_and_cart(
            &obj.to_string(),
            None,
            Some(cart.clone()),
            line_file.clone(),
        );

        let is_tuple_fact: AtomicFact = IsTupleFact::new(obj.clone(), line_file.clone()).into();
        self.store_atomic_fact_without_well_defined_verified_and_infer(is_tuple_fact)?;

        let tuple_dim_obj: Obj = TupleDim::new(obj.clone()).into();
        let cart_arg_count_obj: Obj = Number::new(cart.args.len().to_string()).into();
        let tuple_dim_fact: AtomicFact =
            EqualFact::new(tuple_dim_obj, cart_arg_count_obj, line_file.clone()).into();
        self.store_atomic_fact_without_well_defined_verified_and_infer(tuple_dim_fact)?;

        for (factor_index, factor) in cart.args.iter().enumerate() {
            let index = factor_index + 1;
            let index_obj: Obj = Number::new(index.to_string()).into();
            let index_bound_fact: AtomicFact = LessEqualFact::new(
                index_obj.clone(),
                TupleDim::new(obj.clone()).into(),
                line_file.clone(),
            )
            .into();
            self.store_atomic_fact_without_well_defined_verified_and_infer(index_bound_fact)?;

            let projected_obj: Obj = ObjAtIndex::new(obj.clone(), index_obj).into();
            let projected_in_factor_fact: AtomicFact =
                InFact::new(projected_obj, (**factor).clone(), line_file.clone()).into();
            self.store_atomic_fact_without_well_defined_verified_and_infer(
                projected_in_factor_fact,
            )?;
        }

        Ok(())
    }

    pub(crate) fn fn_obj_return_set_after_application(
        &self,
        fn_obj: &FnObj,
    ) -> Result<Option<Obj>, RuntimeError> {
        if fn_obj.body.is_empty() {
            return Ok(None);
        }

        let mut space = match fn_obj.head.as_ref() {
            FnObjHead::AnonymousFnLiteral(a) => FnSetSpace::Anon((**a).clone()),
            FnObjHead::FiniteSeqListObj(_) => return Ok(None),
            _ => {
                let function_name_obj: Obj = (*fn_obj.head).clone().into();
                let Some(body) = self.get_object_in_fn_set_or_restrict(&function_name_obj) else {
                    return Ok(None);
                };
                FnSetSpace::Set(FnSet::from_body(body.clone())?)
            }
        };

        for i in 0..fn_obj.body.len() {
            let ret_set = space.ret_set_obj();
            if i == fn_obj.body.len() - 1 {
                return Ok(Some(ret_set));
            }
            space = self.fn_set_space_from_return_set_obj(ret_set)?;
        }

        Ok(None)
    }

    pub(crate) fn fn_set_space_from_return_set_obj(
        &self,
        return_set: Obj,
    ) -> Result<FnSetSpace, RuntimeError> {
        let original_return_set = return_set.clone();
        let mut candidates = vec![return_set];
        let mut seen = Vec::new();
        let mut next_index = 0;

        while next_index < candidates.len() {
            let candidate = candidates[next_index].clone();
            next_index += 1;
            if seen.contains(&candidate.to_string()) {
                continue;
            }
            seen.push(candidate.to_string());

            match &candidate {
                Obj::FnSet(fn_set) => return Ok(FnSetSpace::Set(fn_set.clone())),
                Obj::AnonymousFn(anonymous_fn) => {
                    return Ok(FnSetSpace::Anon(anonymous_fn.clone()));
                }
                Obj::SetBuilder(set_builder) => candidates.push(*set_builder.param_set.clone()),
                _ => {}
            }

            candidates.extend(self.get_all_obj_representatives_equal_to_given(&candidate));
        }

        FnSetSpace::from_ret_obj(original_return_set)
    }

    pub(in crate::verify) fn verify_q_pos_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    pub(in crate::verify) fn verify_r_pos_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    pub(in crate::verify) fn verify_q_neg_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    pub(in crate::verify) fn verify_z_neg_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    pub(in crate::verify) fn verify_r_neg_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    pub(in crate::verify) fn verify_q_nz_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    pub(in crate::verify) fn verify_z_nz_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    pub(in crate::verify) fn verify_r_nz_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }
}
