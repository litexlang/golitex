use crate::prelude::*;

impl Runtime {
    pub(in crate::verify) fn verify_sum_obj_well_defined(
        &mut self,
        x: &Sum,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.start, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.end, verify_state)?;
        self.require_obj_in_z(&x.start, verify_state)?;
        self.require_obj_in_z(&x.end, verify_state)?;
        // A finite range sum is only well-defined on a nonempty integer interval.
        // Example: `sum(1, 3, fn(i Z) Z {i})` is valid, but `sum(m, m - 1, f)` is not.
        self.require_less_equal_verified(
            &x.start,
            &x.end,
            verify_state,
            "sum: cannot verify start <= end for the summation range".to_string(),
        )?;
        self.verify_obj_well_defined_and_store_cache(&x.func, verify_state)?;
        self.verify_iterated_op_summand_under_integer_index_interval(
            &x.func,
            x.start.as_ref(),
            x.end.as_ref(),
            verify_state,
            "sum",
        )
    }

    pub(in crate::verify) fn verify_finite_set_sum_obj_well_defined(
        &mut self,
        x: &SumOfFiniteSet,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.set, verify_state)?;
        let finite_fact = IsFiniteSetFact::new((*x.set).clone(), default_line_file()).into();
        let finite_result = self.verify_atomic_fact(&finite_fact, verify_state)?;
        if finite_result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "finite_set_sum: set {} is not a finite set",
                    x.set
                )),
            )));
        }
        self.verify_obj_well_defined_and_store_cache(&x.func, verify_state)?;
        if let Obj::ListSet(list_set) = x.set.as_ref() {
            return self.verify_finite_set_sum_list_summand_well_defined(
                list_set,
                x.func.as_ref(),
                verify_state,
            );
        }
        if let Obj::ClosedRange(range) = x.set.as_ref() {
            let range_sum = Sum::new(
                range.start.as_ref().clone(),
                range.end.as_ref().clone(),
                x.func.as_ref().clone(),
            );
            return self.verify_sum_obj_well_defined(&range_sum, verify_state);
        }
        self.verify_finite_set_iterand_has_exact_domain("finite_set_sum", &x.func, &x.set)
            .map_err(|e| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!(
                            "finite_set_sum: cannot verify that {} is defined on {}",
                            x.func, x.set
                        ),
                        e,
                    ),
                ))
            })
    }

    fn verify_finite_set_iterand_has_exact_domain(
        &self,
        operation: &str,
        function: &Obj,
        set: &Obj,
    ) -> Result<(), RuntimeError> {
        let Some(body) = self.get_fn_range_function_body(function) else {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{}: {} must be a unary function with a known function set",
                    operation, function
                )),
            )));
        };
        if body.params_def_with_set.number_of_params() != 1 || !body.dom_facts.is_empty() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{}: {} must have domain {} exactly; pass an explicit restriction such as fn(x {}) T {{{}(x)}}",
                    operation, function, set, set, function
                )),
            )));
        }
        let Some(domain) = body.params_def_with_set.first() else {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{}: {} must have domain {} exactly",
                    operation, function, set
                )),
            )));
        };
        if domain.set_obj().to_string() != set.to_string() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{}: {} must have domain {} exactly; pass an explicit restriction such as fn(x {}) T {{{}(x)}}",
                    operation, function, set, set, function
                )),
            )));
        }
        Ok(())
    }

    pub(in crate::verify) fn verify_finite_set_sum_list_summand_well_defined(
        &mut self,
        list_set: &ListSet,
        func: &Obj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        let Some(body) = self.get_fn_range_function_body(func) else {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "finite_set_sum: summand must be a unary function; got {}",
                    func
                )),
            )));
        };
        if ParamGroupWithSet::number_of_params(&body.params_def_with_set) != 1 {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(
                    "finite_set_sum: summand must be unary (one parameter)".to_string(),
                ),
            )));
        }
        for element in list_set.list.iter() {
            let application = self.finite_set_sum_application_obj(func, element.as_ref())?;
            self.verify_obj_well_defined_and_store_cache(&application, verify_state)
                .map_err(|e| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!(
                                "finite_set_sum: summand {} is not defined at {}",
                                func, element
                            ),
                            e,
                        ),
                    ))
                })?;
        }
        Ok(())
    }

    pub(in crate::verify) fn finite_set_sum_application_obj(
        &self,
        func: &Obj,
        arg: &Obj,
    ) -> Result<Obj, RuntimeError> {
        if let Obj::FnObj(fo) = func {
            if !fo.body.is_empty() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "finite_set_sum: expected a bare function, not a function application {}",
                        func
                    )),
                )));
            }
            return Ok(FnObj::new((*fo.head).clone(), vec![vec![Box::new(arg.clone())]]).into());
        }
        let Some(head) = FnObjHead::from_callable_obj(func.clone()) else {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "finite_set_sum: summand must be callable; got {}",
                    func
                )),
            )));
        };
        Ok(FnObj::new(head, vec![vec![Box::new(arg.clone())]]).into())
    }

    pub(in crate::verify) fn verify_finite_set_product_obj_well_defined(
        &mut self,
        x: &ProductOfFiniteSet,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.set, verify_state)?;
        let finite_fact = IsFiniteSetFact::new((*x.set).clone(), default_line_file()).into();
        let finite_result = self.verify_atomic_fact(&finite_fact, verify_state)?;
        if finite_result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "finite_set_product: set {} is not a finite set",
                    x.set
                )),
            )));
        }
        self.verify_obj_well_defined_and_store_cache(&x.func, verify_state)?;
        if let Obj::ListSet(list_set) = x.set.as_ref() {
            return self.verify_finite_set_product_list_factor_well_defined(
                list_set,
                x.func.as_ref(),
                verify_state,
            );
        }
        if let Obj::ClosedRange(range) = x.set.as_ref() {
            let range_product = Product::new(
                range.start.as_ref().clone(),
                range.end.as_ref().clone(),
                x.func.as_ref().clone(),
            );
            return self.verify_product_obj_well_defined(&range_product, verify_state);
        }
        self.verify_finite_set_iterand_has_exact_domain("finite_set_product", &x.func, &x.set)
            .map_err(|e| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!(
                            "finite_set_product: cannot verify that {} is defined on {}",
                            x.func, x.set
                        ),
                        e,
                    ),
                ))
            })
    }

    pub(in crate::verify) fn verify_finite_set_product_list_factor_well_defined(
        &mut self,
        list_set: &ListSet,
        func: &Obj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        let Some(body) = self.get_fn_range_function_body(func) else {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "finite_set_product: factor must be a unary function; got {}",
                    func
                )),
            )));
        };
        if ParamGroupWithSet::number_of_params(&body.params_def_with_set) != 1 {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(
                    "finite_set_product: factor must be unary (one parameter)".to_string(),
                ),
            )));
        }
        for element in list_set.list.iter() {
            let application = self.finite_set_product_application_obj(func, element.as_ref())?;
            self.verify_obj_well_defined_and_store_cache(&application, verify_state)
                .map_err(|e| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!(
                                "finite_set_product: factor {} is not defined at {}",
                                func, element
                            ),
                            e,
                        ),
                    ))
                })?;
        }
        Ok(())
    }

    pub(in crate::verify) fn finite_set_product_application_obj(
        &self,
        func: &Obj,
        arg: &Obj,
    ) -> Result<Obj, RuntimeError> {
        if let Obj::FnObj(fo) = func {
            if !fo.body.is_empty() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "finite_set_product: expected a bare function, not a function application {}",
                        func
                    )),
                )));
            }
            return Ok(FnObj::new((*fo.head).clone(), vec![vec![Box::new(arg.clone())]]).into());
        }
        let Some(head) = FnObjHead::from_callable_obj(func.clone()) else {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "finite_set_product: factor must be callable; got {}",
                    func
                )),
            )));
        };
        Ok(FnObj::new(head, vec![vec![Box::new(arg.clone())]]).into())
    }

    pub(in crate::verify) fn verify_product_obj_well_defined(
        &mut self,
        x: &Product,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.start, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.end, verify_state)?;
        self.require_obj_in_z(&x.start, verify_state)?;
        self.require_obj_in_z(&x.end, verify_state)?;
        // A finite range product is only well-defined on a nonempty integer interval.
        // Example: `product(1, 3, fn(i Z) Z {i})` is valid, but `product(m, m - 1, f)` is not.
        self.require_less_equal_verified(
            &x.start,
            &x.end,
            verify_state,
            "product: cannot verify start <= end for the product range".to_string(),
        )?;
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
    pub(in crate::verify) fn unary_param_set_from_params_def(
        params_def: &[ParamGroupWithSet],
        pname: &str,
    ) -> Option<Obj> {
        for g in params_def {
            if g.params.iter().any(|n| n == pname) {
                return Some(g.set_obj().clone());
            }
        }
        None
    }

    /// For a closed range `[a,b]` with explicit integer endpoints, require each integer in the range
    /// to be in the index parameter's declared set (e.g. `Z_neg` disallows 1,2,3 in `1..3`).
    pub(in crate::verify) fn verify_closed_range_each_integer_satisfies_unary_param_set(
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

    pub(in crate::verify) fn verify_iterated_op_summand_with_stored_fn_set_body(
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
            let k = obj_for_bound_param_in_scope(pname, ParamObjType::FnSet);
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

    pub(in crate::verify) fn verify_iterated_op_summand_under_integer_index_interval(
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
            let Some(fs_body) = self.get_object_in_fn_set(&function_name_obj) else {
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
        if let Some(fs_body) = self.get_cloned_object_in_fn_set(func) {
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

    pub(in crate::verify) fn summand_as_unary_anonymous_fn(obj: &Obj) -> Option<&AnonymousFn> {
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

    pub(in crate::verify) fn verify_unary_iterated_anonymous_in_interval(
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
            let k = obj_for_bound_param_in_scope(pname, ParamObjType::FnSet);
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

    pub(in crate::verify) fn verify_range_well_defined(
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

    pub(in crate::verify) fn verify_closed_range_well_defined(
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
}
