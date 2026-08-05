use crate::prelude::*;

impl Runtime {
    /// Mathematical contract: `sum(a,b,f)` requires well-defined integer
    /// endpoints with `a <= b` and a unary scalar-valued function defined at
    /// every integer of the closed interval.
    pub(in crate::verify) fn verify_sum_obj_well_defined(
        &mut self,
        x: &Sum,
        verify_state: &UseContextVerifyState,
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
        self.verify_iterated_function_has_scalar_return_set("sum", &x.func, verify_state)?;
        self.verify_iterated_op_summand_under_integer_index_interval(
            &x.func,
            x.start.as_ref(),
            x.end.as_ref(),
            verify_state,
            "sum",
        )
    }

    /// Mathematical contract: `finite_set_sum(S,f)` requires a well-defined
    /// finite set and a unary scalar-valued function defined on exactly `S`
    /// (or demonstrably at every member for an extensional literal).
    pub(in crate::verify) fn verify_finite_set_sum_obj_well_defined(
        &mut self,
        x: &SumOfFiniteSet,
        verify_state: &UseContextVerifyState,
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
        self.verify_iterated_function_has_scalar_return_set(
            "finite_set_sum",
            &x.func,
            verify_state,
        )?;
        if let Obj::ListSet(list_set) = x.set.as_ref() {
            return self.verify_finite_set_sum_list_summand_well_defined(
                list_set,
                x.func.as_ref(),
                verify_state,
            );
        }
        if let Obj::ClosedRange(range) = x.set.as_ref() {
            let empty_fact: AtomicFact =
                NotIsNonemptySetFact::new((*x.set).clone(), default_line_file()).into();
            if self
                .verify_atomic_fact(&empty_fact, verify_state)?
                .is_true()
            {
                return self.verify_empty_finite_set_aggregate_has_unary_iterand(
                    "finite_set_sum",
                    &x.func,
                );
            }
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
            })?;
        self.verify_symbolic_finite_set_anonymous_iterand_return(
            "finite_set_sum",
            x.func.as_ref(),
            verify_state,
        )
    }

    /// Mathematical contract: a symbolic finite-set aggregate accepts only a
    /// unary, unconditional function whose declared domain is syntactically
    /// the aggregate set; callers can construct an explicit restriction when
    /// starting from a function on a larger carrier.
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

    /// Mathematical contract: a sum or product combines scalar values, so its
    /// unary iterand must declare a return set contained in `C`.  For a
    /// dependent function set, the containment obligation is checked under
    /// the parameter memberships and domain assumptions of that function set.
    fn verify_iterated_function_has_scalar_return_set(
        &mut self,
        operation: &str,
        function: &Obj,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        let Some(mut body) = self.get_fn_range_function_body(function) else {
            // The operation-specific callable/domain check reports a more
            // precise diagnostic when the object has no known function set.
            return Ok(());
        };
        if body.params_def_with_set.number_of_params() != 1 {
            return Ok(());
        }

        let bindings = body.params_def_with_set.collect_param_bindings();
        let rename_map =
            self.visible_binding_conflict_rename_map(&bindings, ParamObjType::FnSet)?;
        if !rename_map.is_empty() {
            body = self.alpha_rename_fn_set_body(&body, &rename_map)?;
        }

        self.run_in_local_env(|rt| {
            for param in body.params_def_with_set.iter() {
                rt.define_params_with_set_in_scope(param, ParamObjType::FnSet)?;
            }
            for domain_fact in body.dom_facts.iter() {
                rt.verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                    domain_fact,
                    verify_state,
                )?;
            }
            rt.verify_obj_well_defined_and_store_cache(&body.ret_set, verify_state)?;

            let scalar_return_fact: AtomicFact = SubsetFact::new(
                (*body.ret_set).clone(),
                StandardSet::C.into(),
                default_line_file(),
            )
            .into();
            if rt
                .verify_atomic_fact(&scalar_return_fact, verify_state)?
                .is_unknown()
            {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "{operation}: iterand return set {} is not verified to be a subset of C",
                        body.ret_set
                    )),
                )));
            }
            Ok(())
        })
    }

    /// Mathematical contract: an aggregate over a provably empty finite set
    /// never evaluates its iterand, but the aggregate syntax still requires a
    /// unary callable with a known function-set signature.
    fn verify_empty_finite_set_aggregate_has_unary_iterand(
        &self,
        operation: &str,
        function: &Obj,
    ) -> Result<(), RuntimeError> {
        let Some(body) = self.get_fn_range_function_body(function) else {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{operation}: iterand must be a unary function with a known function set"
                )),
            )));
        };
        if body.params_def_with_set.number_of_params() != 1 {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{operation}: iterand must be unary (one parameter)"
                )),
            )));
        }
        Ok(())
    }

    /// Mathematical contract: over an extensional finite set, the summand is
    /// unary, any anonymous body satisfies its return carrier, and each
    /// concrete application is well-defined.
    pub(in crate::verify) fn verify_finite_set_sum_list_summand_well_defined(
        &mut self,
        list_set: &ListSet,
        func: &Obj,
        verify_state: &UseContextVerifyState,
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
        self.verify_finite_list_anonymous_iterand_return(
            "finite_set_sum",
            list_set,
            func,
            verify_state,
        )?;
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

    /// Mathematical contract: `finite_set_product(S,f)` requires a
    /// well-defined finite set and a unary scalar-valued function defined on
    /// exactly `S` (or demonstrably at every extensional member).
    pub(in crate::verify) fn verify_finite_set_product_obj_well_defined(
        &mut self,
        x: &ProductOfFiniteSet,
        verify_state: &UseContextVerifyState,
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
        self.verify_iterated_function_has_scalar_return_set(
            "finite_set_product",
            &x.func,
            verify_state,
        )?;
        if let Obj::ListSet(list_set) = x.set.as_ref() {
            return self.verify_finite_set_product_list_factor_well_defined(
                list_set,
                x.func.as_ref(),
                verify_state,
            );
        }
        if let Obj::ClosedRange(range) = x.set.as_ref() {
            let empty_fact: AtomicFact =
                NotIsNonemptySetFact::new((*x.set).clone(), default_line_file()).into();
            if self
                .verify_atomic_fact(&empty_fact, verify_state)?
                .is_true()
            {
                return self.verify_empty_finite_set_aggregate_has_unary_iterand(
                    "finite_set_product",
                    &x.func,
                );
            }
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
            })?;
        self.verify_symbolic_finite_set_anonymous_iterand_return(
            "finite_set_product",
            x.func.as_ref(),
            verify_state,
        )
    }

    /// Mathematical contract: over an extensional finite set, the factor is
    /// unary, any anonymous body satisfies its return carrier, and each
    /// concrete application is well-defined.
    pub(in crate::verify) fn verify_finite_set_product_list_factor_well_defined(
        &mut self,
        list_set: &ListSet,
        func: &Obj,
        verify_state: &UseContextVerifyState,
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
        self.verify_finite_list_anonymous_iterand_return(
            "finite_set_product",
            list_set,
            func,
            verify_state,
        )?;
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

    /// Mathematical contract: `product(a,b,f)` requires well-defined integer
    /// endpoints with `a <= b` and a unary scalar-valued function defined at
    /// every integer of the closed interval.
    pub(in crate::verify) fn verify_product_obj_well_defined(
        &mut self,
        x: &Product,
        verify_state: &UseContextVerifyState,
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
        self.verify_iterated_function_has_scalar_return_set("product", &x.func, verify_state)?;
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
            if g.params.iter().any(|n| n.name() == pname) {
                return Some(g.set_obj().clone());
            }
        }
        None
    }

    /// Mathematical contract: every integer of the requested closed interval
    /// must lie in the iterand's declared parameter carrier. Example: a `N`
    /// iterand accepts `sum(m,n,f)` only when the nonnegative lower endpoint is
    /// provable.
    pub(in crate::verify) fn verify_closed_range_each_integer_satisfies_unary_param_set(
        &mut self,
        start: &Obj,
        end: &Obj,
        param_set: &Obj,
        verify_state: &UseContextVerifyState,
        op: &str,
    ) -> Result<(), RuntimeError> {
        if let (Some(a_num), Some(b_num)) = (
            self.resolve_obj_to_number(start),
            self.resolve_obj_to_number(end),
        ) {
            let as_ = a_num.normalized_value.trim();
            let bs = b_num.normalized_value.trim();
            if is_number_string_literally_integer_without_dot(as_.to_string())
                && is_number_string_literally_integer_without_dot(bs.to_string())
            {
                if let (Ok(ai), Ok(bi)) = (as_.parse::<i128>(), bs.parse::<i128>()) {
                    for k in ai..=bi {
                        let k_obj: Obj = Number::new(k.to_string()).into();
                        let in_fact =
                            InFact::new(k_obj, param_set.clone(), default_line_file()).into();
                        let result = self.verify_atomic_fact(&in_fact, verify_state)?;
                        if result.is_unknown() {
                            return Err(RuntimeError::from(WellDefinedRuntimeError(
                                RuntimeErrorStruct::new_with_just_msg(format!(
                            "{op}: each integer in the closed range from {} to {} must belong to the index parameter's type; not satisfied at index {}",
                            start, end, k
                        )),
                            )));
                        }
                    }
                    return Ok(());
                }
            }
        }

        let endpoint_requirements: Vec<(&Obj, StandardSet)> = match param_set {
            Obj::StandardSet(StandardSet::Z)
            | Obj::StandardSet(StandardSet::Q)
            | Obj::StandardSet(StandardSet::R)
            | Obj::StandardSet(StandardSet::C) => return Ok(()),
            Obj::StandardSet(StandardSet::N) => vec![(start, StandardSet::N)],
            Obj::StandardSet(StandardSet::NPos)
            | Obj::StandardSet(StandardSet::QPos)
            | Obj::StandardSet(StandardSet::RPos) => vec![(start, StandardSet::NPos)],
            Obj::StandardSet(StandardSet::ZNeg)
            | Obj::StandardSet(StandardSet::QNeg)
            | Obj::StandardSet(StandardSet::RNeg) => vec![(end, StandardSet::ZNeg)],
            Obj::StandardSet(StandardSet::ZNz)
            | Obj::StandardSet(StandardSet::QNz)
            | Obj::StandardSet(StandardSet::RNz) => {
                vec![(start, StandardSet::NPos), (end, StandardSet::ZNeg)]
            }
            _ => Vec::new(),
        };
        for (endpoint, required_set) in endpoint_requirements {
            let fact: AtomicFact =
                InFact::new(endpoint.clone(), required_set.into(), default_line_file()).into();
            if self.verify_atomic_fact(&fact, verify_state)?.is_true() {
                return Ok(());
            }
        }

        let interval: Obj = ClosedRange::new(start.clone(), end.clone()).into();
        let subset_fact: AtomicFact =
            SubsetFact::new(interval, param_set.clone(), default_line_file()).into();
        if self
            .verify_atomic_fact(&subset_fact, verify_state)?
            .is_true()
        {
            return Ok(());
        }

        Err(RuntimeError::from(WellDefinedRuntimeError(
            RuntimeErrorStruct::new_with_just_msg(format!(
                "{op}: cannot verify that every integer from {start} to {end} belongs to the iterand domain {param_set}"
            )),
        )))
    }

    /// Mathematical contract: a stored range iterand is unary, covers the
    /// complete integer interval, satisfies every declared domain predicate
    /// there, and has a meaningful return carrier under those assumptions.
    pub(in crate::verify) fn verify_iterated_op_summand_with_stored_fn_set_body(
        &mut self,
        fs_body: FnSetBody,
        start: &Obj,
        end: &Obj,
        verify_state: &UseContextVerifyState,
        op: &str,
    ) -> Result<(), RuntimeError> {
        if ParamGroupWithSet::number_of_params(&fs_body.params_def_with_set) != 1 {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{op}: the function in the function set must be unary (one index)"
                )),
            )));
        }
        let param_bindings = fs_body.params_def_with_set.collect_param_bindings();
        let param_binding = param_bindings[0].clone();
        let Some(param_set_for_index) = Self::unary_param_set_from_params_def(
            &fs_body.params_def_with_set,
            param_binding.name(),
        ) else {
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
            let k = obj_for_bound_param_in_scope(param_binding, ParamObjType::FnSet);
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
                let result = rt
                    .verify_or_and_chain_atomic_fact(df, verify_state)
                    .map_err(|e| {
                        RuntimeError::from(WellDefinedRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_cause(
                                format!("{op}: function set domain check failed"),
                                e,
                            ),
                        ))
                    })?;
                if !result.is_true() {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "{op}: cannot verify function domain condition {df} on the whole integer range"
                        )),
                    )));
                }
                rt.store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                    df.clone(),
                )
                .map_err(|e| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!("{op}: could not store verified function domain condition"),
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

    /// Mathematical contract: a range iterand must resolve to either a unary
    /// anonymous function or a defined unary function whose domain covers the
    /// complete integer interval.
    pub(in crate::verify) fn verify_iterated_op_summand_under_integer_index_interval(
        &mut self,
        func: &Obj,
        start: &Obj,
        end: &Obj,
        verify_state: &UseContextVerifyState,
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

    /// Mathematical contract: an anonymous range iterand is unary, its
    /// parameter carrier covers the interval, each domain condition holds
    /// throughout it, and its body is meaningful and belongs to the declared
    /// return set under those local assumptions.
    pub(in crate::verify) fn verify_unary_iterated_anonymous_in_interval(
        &mut self,
        af: &AnonymousFn,
        start: &Obj,
        end: &Obj,
        verify_state: &UseContextVerifyState,
        op: &str,
    ) -> Result<(), RuntimeError> {
        if ParamGroupWithSet::number_of_params(&af.body.params_def_with_set) != 1 {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{op}: summation/product index function must be unary (one parameter)"
                )),
            )));
        }
        let param_bindings = af.body.params_def_with_set.collect_param_bindings();
        let param_binding = param_bindings[0].clone();
        let Some(param_set_for_index) = Self::unary_param_set_from_params_def(
            &af.body.params_def_with_set,
            param_binding.name(),
        ) else {
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
            let k = obj_for_bound_param_in_scope(param_binding, ParamObjType::FnSet);
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
                let result = rt
                    .verify_or_and_chain_atomic_fact(df, verify_state)
                    .map_err(|e| {
                        RuntimeError::from(WellDefinedRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_cause(
                                format!("{op}: anonymous iterand domain check failed"),
                                e,
                            ),
                        ))
                    })?;
                if !result.is_true() {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "{op}: cannot verify anonymous iterand domain condition {df} on the whole integer range"
                        )),
                    )));
                }
                rt.store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                    df.clone(),
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
                })?;
            let return_membership: AtomicFact = InFact::new(
                (*af.equal_to).clone(),
                (*af.body.ret_set).clone(),
                default_line_file(),
            )
            .into();
            let return_result = rt.verify_atomic_fact(&return_membership, verify_state)?;
            if return_result.is_unknown() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "{op}: iterand body {} is not verified to belong to declared return set {}",
                        af.equal_to, af.body.ret_set
                    )),
                )));
            }
            Ok(())
        })
    }

    /// Mathematical contract: a half-open integer range is meaningful when
    /// both endpoints are well-defined integers; it may be empty.
    pub(in crate::verify) fn verify_range_well_defined(
        &mut self,
        x: &Range,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.start, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.end, verify_state)?;
        self.require_obj_in_z(&x.start, verify_state)?;
        self.require_obj_in_z(&x.end, verify_state)?;
        Ok(())
    }

    /// Mathematical contract: a closed integer range is meaningful when both
    /// endpoints are well-defined integers; it may be empty.
    pub(in crate::verify) fn verify_closed_range_well_defined(
        &mut self,
        x: &ClosedRange,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.start, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.end, verify_state)?;
        self.require_obj_in_z(&x.start, verify_state)?;
        self.require_obj_in_z(&x.end, verify_state)?;
        Ok(())
    }

    /// Mathematical contract: at every listed index, an anonymous aggregate
    /// body's instantiated value belongs to its instantiated return carrier.
    fn verify_finite_list_anonymous_iterand_return(
        &mut self,
        op: &str,
        list_set: &ListSet,
        func: &Obj,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        let Some(anonymous) = Self::summand_as_unary_anonymous_fn(func) else {
            return Ok(());
        };
        if list_set.list.is_empty() {
            return self.verify_symbolic_finite_set_anonymous_iterand_return(
                op,
                func,
                verify_state,
            );
        }
        for element in &list_set.list {
            let args = vec![element.as_ref().clone()];
            let substitutions = ParamGroupWithSet::param_defs_and_args_to_param_to_arg_map(
                &anonymous.body.params_def_with_set,
                &args,
            );
            let body = self.inst_obj(&anonymous.equal_to, &substitutions, ParamObjType::FnSet)?;
            let return_set =
                self.inst_obj(&anonymous.body.ret_set, &substitutions, ParamObjType::FnSet)?;
            let return_membership: AtomicFact =
                InFact::new(body.clone(), return_set.clone(), default_line_file()).into();
            let result = self.verify_atomic_fact(&return_membership, verify_state)?;
            if result.is_unknown() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "{op}: iterand body {body} is not verified to belong to declared return set {return_set} at {}",
                        element
                    )),
                )));
            }
        }
        Ok(())
    }

    /// Mathematical contract: for a symbolic or empty finite domain, check an
    /// anonymous aggregate body universally under its parameter membership,
    /// including the direct identity-function subset consequence.
    fn verify_symbolic_finite_set_anonymous_iterand_return(
        &mut self,
        op: &str,
        func: &Obj,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        let Some(anonymous) = Self::summand_as_unary_anonymous_fn(func) else {
            return Ok(());
        };
        self.run_in_local_env(|rt| {
            for param in anonymous.body.params_def_with_set.iter() {
                rt.define_params_with_set_in_scope(param, ParamObjType::FnSet)?;
            }
            let bindings = anonymous.body.params_def_with_set.collect_param_bindings();
            if let [binding] = bindings.as_slice() {
                if let Some(param_set) = Self::unary_param_set_from_params_def(
                    &anonymous.body.params_def_with_set,
                    binding.name(),
                ) {
                    if rt.verify_iterand_domain_is_contained_in_return_set(
                        &param_set,
                        anonymous.body.ret_set.as_ref(),
                        verify_state,
                    )? {
                        let param_obj = obj_for_bound_param_in_scope(binding, ParamObjType::FnSet);
                        let domain_membership: AtomicFact =
                            InFact::new(param_obj.clone(), param_set, default_line_file()).into();
                        if rt
                            .verify_atomic_fact(&domain_membership, verify_state)?
                            .is_true()
                        {
                            let return_membership: AtomicFact = InFact::new(
                                param_obj,
                                (*anonymous.body.ret_set).clone(),
                                default_line_file(),
                            )
                            .into();
                            rt.store_atomic_fact_without_well_defined_verified_and_infer(
                                return_membership,
                            )?;
                        }
                    }
                }
            }
            rt.verify_obj_well_defined_and_store_cache(&anonymous.equal_to, verify_state)?;
            let return_membership: AtomicFact = InFact::new(
                (*anonymous.equal_to).clone(),
                (*anonymous.body.ret_set).clone(),
                default_line_file(),
            )
            .into();
            if rt
                .verify_atomic_fact(&return_membership, verify_state)?
                .is_unknown()
            {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "{op}: iterand body {} is not verified to belong to declared return set {}",
                        anonymous.equal_to, anonymous.body.ret_set
                    )),
                )));
            }
            Ok(())
        })
    }

    /// Mathematical contract: prove that every element admitted by the
    /// iterand domain also belongs to its declared return set, using either a
    /// subset proof or sound structural reductions of the domain expression.
    fn verify_iterand_domain_is_contained_in_return_set(
        &mut self,
        domain: &Obj,
        return_set: &Obj,
        verify_state: &UseContextVerifyState,
    ) -> Result<bool, RuntimeError> {
        let subset_fact: AtomicFact =
            SubsetFact::new(domain.clone(), return_set.clone(), default_line_file()).into();
        if self
            .verify_atomic_fact(&subset_fact, verify_state)?
            .is_true()
        {
            return Ok(true);
        }

        match domain {
            Obj::StandardSet(domain_set) => {
                let Obj::StandardSet(return_standard_set) = return_set else {
                    return Ok(false);
                };
                Ok(Self::standard_set_is_subset_eq(
                    domain_set,
                    return_standard_set,
                ))
            }
            Obj::ListSet(list) => {
                for element in &list.list {
                    let membership: AtomicFact = InFact::new(
                        element.as_ref().clone(),
                        return_set.clone(),
                        default_line_file(),
                    )
                    .into();
                    if !self
                        .verify_atomic_fact(&membership, verify_state)?
                        .is_true()
                    {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Obj::Union(union) => {
                if !self.verify_iterand_domain_is_contained_in_return_set(
                    union.left.as_ref(),
                    return_set,
                    verify_state,
                )? {
                    return Ok(false);
                }
                self.verify_iterand_domain_is_contained_in_return_set(
                    union.right.as_ref(),
                    return_set,
                    verify_state,
                )
            }
            Obj::Intersect(intersect) => {
                if self.verify_iterand_domain_is_contained_in_return_set(
                    intersect.left.as_ref(),
                    return_set,
                    verify_state,
                )? {
                    return Ok(true);
                }
                self.verify_iterand_domain_is_contained_in_return_set(
                    intersect.right.as_ref(),
                    return_set,
                    verify_state,
                )
            }
            Obj::SetMinus(set_minus) => self.verify_iterand_domain_is_contained_in_return_set(
                set_minus.left.as_ref(),
                return_set,
                verify_state,
            ),
            Obj::SetDiff(set_diff) => {
                if !self.verify_iterand_domain_is_contained_in_return_set(
                    set_diff.left.as_ref(),
                    return_set,
                    verify_state,
                )? {
                    return Ok(false);
                }
                self.verify_iterand_domain_is_contained_in_return_set(
                    set_diff.right.as_ref(),
                    return_set,
                    verify_state,
                )
            }
            Obj::SetBuilder(builder) => self.verify_iterand_domain_is_contained_in_return_set(
                builder.param_set.as_ref(),
                return_set,
                verify_state,
            ),
            Obj::Range(_) | Obj::ClosedRange(_) => {
                let Obj::StandardSet(return_standard_set) = return_set else {
                    return Ok(false);
                };
                Ok(Self::standard_set_is_subset_eq(
                    &StandardSet::Z,
                    return_standard_set,
                ))
            }
            _ => Ok(false),
        }
    }
}
