use crate::prelude::*;

impl Runtime {
    /// Mathematical contract: `union(A,B)` is meaningful when both operand
    /// expressions are well-defined set-theoretic objects.
    pub(in crate::verify) fn verify_union_well_defined(
        &mut self,
        x: &Union,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.right, verify_state)?;
        Ok(())
    }

    /// Mathematical contract: `intersect(A,B)` is meaningful when both
    /// operand expressions are well-defined set-theoretic objects.
    pub(in crate::verify) fn verify_intersect_well_defined(
        &mut self,
        x: &Intersect,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.right, verify_state)?;
        Ok(())
    }

    /// Mathematical contract: set subtraction is meaningful when both
    /// operand expressions are well-defined set-theoretic objects.
    pub(in crate::verify) fn verify_set_minus_well_defined(
        &mut self,
        x: &SetMinus,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.right, verify_state)?;
        Ok(())
    }

    /// Mathematical contract: symmetric set difference is meaningful when
    /// both operand expressions are well-defined set-theoretic objects.
    pub(in crate::verify) fn verify_set_diff_well_defined(
        &mut self,
        x: &SetDiff,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.right, verify_state)?;
        Ok(())
    }

    /// Mathematical contract: big union is meaningful when its family
    /// expression is well-defined.
    pub(in crate::verify) fn verify_big_union_well_defined(
        &mut self,
        x: &BigUnion,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.left, verify_state)?;
        Ok(())
    }

    /// Mathematical contract: big intersection is meaningful when its family
    /// expression is well-defined.
    pub(in crate::verify) fn verify_big_intersect_well_defined(
        &mut self,
        x: &BigIntersect,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.left, verify_state)?;
        Ok(())
    }

    /// Mathematical contract: a finite extensional literal is meaningful when
    /// every element is well-defined and the literal's entries are provably
    /// pairwise distinct, as required by Litex's canonical-list invariant.
    pub(in crate::verify) fn verify_list_set_well_defined(
        &mut self,
        x: &ListSet,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        for obj in &x.list {
            self.verify_obj_well_defined_and_store_cache(obj, verify_state)?;
        }

        let next_verify_state = verify_state.with_well_defined_already_verified();
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

    /// Mathematical contract: `{x in S: P(x)}` is meaningful when `S` is
    /// well-defined and each defining fact is meaningful under the local
    /// assumption `x in S` and all preceding defining facts.
    pub(in crate::verify) fn verify_set_builder_well_defined(
        &mut self,
        x: &SetBuilder,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        // Must use `ParamObjType::SetBuilder` here, not `define_params_with_set` (FnSet).
        // Parsed set-builder facts use SetBuilder-tagged bound vars; a mismatched tag means
        // e.g. `x $in N` is never found when checking `b ^ x`, so pow domain fails.
        // Run in local env so param binding and body facts do not leak into the outer scope.
        self.run_in_local_env(|rt| {
            if let Err(well_defined_error) = rt.verify_obj_well_defined_and_store_cache(
                &x.param_set,
                &UseContextVerifyState::new(0, false),
            ) {
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
            if let Err(e) = rt.store_parameter_binding(&x.param_binding, ParamObjType::SetBuilder) {
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
                obj_for_bound_param_in_scope(&x.param_binding, ParamObjType::SetBuilder),
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
                let result = match fact {
                    ExistBodyFact::AtomicFact(f) => rt
                        .verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                            &OrAndChainAtomicFact::AtomicFact(f.clone()),
                            verify_state,
                        ),
                    ExistBodyFact::AndFact(f) => rt
                        .verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                            &OrAndChainAtomicFact::AndFact(f.clone()),
                            verify_state,
                        ),
                    ExistBodyFact::ChainFact(f) => rt
                        .verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                            &OrAndChainAtomicFact::ChainFact(f.clone()),
                            verify_state,
                        ),
                    ExistBodyFact::OrFact(f) => rt
                        .verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                            &OrAndChainAtomicFact::OrFact(f.clone()),
                            verify_state,
                        ),
                    ExistBodyFact::InlineForall(f) => {
                        rt.verify_forall_fact_well_defined(f, verify_state)?;
                        rt.store_forall_fact_without_well_defined_verified_and_infer(f.clone())
                    }
                };
                if let Err(e) = result {
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

    /// Mathematical contract: a function set is meaningful when its dependent
    /// parameter carriers are meaningful in order, its domain facts are
    /// meaningful under those binders, and its return carrier is meaningful
    /// under the parameter and domain assumptions.
    pub(in crate::verify) fn verify_fn_set_well_defined(
        &mut self,
        x: &FnSet,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        let bindings = x.body.params_def_with_set.collect_param_bindings();
        let rename_map =
            self.visible_binding_conflict_rename_map(&bindings, ParamObjType::FnSet)?;
        if !rename_map.is_empty() {
            let renamed = self.alpha_rename_fn_set(x, &rename_map)?;
            return self.verify_fn_set_well_defined(&renamed, verify_state);
        }

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

    /// Mathematical contract: `fn(params) T {body}` is meaningful when its
    /// function-set signature is meaningful, `body` is meaningful under that
    /// local domain, and the verifier proves `body in T` for every admissible
    /// parameter assignment.
    pub(in crate::verify) fn verify_anonymous_fn_well_defined(
        &mut self,
        x: &AnonymousFn,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        let bindings = x.body.params_def_with_set.collect_param_bindings();
        let rename_map =
            self.visible_binding_conflict_rename_map(&bindings, ParamObjType::FnSet)?;
        if !rename_map.is_empty() {
            let renamed = self.alpha_rename_anonymous_fn(x, &rename_map)?;
            return self.verify_anonymous_fn_well_defined(&renamed, verify_state);
        }

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

            let return_value_result = rt.verify_value_in_declared_return_set(
                (*x.equal_to).clone(),
                (*x.body.ret_set).clone(),
                default_line_file(),
                verify_state,
            )?;
            let mut return_value_verified = !return_value_result.is_unknown();
            if !return_value_verified {
                for param_group in x.body.params_def_with_set.iter() {
                    let body_is_bound_param = param_group.params.iter().any(|binding| {
                        let param_obj =
                            obj_for_bound_param_in_scope(binding, ParamObjType::FnSet);
                        objs_equal_with_nested_binder_alpha_equivalence(
                            x.equal_to.as_ref(),
                            &param_obj,
                        )
                    });
                    if !body_is_bound_param {
                        continue;
                    }
                    let subset_fact: AtomicFact = SubsetFact::new(
                        param_group.set_obj().clone(),
                        (*x.body.ret_set).clone(),
                        default_line_file(),
                    )
                    .into();
                    if rt.verify_atomic_fact(&subset_fact, verify_state)?.is_true() {
                        return_value_verified = true;
                        break;
                    }
                }
            }
            if !return_value_verified {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "anonymous function body {} is not verified to belong to declared return set {}",
                        x.equal_to, x.body.ret_set
                    )),
                )));
            }

            Ok(())
        })
    }

    /// Mathematical contract: the primitive standard set `N+` is total.
    pub(in crate::verify) fn verify_n_pos_obj_well_defined(&mut self) -> Result<(), RuntimeError> {
        Ok(())
    }

    /// Mathematical contract: the primitive standard set `N` is total.
    pub(in crate::verify) fn verify_n_obj_well_defined(&mut self) -> Result<(), RuntimeError> {
        Ok(())
    }

    /// Mathematical contract: the primitive standard set `Q` is total.
    pub(in crate::verify) fn verify_q_obj_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    /// Mathematical contract: the primitive standard set `Z` is total.
    pub(in crate::verify) fn verify_z_obj_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    /// Mathematical contract: the primitive standard set `R` is total.
    pub(in crate::verify) fn verify_r_obj_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    /// Mathematical contract: the primitive standard set `C` is total.
    pub(in crate::verify) fn verify_c_obj_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    /// Mathematical contract: a finite Cartesian carrier is meaningful when
    /// every factor expression is well-defined.
    pub(in crate::verify) fn verify_cart_well_defined(
        &mut self,
        x: &Cart,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        for obj in &x.args {
            self.verify_obj_well_defined_and_store_cache(obj, verify_state)?;
        }
        Ok(())
    }

    /// Mathematical contract: `cart_dim(S)` is meaningful when `S` is a
    /// well-defined Cartesian-product carrier.
    pub(in crate::verify) fn verify_cart_dim_well_defined(
        &mut self,
        x: &CartDim,
        verify_state: &UseContextVerifyState,
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

    /// Mathematical contract: `proj(S,i)` requires a well-defined Cartesian
    /// carrier `S` and a positive integer `i <= cart_dim(S)`.
    pub(in crate::verify) fn verify_proj_well_defined(
        &mut self,
        x: &Proj,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.set, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.dim, verify_state)?;

        let projection_dimension_obj: Obj =
            if let Some(projection_dimension_number) = self.resolve_obj_to_number(&x.dim) {
                Number::new(projection_dimension_number.normalized_value).into()
            } else {
                (*x.dim).clone()
            };

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

    /// Mathematical contract: `tuple_dim(t)` is meaningful exactly for a
    /// well-defined object provably known to be a tuple.
    pub(in crate::verify) fn verify_dim_well_defined(
        &mut self,
        x: &TupleDim,
        verify_state: &UseContextVerifyState,
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

    /// Mathematical contract: a tuple literal is meaningful when every
    /// component is a well-defined object.
    pub(in crate::verify) fn verify_tuple_well_defined(
        &mut self,
        x: &Tuple,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        for obj in &x.args {
            self.verify_obj_well_defined_and_store_cache(obj, verify_state)?;
        }
        Ok(())
    }

    /// Mathematical contract: `finite_set_size(S)` is meaningful when `S` is
    /// a well-defined object provably known to be a finite set.
    pub(in crate::verify) fn verify_finite_set_size_well_defined(
        &mut self,
        x: &FiniteSetSize,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        // `finite_set_size` is well-defined only for finite sets.
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

    /// Mathematical contract: `finite_set_max(S)` requires a finite,
    /// nonempty set whose elements are provably real.
    pub(in crate::verify) fn verify_finite_set_max_well_defined(
        &mut self,
        x: &FiniteSetMax,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_finite_set_extremum_well_defined(&x.set, FINITE_SET_MAX, verify_state)
    }

    /// Mathematical contract: `finite_set_min(S)` requires a finite,
    /// nonempty set whose elements are provably real.
    pub(in crate::verify) fn verify_finite_set_min_well_defined(
        &mut self,
        x: &FiniteSetMin,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_finite_set_extremum_well_defined(&x.set, FINITE_SET_MIN, verify_state)
    }

    /// Mathematical contract: either finite-set extremum requires a
    /// well-defined, finite, nonempty subset of `R`.
    fn verify_finite_set_extremum_well_defined(
        &mut self,
        set: &Obj,
        operator_name: &str,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(set, verify_state)?;
        let finite: AtomicFact = IsFiniteSetFact::new(set.clone(), default_line_file()).into();
        let nonempty: AtomicFact = IsNonemptySetFact::new(set.clone(), default_line_file()).into();
        for fact in [finite, nonempty] {
            if self.verify_atomic_fact(&fact, verify_state)?.is_unknown() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "{operator_name} requires a finite, nonempty subset of R"
                    )),
                )));
            }
        }

        self.verify_set_elements_are_known_reals(set, operator_name, verify_state)
    }

    /// Mathematical contract: every possible member of the supplied set must
    /// be provably real; structural set forms reduce this to their carriers.
    fn verify_set_elements_are_known_reals(
        &mut self,
        set: &Obj,
        operator_name: &str,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        match set {
            Obj::ListSet(list_set) => {
                for element in &list_set.list {
                    self.require_obj_in_r(element, verify_state)?;
                }
                Ok(())
            }
            Obj::Union(union) => {
                self.verify_set_elements_are_known_reals(&union.left, operator_name, verify_state)?;
                self.verify_set_elements_are_known_reals(&union.right, operator_name, verify_state)
            }
            Obj::Intersect(intersect) => self.verify_set_elements_are_known_reals(
                &intersect.left,
                operator_name,
                verify_state,
            ),
            Obj::SetMinus(set_minus) => self.verify_set_elements_are_known_reals(
                &set_minus.left,
                operator_name,
                verify_state,
            ),
            Obj::SetDiff(set_diff) => {
                self.verify_set_elements_are_known_reals(
                    &set_diff.left,
                    operator_name,
                    verify_state,
                )?;
                self.verify_set_elements_are_known_reals(
                    &set_diff.right,
                    operator_name,
                    verify_state,
                )
            }
            Obj::SetBuilder(set_builder) => self.verify_set_elements_are_known_reals(
                &set_builder.param_set,
                operator_name,
                verify_state,
            ),
            _ => {
                let real_subset: AtomicFact =
                    SubsetFact::new(set.clone(), StandardSet::R.into(), default_line_file()).into();
                if self
                    .verify_atomic_fact(&real_subset, verify_state)?
                    .is_unknown()
                {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "{operator_name} requires a finite, nonempty subset of R"
                        )),
                    )));
                }
                Ok(())
            }
        }
    }

    /// Mathematical contract: `fn_range(f)` is meaningful when `f` is a
    /// well-defined callable with a known function-set signature.
    pub(in crate::verify) fn verify_fn_range_well_defined(
        &mut self,
        x: &FnRange,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.function, verify_state)?;
        if self.get_fn_range_function_body(&x.function).is_none() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "fn_range expects a function with a known function set, got {}",
                    x.function
                )),
            )));
        }
        Ok(())
    }

    /// Mathematical contract: `replacement(P,S)` requires a well-defined
    /// source set, a binary user predicate `P`, and a previously proved
    /// uniqueness theorem for the output associated with every input in `S`.
    pub(in crate::verify) fn verify_replacement_well_defined(
        &mut self,
        x: &Replacement,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        let prop_arity = self.replacement_prop_arity(x)?;
        if prop_arity != 2 {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "replacement({}, {}) expects a binary prop, but `{}` has arity {}",
                    x.prop_name, x.source_set, x.prop_name, prop_arity
                )),
            )));
        }

        self.verify_obj_well_defined_and_store_cache(&x.source_set, verify_state)?;
        let uniqueness_fact = self.replacement_uniqueness_fact(x)?;
        let uniqueness_as_fact: Fact = uniqueness_fact.clone().into();
        let exact_cached = self
            .verify_fact_from_cache_using_display_string(&uniqueness_as_fact)
            .is_some();
        let alpha_normalized_key = self.alpha_normalized_forall_cache_key(&uniqueness_fact)?;
        let (alpha_cached, _) = self.cache_known_facts_contains(&alpha_normalized_key);
        if !exact_cached && !alpha_cached {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "replacement({}, {}) needs uniqueness of `{}` over `{}`: {}",
                    x.prop_name, x.source_set, x.prop_name, x.source_set, uniqueness_fact
                )),
            )));
        }
        Ok(())
    }

    pub(in crate::verify) fn replacement_prop_arity(
        &self,
        x: &Replacement,
    ) -> Result<usize, RuntimeError> {
        let prop_name = x.prop_name.to_string();
        if let Some(definition) = self.get_prop_definition_by_name(&prop_name) {
            return Ok(definition.params_def_with_type.number_of_params());
        }
        if let Some(definition) = self.get_abstract_prop_definition_by_name(&prop_name) {
            return Ok(definition.params.len());
        }
        Err(RuntimeError::from(WellDefinedRuntimeError(
            RuntimeErrorStruct::new_with_just_msg(format!(
                "replacement({}, {}) expects `{}` to be a user-defined prop or abstract_prop",
                x.prop_name, x.source_set, x.prop_name
            )),
        )))
    }

    pub(in crate::verify) fn replacement_uniqueness_fact(
        &self,
        x: &Replacement,
    ) -> Result<ForallFact, RuntimeError> {
        let x_name = self.generate_internal_binder_name();
        let y_name = self.generate_internal_binder_name();
        let y2_name = self.generate_internal_binder_name();
        let x_group = self.fresh_param_group_with_type(
            vec![x_name],
            ParamType::Obj(x.source_set.as_ref().clone()),
        )?;
        let y_group =
            self.fresh_param_group_with_type(vec![y_name, y2_name], ParamType::Set(Set::new()))?;
        let x_obj = obj_for_bound_param_in_scope(&x_group.params[0], ParamObjType::Forall);
        let y_obj = obj_for_bound_param_in_scope(&y_group.params[0], ParamObjType::Forall);
        let y2_obj = obj_for_bound_param_in_scope(&y_group.params[1], ParamObjType::Forall);
        let line_file = default_line_file();

        ForallFact::new_canonical_forall(
            ParamDefWithType::new(vec![x_group, y_group]),
            vec![
                NormalAtomicFact::new(
                    x.prop_name.clone(),
                    vec![x_obj.clone(), y_obj.clone()],
                    line_file.clone(),
                )
                .into(),
                NormalAtomicFact::new(
                    x.prop_name.clone(),
                    vec![x_obj, y2_obj.clone()],
                    line_file.clone(),
                )
                .into(),
            ],
            vec![EqualFact::new(y_obj, y2_obj, line_file.clone()).into()],
            line_file,
        )
    }
}
