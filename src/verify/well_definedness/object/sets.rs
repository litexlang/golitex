//! Set, function-set, and tuple object well-definedness.

use crate::prelude::*;

impl Runtime {
    /// Mathematical contract: `union(A,B)` is meaningful when both operand
    /// expressions are well-defined set-theoretic objects.
    pub(in crate::verify) fn verify_union_well_defined(
        &mut self,
        x: &Union,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.left,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &x.right,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
        Ok(())
    }

    /// Mathematical contract: `intersect(A,B)` is meaningful when both
    /// operand expressions are well-defined set-theoretic objects.
    pub(in crate::verify) fn verify_intersect_well_defined(
        &mut self,
        x: &Intersect,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.left,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &x.right,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
        Ok(())
    }

    /// Mathematical contract: set subtraction is meaningful when both
    /// operand expressions are well-defined set-theoretic objects.
    pub(in crate::verify) fn verify_set_minus_well_defined(
        &mut self,
        x: &SetMinus,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.left,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &x.right,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
        Ok(())
    }

    /// Mathematical contract: big union is meaningful when its family
    /// expression is well-defined.
    pub(in crate::verify) fn verify_big_union_well_defined(
        &mut self,
        x: &BigUnion,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.left,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        Ok(())
    }

    /// Mathematical contract: big intersection is meaningful when its family
    /// expression is well-defined.
    pub(in crate::verify) fn verify_big_intersect_well_defined(
        &mut self,
        x: &BigIntersect,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.left,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        Ok(())
    }

    /// Mathematical contract: a finite extensional literal is meaningful when
    /// every element is well-defined and the literal's entries are provably
    /// pairwise distinct, as required by Litex's canonical-list invariant.
    pub(in crate::verify) fn verify_list_set_well_defined(
        &mut self,
        x: &ListSet,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        for (argument_index, obj) in x.list.iter().enumerate() {
            self.verify_child_obj_well_defined_and_store_cache(
                obj,
                verify_state,
                WellDefinedObjChildRole::ConstructorArgument { argument_index },
            )?;
        }

        let next_verify_state = verify_state.with_well_definedness_verified();
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
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        // A set-builder parameter is a local binder in this isolated environment.
        // Parsed set-builder facts use SetBuilder-tagged bound vars; a mismatched tag means
        // e.g. `x $in N` is never found when checking `b ^ x`, so pow domain fails.
        // Run in local env so param binding and body facts do not leak into the outer scope.
        self.run_in_local_env(|rt| {
            rt.verify_child_obj_well_defined_and_store_cache(
                &x.param_set,
                &ProofSearchState::initial(),
                WellDefinedObjChildRole::BinderParameterCarrier {
                    parameter_group_index: 0,
                },
            )?;
            if let Err(e) = rt.store_parameter_binding(&x.param_binding, BindingScope::LocalBinder)
            {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!("failed to verify well-defined of set builder {}", x),
                        e,
                    ),
                )));
            }
            let param_in_set: Fact = InFact::new(
                obj_for_bound_param_in_scope(&x.param_binding),
                (*x.param_set).clone(),
                default_line_file(),
            )
            .into();
            let mut parameter_infers = rt
                .store_with_well_defined_verification_and_infer_with_default_verify_state(
                    param_in_set,
                )
                .map_err(|e| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!("failed to verify well-defined of set builder {}", x),
                            e,
                        ),
                    ))
                })?;
            rt.attach_known_fact_ids_to_infer_result(&mut parameter_infers)?;

            for fact in x.facts.iter() {
                let mut result = match fact {
                    QuantifierFreeFact::AtomicFact(f) => rt
                        .store_quantifier_free_fact_with_well_defined_verification_and_infer(
                            &QuantifierFreeFact::AtomicFact(f.clone()),
                            verify_state,
                        ),
                    QuantifierFreeFact::AndFact(f) => rt
                        .store_quantifier_free_fact_with_well_defined_verification_and_infer(
                            &QuantifierFreeFact::AndFact(f.clone()),
                            verify_state,
                        ),
                    QuantifierFreeFact::ChainFact(f) => rt
                        .store_quantifier_free_fact_with_well_defined_verification_and_infer(
                            &QuantifierFreeFact::ChainFact(f.clone()),
                            verify_state,
                        ),
                    QuantifierFreeFact::OrFact(f) => rt
                        .store_quantifier_free_fact_with_well_defined_verification_and_infer(
                            &QuantifierFreeFact::OrFact(f.clone()),
                            verify_state,
                        ),
                }
                .map_err(|e| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!(
                                "failed to verify well-defined of set builder {}",
                                x.to_string()
                            ),
                            e,
                        ),
                    ))
                })?;
                rt.attach_known_fact_ids_to_infer_result(&mut result)?;
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
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        let bindings = x.body.params_def_with_set.collect_param_bindings();
        let rename_map = self.visible_binding_conflict_rename_map(&bindings)?;
        if !rename_map.is_empty() {
            let renamed = self.alpha_rename_fn_set(x, &rename_map)?;
            return self.verify_fn_set_well_defined(&renamed, verify_state);
        }

        for (parameter_group_index, param_def_with_set) in
            x.body.params_def_with_set.iter().enumerate()
        {
            self.verify_child_obj_well_defined_and_store_cache(
                param_def_with_set.set_obj(),
                verify_state,
                WellDefinedObjChildRole::BinderParameterCarrier {
                    parameter_group_index,
                },
            )?;
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
            if let Err(e) = self
                .store_quantifier_free_fact_with_well_defined_verification_and_infer(
                    fact,
                    verify_state,
                )
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
        }

        if let Err(e) = self.verify_child_obj_well_defined_and_store_cache(
            &x.body.ret_set,
            verify_state,
            WellDefinedObjChildRole::BinderReturnCarrier,
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

        Ok(())
    }

    /// Mathematical contract: `fn(params) T {body}` is meaningful when its
    /// function-set signature is meaningful, `body` is meaningful under that
    /// local domain, and the verifier proves `body in T` for every admissible
    /// parameter assignment.
    pub(in crate::verify) fn verify_anonymous_fn_well_defined(
        &mut self,
        x: &AnonymousFn,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        let bindings = x.body.params_def_with_set.collect_param_bindings();
        let rename_map = self.visible_binding_conflict_rename_map(&bindings)?;
        if !rename_map.is_empty() {
            let renamed = self.alpha_rename_anonymous_fn(x, &rename_map)?;
            return self.verify_anonymous_fn_well_defined(&renamed, verify_state);
        }

        self.run_in_local_env(|rt| {
            for (parameter_group_index, param_def_with_set) in
                x.body.params_def_with_set.iter().enumerate()
            {
                rt.verify_child_obj_well_defined_and_store_cache(
                    param_def_with_set.set_obj(),
                    verify_state,
                    WellDefinedObjChildRole::BinderParameterCarrier {
                        parameter_group_index,
                    },
                )?;
            }
            for param_def_with_set in x.body.params_def_with_set.iter() {
                let mut parameter_infers = rt
                    .define_params_with_set_in_scope(param_def_with_set, BindingScope::LocalBinder)
                    .map_err(|e| {
                        RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!(
                                "failed to verify well-defined of anonymous fn {}",
                                x.to_string()
                            ),
                            e,
                        ),
                    ))
                    })?;
                rt.attach_known_fact_ids_to_infer_result(&mut parameter_infers)?;
            }

            for fact in x.body.dom_facts.iter() {
                let mut domain_infers = rt
                    .store_quantifier_free_fact_with_well_defined_verification_and_infer(
                        fact,
                        verify_state,
                    )
                    .map_err(|e| {
                        RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!(
                                "failed to verify well-defined of anonymous fn {}",
                                x.to_string()
                            ),
                            e,
                        ),
                    ))
                    })?;
                rt.attach_known_fact_ids_to_infer_result(&mut domain_infers)?;
            }

            if let Err(e) = rt.verify_child_obj_well_defined_and_store_cache(
                &x.body.ret_set,
                verify_state,
                WellDefinedObjChildRole::BinderReturnCarrier,
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

            if let Err(e) = rt.verify_child_obj_well_defined_and_store_cache(
                &x.equal_to,
                verify_state,
                WellDefinedObjChildRole::BinderBody,
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

            let mut return_value_verified = !rt
                .verify_value_in_declared_return_set(
                (*x.equal_to).clone(),
                (*x.body.ret_set).clone(),
                default_line_file(),
                verify_state,
            )?
                .is_unknown();
            if !return_value_verified {
                'parameter_groups: for param_group in x.body.params_def_with_set.iter() {
                    for binding in param_group.params.iter() {
                        let param_obj =
                            obj_for_bound_param_in_scope(binding);
                        if !objs_equal_with_nested_binder_alpha_equivalence(
                            x.equal_to.as_ref(),
                            &param_obj,
                        ) {
                            continue;
                        }
                        let subset_fact: AtomicFact = SubsetFact::new(
                            param_group.set_obj().clone(),
                            (*x.body.ret_set).clone(),
                            default_line_file(),
                        )
                        .into();
                        let subset_result = rt.verify_atomic_fact(&subset_fact, verify_state)?;
                        if subset_result.is_success() {
                            return_value_verified = true;
                            break 'parameter_groups;
                        }
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
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        for (argument_index, obj) in x.args.iter().enumerate() {
            self.verify_child_obj_well_defined_and_store_cache(
                obj,
                verify_state,
                WellDefinedObjChildRole::ConstructorArgument { argument_index },
            )?;
        }
        Ok(())
    }

    /// Mathematical contract: `cart_dim(S)` is meaningful when `S` is a
    /// well-defined Cartesian-product carrier.
    pub(in crate::verify) fn verify_cart_dim_well_defined(
        &mut self,
        x: &CartDim,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.set,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;

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
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.set,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &x.dim,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;

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
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.arg,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;

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
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        for (argument_index, obj) in x.args.iter().enumerate() {
            self.verify_child_obj_well_defined_and_store_cache(
                obj,
                verify_state,
                WellDefinedObjChildRole::ConstructorArgument { argument_index },
            )?;
        }
        Ok(())
    }

    /// Mathematical contract: `finite_set_size(S)` is meaningful when `S` is
    /// a well-defined object provably known to be a finite set.
    pub(in crate::verify) fn verify_finite_set_size_well_defined(
        &mut self,
        x: &FiniteSetSize,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.set,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
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
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.set,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_finite_set_extremum_well_defined(&x.set, FINITE_SET_MAX, verify_state)
    }

    /// Mathematical contract: `finite_set_min(S)` requires a finite,
    /// nonempty set whose elements are provably real.
    pub(in crate::verify) fn verify_finite_set_min_well_defined(
        &mut self,
        x: &FiniteSetMin,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.set,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_finite_set_extremum_well_defined(&x.set, FINITE_SET_MIN, verify_state)
    }

    /// Mathematical contract: either finite-set extremum requires a
    /// well-defined, finite, nonempty subset of `R`.
    fn verify_finite_set_extremum_well_defined(
        &mut self,
        set: &Obj,
        operator_name: &str,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
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
        verify_state: &ProofSearchState,
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
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.function,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
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
        verify_state: &ProofSearchState,
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

        self.verify_child_obj_well_defined_and_store_cache(
            &x.source_set,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        let uniqueness_fact = self.replacement_uniqueness_fact(x)?;
        let uniqueness_as_fact: Fact = uniqueness_fact.clone().into();
        let exact_cached = self
            .verification_result_from_known_fact_cache(&uniqueness_as_fact)
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
        let x_obj = obj_for_bound_param_in_scope(&x_group.params[0]);
        let y_obj = obj_for_bound_param_in_scope(&y_group.params[0]);
        let y2_obj = obj_for_bound_param_in_scope(&y_group.params[1]);
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

impl Runtime {
    fn verify_set_constructor_children_result(
        &mut self,
        arguments: &[Obj],
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        for (argument_index, argument) in arguments.iter().enumerate() {
            steps.push_child(self.verify_child_obj_well_defined_result(
                argument,
                verify_state,
                WellDefinedObjChildRole::ConstructorArgument { argument_index },
            )?);
        }
        Ok(steps)
    }

    pub(in crate::verify) fn verify_set_builder_well_defined_result(
        &mut self,
        value: &SetBuilder,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let rename_map =
            self.visible_binding_conflict_rename_map(std::slice::from_ref(&value.param_binding))?;
        if !rename_map.is_empty() {
            let renamed = self.alpha_rename_set_builder(value, &rename_map)?;
            return self.verify_set_builder_well_defined_result(&renamed, verify_state);
        }
        self.run_in_local_env(|runtime| {
            let parameter_carrier = runtime.verify_child_obj_well_defined_result(
                &value.param_set,
                &ProofSearchState::initial(),
                WellDefinedObjChildRole::BinderParameterCarrier {
                    parameter_group_index: 0,
                },
            )?;
            runtime
                .store_parameter_binding(&value.param_binding, BindingScope::LocalBinder)
                .map_err(|error| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!("failed to verify well-defined of set builder {}", value),
                            error,
                        ),
                    ))
                })?;

            let parameter_fact: Fact = InFact::new(
                obj_for_bound_param_in_scope(&value.param_binding),
                (*value.param_set).clone(),
                default_line_file(),
            )
            .into();
            let parameter_well_definedness =
                runtime.verify_fact_well_defined_result(&parameter_fact, verify_state)?;
            let Fact::AtomicFact(parameter_atomic_fact) = parameter_fact.clone() else {
                unreachable!("set-builder parameter membership is atomic")
            };
            let mut parameter_infers = runtime
                .store_atomic_fact_without_well_defined_verified_and_infer_with_reason(
                    parameter_atomic_fact,
                    InferReason::ParameterDefinition.store_reason(),
                )?;
            runtime.attach_known_fact_ids_to_infer_result(&mut parameter_infers)?;
            let parameter = SuccessVerifyBinderPremiseResult::new(
                WellDefinedBinderPremiseRole::ParameterMembership {
                    parameter_group_index: 0,
                    parameter_index: 0,
                },
                Some(value.param_binding.id()),
                parameter_fact,
                parameter_well_definedness,
                parameter_infers,
            );

            let mut conditions = Vec::with_capacity(value.facts.len());
            for (condition_index, condition) in value.facts.iter().enumerate() {
                let condition_fact: Fact = condition.clone().into();
                let well_definedness =
                    runtime.verify_fact_well_defined_result(&condition_fact, verify_state)?;
                let mut infers = runtime
                    .store_quantifier_free_fact_without_well_defined_verified_and_infer(
                        condition.clone(),
                    )?;
                runtime.attach_known_fact_ids_to_infer_result(&mut infers)?;
                let fact_id = runtime.known_fact_id_for_fact(&condition_fact)?;
                conditions.push(SuccessVerifySetBuilderConditionResult::new(
                    condition_index,
                    well_definedness,
                    SuccessStoreFactResult {
                        fact: condition_fact,
                        fact_id,
                        infers,
                    },
                ));
            }

            let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
            steps.binder = Some(Box::new(
                SuccessVerifyBinderObjectWellDefinedResult::SetBuilder(Box::new(
                    SuccessVerifySetBuilderWellDefinedResult {
                        parameter_carrier,
                        parameter,
                        conditions,
                    },
                )),
            ));
            Ok(steps)
        })
    }

    pub(in crate::verify) fn verify_fn_set_well_defined_result(
        &mut self,
        value: &FnSet,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let bindings = value.body.params_def_with_set.collect_param_bindings();
        let rename_map = self.visible_binding_conflict_rename_map(&bindings)?;
        if !rename_map.is_empty() {
            let renamed = self.alpha_rename_fn_set(value, &rename_map)?;
            return self.verify_fn_set_well_defined_result(&renamed, verify_state);
        }
        self.run_in_local_env(|runtime| {
            let (parameter_carriers, parameters, domains) = runtime
                .verify_fn_binder_inputs_result(
                    &value.body.params_def_with_set,
                    &value.body.dom_facts,
                    verify_state,
                )?;
            let return_carrier = runtime.verify_child_obj_well_defined_result(
                &value.body.ret_set,
                verify_state,
                WellDefinedObjChildRole::BinderReturnCarrier,
            )?;
            let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
            steps.binder = Some(Box::new(
                SuccessVerifyBinderObjectWellDefinedResult::FunctionSet(Box::new(
                    SuccessVerifyFunctionSetWellDefinedResult {
                        parameter_carriers,
                        parameters,
                        domains,
                        return_carrier,
                    },
                )),
            ));
            Ok(steps)
        })
    }

    pub(in crate::verify) fn verify_anonymous_fn_well_defined_result(
        &mut self,
        value: &AnonymousFn,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let bindings = value.body.params_def_with_set.collect_param_bindings();
        let rename_map = self.visible_binding_conflict_rename_map(&bindings)?;
        if !rename_map.is_empty() {
            let renamed = self.alpha_rename_anonymous_fn(value, &rename_map)?;
            return self.verify_anonymous_fn_well_defined_result(&renamed, verify_state);
        }
        self.run_in_local_env(|runtime| {
            let (parameter_carriers, parameters, domains) = runtime
                .verify_fn_binder_inputs_result(
                    &value.body.params_def_with_set,
                    &value.body.dom_facts,
                    verify_state,
                )?;
            let return_carrier = runtime.verify_child_obj_well_defined_result(
                &value.body.ret_set,
                verify_state,
                WellDefinedObjChildRole::BinderReturnCarrier,
            )?;
            let body = runtime.verify_child_obj_well_defined_result(
                &value.equal_to,
                verify_state,
                WellDefinedObjChildRole::BinderBody,
            )?;
            let parent: Obj = value.clone().into();
            let direct_membership = runtime.verify_value_in_declared_return_set(
                (*value.equal_to).clone(),
                (*value.body.ret_set).clone(),
                default_line_file(),
                verify_state,
            )?;
            let body_membership = if direct_membership.is_success() {
                super::success_obj_target_requirement(
                    parent,
                    WellDefinednessRequirementRole::AnonymousFunctionBodyMembership,
                    direct_membership,
                )?
            } else {
                let mut subset_result = None;
                'groups: for (parameter_group_index, group) in
                    value.body.params_def_with_set.iter().enumerate()
                {
                    for (parameter_index, binding) in group.params.iter().enumerate() {
                        let parameter =
                            obj_for_bound_param_in_scope(binding);
                        if !objs_equal_with_nested_binder_alpha_equivalence(
                            value.equal_to.as_ref(),
                            &parameter,
                        ) {
                            continue;
                        }
                        let subset: AtomicFact = SubsetFact::new(
                            group.set_obj().clone(),
                            (*value.body.ret_set).clone(),
                            default_line_file(),
                        )
                        .into();
                        let result = runtime.verify_atomic_fact(&subset, verify_state)?;
                        if result.is_success() {
                            subset_result = Some(super::success_obj_target_requirement(
                                value.clone().into(),
                                WellDefinednessRequirementRole::AnonymousFunctionBoundParameterSubset {
                                    parameter_group_index,
                                    parameter_index,
                                },
                                result,
                            )?);
                            break 'groups;
                        }
                    }
                }
                subset_result.ok_or_else(|| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "anonymous function body {} is not verified to belong to declared return set {}",
                            value.equal_to, value.body.ret_set
                        )),
                    ))
                })?
            };
            let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
            steps.binder = Some(Box::new(
                SuccessVerifyBinderObjectWellDefinedResult::AnonymousFunction(Box::new(
                    SuccessVerifyAnonymousFunctionWellDefinedResult {
                        parameter_carriers,
                        parameters,
                        domains,
                        return_carrier,
                        body,
                        body_membership,
                    },
                )),
            ));
            Ok(steps)
        })
    }

    pub(in crate::verify) fn verify_fn_binder_inputs_result(
        &mut self,
        parameter_definition: &ParamDefWithSet,
        domain_facts: &[QuantifierFreeFact],
        verify_state: &ProofSearchState,
    ) -> Result<
        (
            Vec<SuccessVerifyChildObjWellDefinedResult>,
            Vec<SuccessVerifyBinderPremiseResult>,
            Vec<SuccessVerifyBinderPremiseResult>,
        ),
        RuntimeError,
    > {
        let mut parameter_carriers = Vec::with_capacity(parameter_definition.len());
        let mut parameters = Vec::with_capacity(parameter_definition.number_of_params());
        for (parameter_group_index, group) in parameter_definition.iter().enumerate() {
            parameter_carriers.push(self.verify_child_obj_well_defined_result(
                group.set_obj(),
                verify_state,
                WellDefinedObjChildRole::BinderParameterCarrier {
                    parameter_group_index,
                },
            )?);
            for (parameter_index, binding) in group.params.iter().enumerate() {
                self.store_parameter_binding(binding, BindingScope::LocalBinder)?;
                let proposition: Fact = InFact::new(
                    obj_for_bound_param_in_scope(binding),
                    group.set_obj().clone(),
                    default_line_file(),
                )
                .into();
                let well_definedness =
                    self.verify_fact_well_defined_result(&proposition, verify_state)?;
                let Fact::AtomicFact(atomic) = proposition.clone() else {
                    unreachable!("function parameter membership is atomic")
                };
                let mut infers = self
                    .store_atomic_fact_without_well_defined_verified_and_infer_with_reason(
                        atomic,
                        InferReason::ParameterDefinition.store_reason(),
                    )?;
                self.attach_known_fact_ids_to_infer_result(&mut infers)?;
                parameters.push(SuccessVerifyBinderPremiseResult::new(
                    WellDefinedBinderPremiseRole::ParameterMembership {
                        parameter_group_index,
                        parameter_index,
                    },
                    Some(binding.id()),
                    proposition,
                    well_definedness,
                    infers,
                ));
            }
        }

        let mut domains = Vec::with_capacity(domain_facts.len());
        for (domain_index, domain) in domain_facts.iter().enumerate() {
            let proposition: Fact = domain.clone().into();
            let well_definedness =
                self.verify_fact_well_defined_result(&proposition, verify_state)?;
            let mut infers = self
                .store_quantifier_free_fact_without_well_defined_verified_and_infer(
                    domain.clone(),
                )?;
            self.attach_known_fact_ids_to_infer_result(&mut infers)?;
            domains.push(SuccessVerifyBinderPremiseResult::new(
                WellDefinedBinderPremiseRole::Domain { domain_index },
                None,
                proposition,
                well_definedness,
                infers,
            ));
        }
        Ok((parameter_carriers, parameters, domains))
    }

    fn push_set_wd_fact_check(
        &mut self,
        steps: &mut SuccessVerifyObjWellDefinedStepsResult,
        fact: &AtomicFact,
        verify_state: &ProofSearchState,
        error_message: String,
    ) -> Result<(), RuntimeError> {
        let result = self.verify_atomic_fact(fact, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(error_message),
            )));
        }
        steps.push_fact_check(super::success_obj_fact_check(result)?);
        Ok(())
    }

    fn push_required_real_object_result(
        &mut self,
        steps: &mut SuccessVerifyObjWellDefinedStepsResult,
        object: &Obj,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        match object {
            Obj::Abs(value) => {
                self.push_required_real_object_result(steps, &value.arg, verify_state)
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
                self.push_required_real_object_result(steps, &value.base, verify_state)?;
                self.push_required_real_object_result(steps, &value.arg, verify_state)
            }
            _ => {
                let fact: AtomicFact =
                    InFact::new(object.clone(), StandardSet::R.into(), default_line_file()).into();
                self.push_set_wd_fact_check(
                    steps,
                    &fact,
                    verify_state,
                    format!("obj {object} is not in r"),
                )
            }
        }
    }

    fn push_set_elements_are_known_reals_result(
        &mut self,
        steps: &mut SuccessVerifyObjWellDefinedStepsResult,
        set: &Obj,
        operator_name: &str,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        match set {
            Obj::ListSet(list_set) => {
                for element in &list_set.list {
                    self.push_required_real_object_result(steps, element, verify_state)?;
                }
                Ok(())
            }
            Obj::Union(union) => {
                self.push_set_elements_are_known_reals_result(
                    steps,
                    &union.left,
                    operator_name,
                    verify_state,
                )?;
                self.push_set_elements_are_known_reals_result(
                    steps,
                    &union.right,
                    operator_name,
                    verify_state,
                )
            }
            Obj::Intersect(intersect) => self.push_set_elements_are_known_reals_result(
                steps,
                &intersect.left,
                operator_name,
                verify_state,
            ),
            Obj::SetMinus(set_minus) => self.push_set_elements_are_known_reals_result(
                steps,
                &set_minus.left,
                operator_name,
                verify_state,
            ),
            Obj::SetBuilder(set_builder) => self.push_set_elements_are_known_reals_result(
                steps,
                &set_builder.param_set,
                operator_name,
                verify_state,
            ),
            _ => {
                let subset: AtomicFact =
                    SubsetFact::new(set.clone(), StandardSet::R.into(), default_line_file()).into();
                self.push_set_wd_fact_check(
                    steps,
                    &subset,
                    verify_state,
                    format!("{operator_name} requires a finite, nonempty subset of R"),
                )
            }
        }
    }

    fn verify_finite_set_extremum_well_defined_result(
        &mut self,
        set: &Obj,
        operator_name: &str,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps =
            self.verify_set_constructor_children_result(&[set.clone()], verify_state)?;
        let finite: AtomicFact = IsFiniteSetFact::new(set.clone(), default_line_file()).into();
        let nonempty: AtomicFact = IsNonemptySetFact::new(set.clone(), default_line_file()).into();
        let error_message = format!("{operator_name} requires a finite, nonempty subset of R");
        self.push_set_wd_fact_check(&mut steps, &finite, verify_state, error_message.clone())?;
        self.push_set_wd_fact_check(&mut steps, &nonempty, verify_state, error_message)?;
        self.push_set_elements_are_known_reals_result(
            &mut steps,
            set,
            operator_name,
            verify_state,
        )?;
        Ok(steps)
    }

    pub(in crate::verify) fn verify_union_well_defined_result(
        &mut self,
        value: &Union,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_set_constructor_children_result(
            &[(*value.left).clone(), (*value.right).clone()],
            verify_state,
        )
    }

    pub(in crate::verify) fn verify_intersect_well_defined_result(
        &mut self,
        value: &Intersect,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_set_constructor_children_result(
            &[(*value.left).clone(), (*value.right).clone()],
            verify_state,
        )
    }

    pub(in crate::verify) fn verify_set_minus_well_defined_result(
        &mut self,
        value: &SetMinus,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_set_constructor_children_result(
            &[(*value.left).clone(), (*value.right).clone()],
            verify_state,
        )
    }

    pub(in crate::verify) fn verify_big_union_well_defined_result(
        &mut self,
        value: &BigUnion,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_set_constructor_children_result(&[(*value.left).clone()], verify_state)
    }

    pub(in crate::verify) fn verify_big_intersect_well_defined_result(
        &mut self,
        value: &BigIntersect,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_set_constructor_children_result(&[(*value.left).clone()], verify_state)
    }

    pub(in crate::verify) fn verify_list_set_well_defined_result(
        &mut self,
        value: &ListSet,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let arguments = value
            .list
            .iter()
            .map(|element| element.as_ref().clone())
            .collect::<Vec<_>>();
        let mut steps = self.verify_set_constructor_children_result(&arguments, verify_state)?;
        let parent: Obj = value.clone().into();
        let next_verify_state = verify_state.with_well_definedness_verified();
        for left_index in 0..arguments.len() {
            for right_index in left_index + 1..arguments.len() {
                let fact: AtomicFact = NotEqualFact::new(
                    arguments[left_index].clone(),
                    arguments[right_index].clone(),
                    default_line_file(),
                )
                .into();
                let result = self.verify_atomic_fact(&fact, &next_verify_state)?;
                if result.is_unknown() {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "list set elements must be pairwise not equal, but it is not provable: {fact}"
                        )),
                    )));
                }
                steps.push_target_requirement(super::success_obj_target_requirement(
                    parent.clone(),
                    WellDefinednessRequirementRole::ConstructorPairwiseDistinct {
                        left_index,
                        right_index,
                    },
                    result,
                )?);
            }
        }
        Ok(steps)
    }

    pub(in crate::verify) fn verify_cart_well_defined_result(
        &mut self,
        value: &Cart,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let arguments = value
            .args
            .iter()
            .map(|argument| argument.as_ref().clone())
            .collect::<Vec<_>>();
        self.verify_set_constructor_children_result(&arguments, verify_state)
    }

    pub(in crate::verify) fn verify_cart_dim_well_defined_result(
        &mut self,
        value: &CartDim,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps =
            self.verify_set_constructor_children_result(&[(*value.set).clone()], verify_state)?;
        let fact: AtomicFact = IsCartFact::new((*value.set).clone(), default_line_file()).into();
        self.push_set_wd_fact_check(
            &mut steps,
            &fact,
            verify_state,
            format!("set {} is not a cart", value.set),
        )?;
        Ok(steps)
    }

    pub(in crate::verify) fn verify_proj_well_defined_result(
        &mut self,
        value: &Proj,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = self.verify_set_constructor_children_result(
            &[(*value.set).clone(), (*value.dim).clone()],
            verify_state,
        )?;
        let dimension: Obj = self
            .resolve_obj_to_number(&value.dim)
            .map(|number| Number::new(number.normalized_value).into())
            .unwrap_or_else(|| (*value.dim).clone());
        let positive: AtomicFact = InFact::new(
            dimension.clone(),
            StandardSet::NPos.into(),
            default_line_file(),
        )
        .into();
        self.push_set_wd_fact_check(
            &mut steps,
            &positive,
            verify_state,
            format!("projection dimension {dimension} is not a positive integer"),
        )?;
        let cart: AtomicFact = IsCartFact::new((*value.set).clone(), default_line_file()).into();
        self.push_set_wd_fact_check(
            &mut steps,
            &cart,
            verify_state,
            format!("projection left side {} is not a cart", value.set),
        )?;
        let cart_dim: Obj = CartDim::new((*value.set).clone()).into();
        let bounded: AtomicFact =
            LessEqualFact::new(dimension.clone(), cart_dim.clone(), default_line_file()).into();
        self.push_set_wd_fact_check(
            &mut steps,
            &bounded,
            verify_state,
            format!("{dimension} <= {cart_dim} is unknown"),
        )?;
        Ok(steps)
    }

    pub(in crate::verify) fn verify_tuple_dim_well_defined_result(
        &mut self,
        value: &TupleDim,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps =
            self.verify_set_constructor_children_result(&[(*value.arg).clone()], verify_state)?;
        let fact: AtomicFact = IsTupleFact::new((*value.arg).clone(), default_line_file()).into();
        self.push_set_wd_fact_check(
            &mut steps,
            &fact,
            verify_state,
            format!("`{fact}` is unknown, `dim` object requires its argument to be a tuple"),
        )?;
        Ok(steps)
    }

    pub(in crate::verify) fn verify_tuple_well_defined_result(
        &mut self,
        value: &Tuple,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let arguments = value
            .args
            .iter()
            .map(|argument| argument.as_ref().clone())
            .collect::<Vec<_>>();
        self.verify_set_constructor_children_result(&arguments, verify_state)
    }

    pub(in crate::verify) fn verify_finite_set_size_well_defined_result(
        &mut self,
        value: &FiniteSetSize,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps =
            self.verify_set_constructor_children_result(&[(*value.set).clone()], verify_state)?;
        let fact: AtomicFact =
            IsFiniteSetFact::new((*value.set).clone(), default_line_file()).into();
        self.push_set_wd_fact_check(
            &mut steps,
            &fact,
            verify_state,
            format!("set {} is not a finite set", value.set),
        )?;
        Ok(steps)
    }

    pub(in crate::verify) fn verify_finite_set_max_well_defined_result(
        &mut self,
        value: &FiniteSetMax,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_finite_set_extremum_well_defined_result(
            &value.set,
            FINITE_SET_MAX,
            verify_state,
        )
    }

    pub(in crate::verify) fn verify_finite_set_min_well_defined_result(
        &mut self,
        value: &FiniteSetMin,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_finite_set_extremum_well_defined_result(
            &value.set,
            FINITE_SET_MIN,
            verify_state,
        )
    }

    pub(in crate::verify) fn verify_fn_range_well_defined_result(
        &mut self,
        value: &FnRange,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let steps = self
            .verify_set_constructor_children_result(&[(*value.function).clone()], verify_state)?;
        if self.get_fn_range_function_body(&value.function).is_none() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "fn_range expects a function with a known function set, got {}",
                    value.function
                )),
            )));
        }
        Ok(steps)
    }

    pub(in crate::verify) fn verify_replacement_well_defined_result(
        &mut self,
        value: &Replacement,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let prop_arity = self.replacement_prop_arity(value)?;
        if prop_arity != 2 {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "replacement({}, {}) expects a binary prop, but `{}` has arity {}",
                    value.prop_name, value.source_set, value.prop_name, prop_arity
                )),
            )));
        }
        let steps = self
            .verify_set_constructor_children_result(&[(*value.source_set).clone()], verify_state)?;
        let uniqueness = self.replacement_uniqueness_fact(value)?;
        let uniqueness_as_fact: Fact = uniqueness.clone().into();
        let exact_cached = self
            .verification_result_from_known_fact_cache(&uniqueness_as_fact)
            .is_some();
        let alpha_key = self.alpha_normalized_forall_cache_key(&uniqueness)?;
        let (alpha_cached, _) = self.cache_known_facts_contains(&alpha_key);
        if !exact_cached && !alpha_cached {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "replacement({}, {}) needs uniqueness of `{}` over `{}`: {}",
                    value.prop_name,
                    value.source_set,
                    value.prop_name,
                    value.source_set,
                    uniqueness
                )),
            )));
        }
        Ok(steps)
    }
}
