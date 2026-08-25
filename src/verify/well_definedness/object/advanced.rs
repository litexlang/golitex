//! Advanced object constructors and indexed families.

use crate::prelude::*;

impl Runtime {
    fn verify_indexed_set_family_operator_well_defined_result(
        &mut self,
        index_set: &Obj,
        ambient_set: &Obj,
        family_fn: &Obj,
        operator_display: &str,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        for (argument_index, child) in [index_set, ambient_set, family_fn].into_iter().enumerate() {
            steps.push_child(self.verify_child_obj_well_defined_result(
                child,
                verify_state,
                WellDefinedObjChildRole::ConstructorArgument { argument_index },
            )?);
        }

        for set in [index_set, ambient_set] {
            let is_set: Fact = IsSetFact::new(set.clone(), default_line_file()).into();
            let result = self
                .verify_fact_or_error(&is_set, verify_state)
                .map_err(|error| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!("failed to verify well-defined of {operator_display}"),
                            error,
                        ),
                    ))
                })?;
            steps.push_fact_check(super::success_obj_fact_check(result)?);
        }

        let family_param_name = self.generate_internal_binder_name();
        let family_fn_set: Obj = FnSet::new(
            vec![self.fresh_param_group_with_set(vec![family_param_name], index_set.clone())?],
            vec![],
            PowerSet::new(ambient_set.clone()).into(),
        )?
        .into();
        let family_fn_type: Fact =
            InFact::new(family_fn.clone(), family_fn_set, default_line_file()).into();
        let result = self
            .verify_fact_or_error(&family_fn_type, verify_state)
            .map_err(|error| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!("failed to verify well-defined of {operator_display}"),
                        error,
                    ),
                ))
            })?;
        steps.push_fact_check(super::success_obj_fact_check(result)?);
        Ok(steps)
    }

    pub(in crate::verify) fn verify_index_union_well_defined_result(
        &mut self,
        value: &IndexUnion,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_indexed_set_family_operator_well_defined_result(
            &value.index_set,
            &value.ambient_set,
            &value.family_fn,
            &value.to_string(),
            verify_state,
        )
    }

    pub(in crate::verify) fn verify_index_intersect_well_defined_result(
        &mut self,
        value: &IndexIntersect,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_indexed_set_family_operator_well_defined_result(
            &value.index_set,
            &value.ambient_set,
            &value.family_fn,
            &value.to_string(),
            verify_state,
        )
    }

    pub(in crate::verify) fn verify_power_set_well_defined_result(
        &mut self,
        value: &PowerSet,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        steps.push_child(self.verify_child_obj_well_defined_result(
            &value.set,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?);
        Ok(steps)
    }

    pub(in crate::verify) fn verify_general_cart_well_defined_result(
        &mut self,
        value: &GeneralCart,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        for (argument_index, child) in [&value.index_set, &value.family_set, &value.family_fn]
            .into_iter()
            .enumerate()
        {
            steps.push_child(self.verify_child_obj_well_defined_result(
                child,
                verify_state,
                WellDefinedObjChildRole::ConstructorArgument { argument_index },
            )?);
        }

        let index_is_set: Fact =
            IsSetFact::new((*value.index_set).clone(), default_line_file()).into();
        let index_result = self
            .verify_fact_or_error(&index_is_set, verify_state)
            .map_err(|error| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!("failed to verify well-defined of {value}"),
                        error,
                    ),
                ))
            })?;
        steps.push_fact_check(super::success_obj_fact_check(index_result)?);

        let family_is_nonempty: Fact =
            IsNonemptySetFact::new((*value.family_set).clone(), default_line_file()).into();
        let family_result = self
            .verify_fact_or_error(&family_is_nonempty, verify_state)
            .map_err(|error| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!("failed to verify well-defined of {value}"),
                        error,
                    ),
                ))
            })?;
        steps.push_fact_check(super::success_obj_fact_check(family_result)?);

        let family_param_name = self.generate_internal_binder_name();
        let family_fn_set: Obj = FnSet::new(
            vec![self
                .fresh_param_group_with_set(vec![family_param_name], (*value.index_set).clone())?],
            vec![],
            (*value.family_set).clone(),
        )?
        .into();
        let family_fn_type: Fact = InFact::new(
            (*value.family_fn).clone(),
            family_fn_set,
            default_line_file(),
        )
        .into();
        let function_result = self
            .verify_fact_or_error(&family_fn_type, verify_state)
            .map_err(|error| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!("failed to verify well-defined of {value}"),
                        error,
                    ),
                ))
            })?;
        steps.push_fact_check(super::success_obj_fact_check(function_result)?);
        Ok(steps)
    }

    pub(in crate::verify) fn verify_obj_at_index_well_defined_result(
        &mut self,
        value: &ObjAtIndex,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        for (argument_index, child) in [&value.obj, &value.index].into_iter().enumerate() {
            steps.push_child(self.verify_child_obj_well_defined_result(
                child,
                verify_state,
                WellDefinedObjChildRole::ConstructorArgument { argument_index },
            )?);
        }

        let calculated_index: Obj = self
            .resolve_obj_to_number(&value.index)
            .map(|number| Number::new(number.normalized_value).into())
            .unwrap_or_else(|| (*value.index).clone());
        let positive: AtomicFact = InFact::new(
            calculated_index.clone(),
            StandardSet::NPos.into(),
            default_line_file(),
        )
        .into();
        let positive_result = self.verify_atomic_fact(&positive, verify_state)?;
        if positive_result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "index {calculated_index} is not a positive integer"
                )),
            )));
        }
        steps.push_fact_check(super::success_obj_fact_check(positive_result)?);

        self.store_fn_obj_cart_return_facts_if_available(&value.obj, default_line_file())?;
        let default_struct_view = self.known_struct_carrier_for_obj(&value.obj);
        if let Some(struct_obj) = default_struct_view {
            let struct_membership: AtomicFact = InFact::new(
                (*value.obj).clone(),
                struct_obj.clone().into(),
                default_line_file(),
            )
            .into();
            let membership_result = self.verify_atomic_fact(&struct_membership, verify_state)?;
            if membership_result.is_success() {
                steps.push_fact_check(super::success_obj_fact_check(membership_result)?);
                let field_types =
                    self.instantiated_struct_field_types(&struct_obj, verify_state)?;
                if field_types.len() > 1 {
                    let cart_membership: AtomicFact = InFact::new(
                        (*value.obj).clone(),
                        Cart::new(field_types).into(),
                        default_line_file(),
                    )
                    .into();
                    self.store_atomic_fact_without_well_defined_verified_and_infer(
                        cart_membership,
                    )?;
                }
            }
        }

        let is_tuple: AtomicFact =
            IsTupleFact::new((*value.obj).clone(), default_line_file()).into();
        let tuple_result = self.verify_atomic_fact(&is_tuple, verify_state)?;
        if tuple_result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "index target {} is not a tuple",
                    value.obj
                )),
            )));
        }
        steps.push_fact_check(super::success_obj_fact_check(tuple_result)?);

        let tuple_dim: Obj = TupleDim::new((*value.obj).clone()).into();
        let bounded: AtomicFact = LessEqualFact::new(
            calculated_index.clone(),
            tuple_dim.clone(),
            default_line_file(),
        )
        .into();
        let bounded_result = self.verify_atomic_fact(&bounded, verify_state)?;
        if bounded_result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{calculated_index} <= {tuple_dim} is unknown"
                )),
            )));
        }
        steps.push_fact_check(super::success_obj_fact_check(bounded_result)?);
        Ok(steps)
    }

    fn verify_indexed_set_family_operator_well_defined(
        &mut self,
        index_set: &Obj,
        ambient_set: &Obj,
        family_fn: &Obj,
        operator_display: &str,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        for (argument_index, child) in [index_set, ambient_set, family_fn].into_iter().enumerate() {
            self.verify_child_obj_well_defined_and_store_cache(
                child,
                verify_state,
                WellDefinedObjChildRole::ConstructorArgument { argument_index },
            )?;
        }

        for set in [index_set, ambient_set] {
            let is_set: Fact = IsSetFact::new(set.clone(), default_line_file()).into();
            self.verify_fact_or_error(&is_set, verify_state)
                .map_err(|e| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!("failed to verify well-defined of {operator_display}"),
                            e,
                        ),
                    ))
                })?;
        }

        let family_param_name = self.generate_internal_binder_name();
        let family_fn_set: Obj = FnSet::new(
            vec![self.fresh_param_group_with_set(vec![family_param_name], index_set.clone())?],
            vec![],
            PowerSet::new(ambient_set.clone()).into(),
        )?
        .into();
        let family_fn_type: Fact =
            InFact::new(family_fn.clone(), family_fn_set, default_line_file()).into();
        self.verify_fact_or_error(&family_fn_type, verify_state)
            .map_err(|e| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!("failed to verify well-defined of {operator_display}"),
                        e,
                    ),
                ))
            })?;

        Ok(())
    }

    /// `index_union(I, X, A)` is meaningful for every set `I`, including the
    /// empty set, when `X` is a set and `A : I -> power_set(X)`.
    pub(in crate::verify) fn verify_index_union_well_defined(
        &mut self,
        x: &IndexUnion,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_indexed_set_family_operator_well_defined(
            &x.index_set,
            &x.ambient_set,
            &x.family_fn,
            &x.to_string(),
            verify_state,
        )
    }

    /// `index_intersect(I, X, A)` has the same typing contract as indexed
    /// union; no nonemptiness premise is required because the ambient set is
    /// the empty-family intersection.
    pub(in crate::verify) fn verify_index_intersect_well_defined(
        &mut self,
        x: &IndexIntersect,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_indexed_set_family_operator_well_defined(
            &x.index_set,
            &x.ambient_set,
            &x.family_fn,
            &x.to_string(),
            verify_state,
        )
    }

    /// Mathematical contract: `power_set(S)` is meaningful when its base
    /// object `S` is well-defined; sethood is handled by the set semantics.
    pub(in crate::verify) fn verify_power_set_well_defined(
        &mut self,
        x: &PowerSet,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.set,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        Ok(())
    }

    /// Mathematical contract: a general Cartesian product has a set-valued
    /// index domain `I`, a nonempty family carrier `S`, and a family selector
    /// of type `fn(i I) S`; all three objects must be well-defined.
    pub(in crate::verify) fn verify_general_cart_well_defined(
        &mut self,
        x: &GeneralCart,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.index_set,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &x.family_set,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &x.family_fn,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 2 },
        )?;

        let index_is_set: Fact = IsSetFact::new((*x.index_set).clone(), default_line_file()).into();
        self.verify_fact_or_error(&index_is_set, verify_state)
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
        self.verify_fact_or_error(&family_is_nonempty, verify_state)
            .map_err(|e| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!("failed to verify well-defined of {}", x),
                        e,
                    ),
                ))
            })?;

        let family_param_name = self.generate_internal_binder_name();
        let family_fn_set: Obj = FnSet::new(
            vec![self.fresh_param_group_with_set(vec![family_param_name], (*x.index_set).clone())?],
            vec![],
            (*x.family_set).clone(),
        )?
        .into();
        let family_fn_type: Fact =
            InFact::new((*x.family_fn).clone(), family_fn_set, default_line_file()).into();
        self.verify_fact_or_error(&family_fn_type, verify_state)
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

    /// Mathematical contract: `a[i]` is meaningful when `a` is a tuple, `i`
    /// is a positive integer, and `i <= tuple_dim(a)`; both operands must also
    /// be well-defined.
    pub(in crate::verify) fn verify_obj_at_index_well_defined(
        &mut self,
        x: &ObjAtIndex,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.obj,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &x.index,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;

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

        // A struct binding keeps its tuple view lazy until a projection is
        // actually used. Example: `q &Point` stores no `q $in cart(...)`,
        // while `q[1]` materializes that cart membership on demand.
        let default_struct_view = self.known_struct_carrier_for_obj(&x.obj);
        if let Some(struct_obj) = default_struct_view {
            let struct_membership: AtomicFact = InFact::new(
                (*x.obj).clone(),
                struct_obj.clone().into(),
                default_line_file(),
            )
            .into();
            let membership_result = self.verify_atomic_fact(&struct_membership, verify_state)?;
            if membership_result.is_success() {
                let field_types =
                    self.instantiated_struct_field_types(&struct_obj, verify_state)?;
                if field_types.len() > 1 {
                    let cart_membership: AtomicFact = InFact::new(
                        (*x.obj).clone(),
                        Cart::new(field_types).into(),
                        default_line_file(),
                    )
                    .into();
                    self.store_atomic_fact_without_well_defined_verified_and_infer(
                        cart_membership,
                    )?;
                }
            }
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

    pub(in crate::verify) fn store_fn_obj_cart_return_facts_if_available(
        &mut self,
        obj: &Obj,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        let Obj::FnObj(fn_obj) = obj else {
            return Ok(());
        };
        // Projected return facts re-enter this helper through index well-definedness.
        // Existing Cartesian metadata means an outer call is already populating them.
        if self.get_object_equal_to_tuple(obj).is_some() {
            return Ok(());
        }
        let Some(ret_set) = self.fn_obj_return_set_after_application(fn_obj)? else {
            return Ok(());
        };
        let Obj::Cart(cart) = ret_set else {
            return Ok(());
        };
        if cart.args.len() < 2 {
            return Ok(());
        }

        let obj_key = obj.to_string();
        self.store_tuple_obj_and_cart(&obj_key, None, Some(cart.clone()), line_file.clone());

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

    /// Mathematical contract: instantiate a callable's defined return carrier
    /// through every supplied argument group; intermediate carriers must remain
    /// function-like for a curried application to continue.
    pub fn fn_obj_return_set_after_application(
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
                let Some(body) = self.get_object_in_fn_set(&function_name_obj) else {
                    return Ok(None);
                };
                FnSetSpace::Set(FnSet::from_body(body.clone())?)
            }
        };

        for i in 0..fn_obj.body.len() {
            let ret_set = self.fn_set_return_set_after_args(&space, &fn_obj.body[i])?;
            if i == fn_obj.body.len() - 1 {
                return Ok(Some(ret_set));
            }
            space = self.fn_set_space_from_return_set_obj(ret_set)?;
        }

        Ok(None)
    }

    /// Mathematical contract: a dependent return carrier is interpreted after
    /// substituting the current argument values for its formal parameters.
    pub(in crate::verify) fn fn_set_return_set_after_args(
        &self,
        space: &FnSetSpace,
        args: &[Box<Obj>],
    ) -> Result<Obj, RuntimeError> {
        let args_as_obj: Vec<Obj> = args.iter().map(|arg| (**arg).clone()).collect();
        let param_to_arg_map = space
            .params()
            .param_defs_and_args_to_param_to_arg_map(&args_as_obj);
        self.inst_obj(
            &space.ret_set_obj(),
            &param_to_arg_map,
            SubstitutionMode::Exact,
        )
    }

    /// Mathematical contract: a curried return can be called again only when
    /// its carrier, a refined base carrier, or an equal representative denotes
    /// a function/sequence/matrix space.
    pub fn fn_set_space_from_return_set_obj(
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
                Obj::FiniteSeqSet(finite_seq) => {
                    return Ok(FnSetSpace::Set(
                        self.finite_seq_set_to_fn_set(finite_seq, default_line_file()),
                    ));
                }
                Obj::SeqSet(seq) => {
                    return Ok(FnSetSpace::Set(
                        self.seq_set_to_fn_set(seq, default_line_file()),
                    ));
                }
                Obj::MatrixSet(matrix) => {
                    return Ok(FnSetSpace::Set(
                        self.matrix_set_to_fn_set(matrix, default_line_file()),
                    ));
                }
                Obj::SetBuilder(set_builder) => candidates.push(*set_builder.param_set.clone()),
                _ => {}
            }

            // A refined carrier can be a named set builder over a function
            // space. Values returned in that carrier remain callable.
            // Example: `selected(i) $in {f fn(j I) V: P(f)}` permits
            // `selected(i)(j)`.
            if let Some(set_builder) = self.get_obj_equal_to_set_builder(&candidate) {
                candidates.push(set_builder.into());
            }
            candidates.extend(self.get_all_obj_representatives_equal_to_given(&candidate));
        }

        FnSetSpace::from_ret_obj(original_return_set)
    }

    /// Mathematical contract: the primitive standard set `Q+` is total.
    pub(in crate::verify) fn verify_q_pos_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    /// Mathematical contract: the primitive standard set `R+` is total.
    pub(in crate::verify) fn verify_r_pos_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    /// Mathematical contract: the primitive standard set `Q-` is total.
    pub(in crate::verify) fn verify_q_neg_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    /// Mathematical contract: the primitive standard set `Z-` is total.
    pub(in crate::verify) fn verify_z_neg_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    /// Mathematical contract: the primitive standard set `R-` is total.
    pub(in crate::verify) fn verify_r_neg_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    /// Mathematical contract: the primitive standard set `Q\\{0}` is total.
    pub(in crate::verify) fn verify_q_star_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    /// Mathematical contract: the primitive standard set `Z\\{0}` is total.
    pub(in crate::verify) fn verify_z_star_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    /// Mathematical contract: the primitive standard set `R\\{0}` is total.
    pub(in crate::verify) fn verify_r_star_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }

    /// Mathematical contract: the primitive standard set `C\{0}` is total.
    pub(in crate::verify) fn verify_c_star_well_defined(&self) -> Result<(), RuntimeError> {
        Ok(())
    }
}
