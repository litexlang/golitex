//! Iterated operators, reductions, ranges, and aggregates.

use crate::prelude::*;

impl Runtime {
    fn verify_integer_range_children_result(
        &mut self,
        start: &Obj,
        end: &Obj,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        for (argument_index, child) in [start, end].into_iter().enumerate() {
            steps.push_child(self.verify_child_obj_well_defined_result(
                child,
                verify_state,
                WellDefinedObjChildRole::ConstructorArgument { argument_index },
            )?);
            let integer: AtomicFact =
                InFact::new(child.clone(), StandardSet::Z.into(), default_line_file()).into();
            let result = self.verify_atomic_fact(&integer, verify_state)?;
            if result.is_unknown() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!("obj {child} is not in z")),
                )));
            }
            steps.push_fact_check(super::success_obj_fact_check(result)?);
        }
        Ok(steps)
    }

    pub(in crate::verify) fn verify_range_well_defined_result(
        &mut self,
        value: &Range,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_integer_range_children_result(&value.start, &value.end, verify_state)
    }

    pub(in crate::verify) fn verify_closed_range_well_defined_result(
        &mut self,
        value: &ClosedRange,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_integer_range_children_result(&value.start, &value.end, verify_state)
    }

    fn store_iteration_assumption_result(
        &mut self,
        proposition: QuantifierFreeFact,
    ) -> Result<SuccessStoreFactResult, RuntimeError> {
        let fact: Fact = proposition.clone().into();
        let mut infers =
            self.store_quantifier_free_fact_without_well_defined_verified_and_infer(proposition)?;
        self.attach_known_fact_ids_to_infer_result(&mut infers)?;
        let fact_id = self.known_fact_id_for_fact(&fact)?;
        Ok(SuccessStoreFactResult {
            fact,
            fact_id,
            infers,
        })
    }

    fn verify_iteration_scalar_return_result(
        &mut self,
        operation: &str,
        function: &Obj,
        verify_state: &ProofSearchState,
    ) -> Result<Option<SuccessVerifyIterationScalarReturnResult>, RuntimeError> {
        let Some(mut body) = self.get_fn_range_function_body(function) else {
            return Ok(None);
        };
        if body.set_bound_parameters.number_of_params() != 1 {
            return Ok(None);
        }
        let bindings = body.set_bound_parameters.collect_param_bindings();
        let rename_map = self.visible_binding_conflict_rename_map(&bindings)?;
        if !rename_map.is_empty() {
            body = self.alpha_rename_fn_set_body(&body, &rename_map)?;
        }
        self.run_in_local_env(|runtime| {
            let (parameter_carriers, parameters, domains) = runtime
                .verify_fn_binder_inputs_result(
                    &body.set_bound_parameters,
                    &body.dom_facts,
                    verify_state,
                )?;
            let return_carrier = runtime.verify_child_obj_well_defined_result(
                &body.ret_set,
                verify_state,
                WellDefinedObjChildRole::BinderReturnCarrier,
            )?;
            let subset: AtomicFact = SubsetFact::new(
                (*body.ret_set).clone(),
                StandardSet::C.into(),
                default_line_file(),
            )
            .into();
            let result = runtime.verify_atomic_fact(&subset, verify_state)?;
            if result.is_unknown() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "{operation}: iterand return set {} is not verified to be a subset of C",
                        body.ret_set
                    )),
                )));
            }
            Ok(SuccessVerifyIterationScalarReturnResult {
                parameter_carriers,
                parameters,
                domains,
                return_carrier,
                return_subset: super::success_obj_fact_check(result)?,
            })
        })
        .map(Some)
    }

    fn verify_iteration_coverage_result(
        &mut self,
        start: &Obj,
        end: &Obj,
        parameter_set: &Obj,
        verify_state: &ProofSearchState,
        operation: &str,
    ) -> Result<SuccessVerifyIterationCoverageResult, RuntimeError> {
        if let (Some(start_number), Some(end_number)) = (
            self.resolve_obj_to_number(start),
            self.resolve_obj_to_number(end),
        ) {
            let start_text = start_number.normalized_value.trim();
            let end_text = end_number.normalized_value.trim();
            if is_number_string_literally_integer_without_dot(start_text.to_string())
                && is_number_string_literally_integer_without_dot(end_text.to_string())
            {
                if let (Ok(start_integer), Ok(end_integer)) =
                    (start_text.parse::<i128>(), end_text.parse::<i128>())
                {
                    let mut checks = Vec::new();
                    for integer in start_integer..=end_integer {
                        let fact: AtomicFact = InFact::new(
                            Number::new(integer.to_string()).into(),
                            parameter_set.clone(),
                            default_line_file(),
                        )
                        .into();
                        let result = self.verify_atomic_fact(&fact, verify_state)?;
                        if result.is_unknown() {
                            return Err(RuntimeError::from(WellDefinedRuntimeError(
                                RuntimeErrorStruct::new_with_just_msg(format!(
                                    "{operation}: each integer in the closed range from {start} to {end} must belong to the index parameter's type; not satisfied at index {integer}"
                                )),
                            )));
                        }
                        checks.push(super::success_obj_fact_check(result)?);
                    }
                    return Ok(SuccessVerifyIterationCoverageResult::Enumerated(Box::new(
                        SuccessVerifyEnumeratedIterationCoverageResult { checks },
                    )));
                }
            }
        }

        let endpoint_requirements: Vec<(&Obj, StandardSet)> = match parameter_set {
            Obj::StandardSet(StandardSet::Z)
            | Obj::StandardSet(StandardSet::Q)
            | Obj::StandardSet(StandardSet::R)
            | Obj::StandardSet(StandardSet::C) => {
                return Ok(
                    SuccessVerifyIterationCoverageResult::UniversalIntegerCarrier(Box::new(
                        SuccessVerifyUniversalIntegerCarrierCoverageResult {
                            parameter_set: parameter_set.clone(),
                        },
                    )),
                );
            }
            Obj::StandardSet(StandardSet::N) => vec![(start, StandardSet::N)],
            Obj::StandardSet(StandardSet::NPos)
            | Obj::StandardSet(StandardSet::QPos)
            | Obj::StandardSet(StandardSet::RPos) => vec![(start, StandardSet::NPos)],
            Obj::StandardSet(StandardSet::ZNeg)
            | Obj::StandardSet(StandardSet::QNeg)
            | Obj::StandardSet(StandardSet::RNeg) => vec![(end, StandardSet::ZNeg)],
            Obj::StandardSet(StandardSet::ZStar)
            | Obj::StandardSet(StandardSet::QStar)
            | Obj::StandardSet(StandardSet::RStar)
            | Obj::StandardSet(StandardSet::CStar) => {
                vec![(start, StandardSet::NPos), (end, StandardSet::ZNeg)]
            }
            _ => Vec::new(),
        };
        for (endpoint, required_set) in endpoint_requirements {
            let fact: AtomicFact =
                InFact::new(endpoint.clone(), required_set.into(), default_line_file()).into();
            let result = self.verify_atomic_fact(&fact, verify_state)?;
            if result.is_success() {
                return Ok(SuccessVerifyIterationCoverageResult::Endpoint(Box::new(
                    SuccessVerifyEndpointIterationCoverageResult {
                        check: super::success_obj_fact_check(result)?,
                    },
                )));
            }
        }
        let interval: Obj = ClosedRange::new(start.clone(), end.clone()).into();
        let subset: AtomicFact =
            SubsetFact::new(interval, parameter_set.clone(), default_line_file()).into();
        let result = self.verify_atomic_fact(&subset, verify_state)?;
        if result.is_success() {
            return Ok(SuccessVerifyIterationCoverageResult::IntervalSubset(
                Box::new(SuccessVerifyIntervalSubsetCoverageResult {
                    check: super::success_obj_fact_check(result)?,
                }),
            ));
        }
        Err(RuntimeError::from(WellDefinedRuntimeError(
            RuntimeErrorStruct::new_with_just_msg(format!(
                "{operation}: cannot verify that every integer from {start} to {end} belongs to the iterand domain {parameter_set}"
            )),
        )))
    }

    fn verify_iteration_interval_body_result(
        &mut self,
        body: &FnSetBody,
        anonymous_body: Option<&Obj>,
        start: &Obj,
        end: &Obj,
        verify_state: &ProofSearchState,
        operation: &str,
    ) -> Result<SuccessVerifyIterationIntervalResult, RuntimeError> {
        if body.set_bound_parameters.number_of_params() != 1 {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{operation}: the function in the function set must be unary (one index)"
                )),
            )));
        }
        let parameter_binding = body.set_bound_parameters.collect_param_bindings()[0].clone();
        let parameter_set = Self::unary_param_set_from_params_def(
            &body.set_bound_parameters,
            parameter_binding.name(),
        )
        .ok_or_else(|| {
            RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{operation}: could not find index parameter in set_bound_parameters"
                )),
            ))
        })?;
        let coverage = self.verify_iteration_coverage_result(
            start,
            end,
            &parameter_set,
            verify_state,
            operation,
        )?;

        self.run_in_local_env(|runtime| {
            let (parameter_carriers, parameters, _) = runtime
                .verify_fn_binder_inputs_result(
                    &body.set_bound_parameters,
                    &[],
                    verify_state,
                )
                .map_err(|error| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!(
                                "{operation}: could not bind index parameter in local well-defined check"
                            ),
                            error,
                        ),
                    ))
                })?;
            let parameter =
                obj_for_bound_param_in_scope(&parameter_binding);
            let lower = QuantifierFreeFact::AtomicFact(
                LessEqualFact::new(start.clone(), parameter.clone(), default_line_file()).into(),
            );
            let upper = QuantifierFreeFact::AtomicFact(
                LessEqualFact::new(parameter, end.clone(), default_line_file()).into(),
            );
            let lower_bound = runtime
                .store_iteration_assumption_result(lower)
                .map_err(|error| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!("{operation}: could not add lower bound in local check"),
                            error,
                        ),
                    ))
                })?;
            let upper_bound = runtime
                .store_iteration_assumption_result(upper)
                .map_err(|error| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!("{operation}: could not add upper bound in local check"),
                            error,
                        ),
                    ))
                })?;

            let mut domains = Vec::with_capacity(body.dom_facts.len());
            for domain in &body.dom_facts {
                let result = runtime
                    .verify_quantifier_free_fact(domain, verify_state)
                    .map_err(|error| {
                        RuntimeError::from(WellDefinedRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_cause(
                                format!("{operation}: function set domain check failed"),
                                error,
                            ),
                        ))
                    })?;
                if !result.is_success() {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "{operation}: cannot verify function domain condition {domain} on the whole integer range"
                        )),
                    )));
                }
                let proof = super::success_obj_fact_check(result)?;
                let store = runtime
                    .store_iteration_assumption_result(domain.clone())
                    .map_err(|error| {
                        RuntimeError::from(WellDefinedRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_cause(
                                format!(
                                    "{operation}: could not store verified function domain condition"
                                ),
                                error,
                            ),
                        ))
                    })?;
                domains.push(SuccessVerifyIterationDomainResult {
                    proposition: proof.expected_proposition,
                    verification: proof.verification,
                    store,
                });
            }

            let return_carrier = runtime
                .verify_child_obj_well_defined_result(
                    &body.ret_set,
                    verify_state,
                    WellDefinedObjChildRole::BinderReturnCarrier,
                )
                .map_err(|error| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!(
                                "{operation}: return set not well-defined on the integer range"
                            ),
                            error,
                        ),
                    ))
                })?;

            let (body_result, body_membership) = if let Some(anonymous_body) = anonymous_body {
                let body_result = runtime
                    .verify_child_obj_well_defined_result(
                        anonymous_body,
                        verify_state,
                        WellDefinedObjChildRole::BinderBody,
                    )
                    .map_err(|error| {
                        RuntimeError::from(WellDefinedRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_cause(
                                format!(
                                    "{operation}: expression body not well-defined on the integer range"
                                ),
                                error,
                            ),
                        ))
                    })?;
                let membership: AtomicFact = InFact::new(
                    anonymous_body.clone(),
                    (*body.ret_set).clone(),
                    default_line_file(),
                )
                .into();
                let result = runtime.verify_atomic_fact(&membership, verify_state)?;
                if result.is_unknown() {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "{operation}: iterand body {anonymous_body} is not verified to belong to defined return set {}",
                            body.ret_set
                        )),
                    )));
                }
                let parent: Obj = AnonymousFn::new(
                    body.set_bound_parameters.clone(),
                    body.dom_facts.clone(),
                    (*body.ret_set).clone(),
                    anonymous_body.clone(),
                )?
                .into();
                let membership = super::success_obj_target_requirement(
                    parent,
                    WellDefinednessRequirementRole::AnonymousFunctionBodyMembership,
                    result,
                )?;
                (Some(body_result), Some(membership))
            } else {
                (None, None)
            };
            Ok(SuccessVerifyIterationIntervalResult {
                parameter_set: parameter_set.clone(),
                coverage,
                parameter_carriers,
                parameters,
                lower_bound,
                upper_bound,
                domains,
                return_carrier,
                body: body_result,
                body_membership,
            })
        })
    }

    fn verify_iteration_interval_result(
        &mut self,
        function: &Obj,
        start: &Obj,
        end: &Obj,
        verify_state: &ProofSearchState,
        operation: &str,
    ) -> Result<SuccessVerifyIterationIntervalResult, RuntimeError> {
        if let Some(anonymous) = Self::summand_as_unary_anonymous_fn(function) {
            return self.verify_iteration_interval_body_result(
                &anonymous.body,
                Some(&anonymous.equal_to),
                start,
                end,
                verify_state,
                operation,
            );
        }
        if let Obj::FnObj(application) = function {
            if !application.body.is_empty() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "{operation}: expected a bare function as summand, not a function application"
                    )),
                )));
            }
            let function_name: Obj = (*application.head).clone().into();
            let body = self.get_object_in_fn_set(&function_name).ok_or_else(|| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "{operation}: summand must be a unary anonymous function, or a name with a stored function set; got {function}"
                    )),
                ))
            })?;
            return self.verify_iteration_interval_body_result(
                &body,
                None,
                start,
                end,
                verify_state,
                operation,
            );
        }
        if let Some(body) = self.get_cloned_object_in_fn_set(function) {
            return self.verify_iteration_interval_body_result(
                &body,
                None,
                start,
                end,
                verify_state,
                operation,
            );
        }
        Err(RuntimeError::from(WellDefinedRuntimeError(
            RuntimeErrorStruct::new_with_just_msg(format!(
                "{operation}: summand must be a unary anonymous function, or a defined unary function in a function set; got {function}"
            )),
        )))
    }

    fn verify_range_iteration_result(
        &mut self,
        start: &Obj,
        end: &Obj,
        function: &Obj,
        operation: &str,
        range_error: String,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = self.verify_integer_range_children_result(start, end, verify_state)?;
        let ordered: AtomicFact =
            LessEqualFact::new(start.clone(), end.clone(), default_line_file()).into();
        let ordered_result = self.verify_atomic_fact(&ordered, verify_state)?;
        if ordered_result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(range_error),
            )));
        }
        steps.push_fact_check(super::success_obj_fact_check(ordered_result)?);
        steps.push_child(self.verify_child_obj_well_defined_result(
            function,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 2 },
        )?);
        let scalar_return =
            self.verify_iteration_scalar_return_result(operation, function, verify_state)?;
        let interval =
            self.verify_iteration_interval_result(function, start, end, verify_state, operation)?;
        steps.binder = Some(Box::new(
            SuccessVerifyBinderObjectWellDefinedResult::Iteration(Box::new(
                SuccessVerifyIterationWellDefinedResult {
                    operation: operation.to_string(),
                    scalar_return: scalar_return.map(Box::new),
                    interval: Box::new(interval),
                },
            )),
        ));
        Ok(steps)
    }

    pub(in crate::verify) fn verify_sum_obj_well_defined_result(
        &mut self,
        value: &Sum,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_range_iteration_result(
            &value.start,
            &value.end,
            &value.func,
            "sum",
            "sum: cannot verify start <= end for the summation range".to_string(),
            verify_state,
        )
    }

    pub(in crate::verify) fn verify_product_obj_well_defined_result(
        &mut self,
        value: &Product,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_range_iteration_result(
            &value.start,
            &value.end,
            &value.func,
            "product",
            "product: cannot verify start <= end for the product range".to_string(),
            verify_state,
        )
    }

    fn verify_finite_aggregate_body_memberships_result(
        &mut self,
        operation: &str,
        list: &ListSet,
        function: &Obj,
        verify_state: &ProofSearchState,
    ) -> Result<Vec<SuccessVerifyFactForObjWellDefinedResult>, RuntimeError> {
        let Some(anonymous) = Self::summand_as_unary_anonymous_fn(function) else {
            return Ok(Vec::new());
        };
        if list.list.is_empty() {
            self.verify_symbolic_finite_set_anonymous_iterand_return(
                operation,
                function,
                verify_state,
            )?;
            return Ok(Vec::new());
        }
        let mut checks = Vec::with_capacity(list.list.len());
        for element in &list.list {
            let arguments = vec![element.as_ref().clone()];
            let substitutions = SetBoundParameterGroup::param_defs_and_args_to_param_to_arg_map(
                &anonymous.body.set_bound_parameters,
                &arguments,
            );
            let body =
                self.inst_obj(&anonymous.equal_to, &substitutions, SubstitutionMode::Exact)?;
            let return_set = self.inst_obj(
                &anonymous.body.ret_set,
                &substitutions,
                SubstitutionMode::Exact,
            )?;
            let membership: AtomicFact =
                InFact::new(body.clone(), return_set.clone(), default_line_file()).into();
            let result = self.verify_atomic_fact(&membership, verify_state)?;
            if result.is_unknown() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "{operation}: iterand body {body} is not verified to belong to defined return set {return_set} at {element}"
                    )),
                )));
            }
            checks.push(super::success_obj_fact_check(result)?);
        }
        Ok(checks)
    }

    fn verify_finite_aggregate_mode_result(
        &mut self,
        operation: &str,
        set: &Obj,
        function: &Obj,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyFiniteAggregateModeResult, RuntimeError> {
        if let Obj::ListSet(list) = set {
            let body = self.get_fn_range_function_body(function).ok_or_else(|| {
                let role = if operation == "finite_set_sum" {
                    "summand"
                } else {
                    "factor"
                };
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "{operation}: {role} must be a unary function; got {function}"
                    )),
                ))
            })?;
            if body.set_bound_parameters.number_of_params() != 1 {
                let role = if operation == "finite_set_sum" {
                    "summand"
                } else {
                    "factor"
                };
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "{operation}: {role} must be unary (one parameter)"
                    )),
                )));
            }
            let body_memberships = self.verify_finite_aggregate_body_memberships_result(
                operation,
                list,
                function,
                verify_state,
            )?;
            let mut applications = Vec::with_capacity(list.list.len());
            for element in &list.list {
                let application = if operation == "finite_set_sum" {
                    self.finite_set_sum_application_obj(function, element)?
                } else {
                    self.finite_set_product_application_obj(function, element)?
                };
                let dependency_index = applications.len();
                applications.push(
                    self.verify_child_obj_well_defined_result(
                        &application,
                        verify_state,
                        WellDefinedObjChildRole::VerificationDependency { dependency_index },
                    )
                    .map_err(|error| {
                        RuntimeError::from(WellDefinedRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_cause(
                                format!(
                                    "{operation}: iterand {function} is not defined at {element}"
                                ),
                                error,
                            ),
                        ))
                    })?,
                );
            }
            return Ok(SuccessVerifyFiniteAggregateModeResult::Elements(Box::new(
                SuccessVerifyFiniteAggregateElementsResult {
                    body_memberships,
                    applications,
                },
            )));
        }

        if let Obj::ClosedRange(range) = set {
            let empty: AtomicFact =
                NotIsNonemptySetFact::new(set.clone(), default_line_file()).into();
            let result = self.verify_atomic_fact(&empty, verify_state)?;
            if result.is_success() {
                self.verify_empty_finite_set_aggregate_has_unary_iterand(operation, function)?;
                return Ok(SuccessVerifyFiniteAggregateModeResult::Empty(Box::new(
                    SuccessVerifyEmptyFiniteAggregateResult {
                        empty_set: super::success_obj_fact_check(result)?,
                    },
                )));
            }
            let aggregate: Obj = if operation == "finite_set_sum" {
                Sum::new(
                    range.start.as_ref().clone(),
                    range.end.as_ref().clone(),
                    function.clone(),
                )
                .into()
            } else {
                Product::new(
                    range.start.as_ref().clone(),
                    range.end.as_ref().clone(),
                    function.clone(),
                )
                .into()
            };
            let aggregate_dependency = self
                .verify_child_obj_well_defined_result(
                    &aggregate,
                    verify_state,
                    WellDefinedObjChildRole::VerificationDependency {
                        dependency_index: 0,
                    },
                )
                .map_err(|error| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!("{operation}: closed-range aggregate is not well-defined"),
                            error,
                        ),
                    ))
                })?;
            return Ok(SuccessVerifyFiniteAggregateModeResult::ClosedRange(
                Box::new(SuccessVerifyFiniteAggregateClosedRangeResult {
                    aggregate_dependency,
                }),
            ));
        }

        self.verify_finite_set_iterand_has_exact_domain(operation, function, set)
            .map_err(|error| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!("{operation}: cannot verify that {function} is defined on {set}"),
                        error,
                    ),
                ))
            })?;
        self.verify_symbolic_finite_set_anonymous_iterand_return(
            operation,
            function,
            verify_state,
        )?;
        Ok(SuccessVerifyFiniteAggregateModeResult::Symbolic(Box::new(
            SuccessVerifySymbolicFiniteAggregateResult {
                exact_domain: set.clone(),
            },
        )))
    }

    fn verify_finite_aggregate_result(
        &mut self,
        set: &Obj,
        function: &Obj,
        operation: &str,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        steps.push_child(self.verify_child_obj_well_defined_result(
            set,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?);
        let finite: AtomicFact = IsFiniteSetFact::new(set.clone(), default_line_file()).into();
        let result = self.verify_atomic_fact(&finite, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{operation}: set {set} is not a finite set"
                )),
            )));
        }
        steps.push_fact_check(super::success_obj_fact_check(result)?);
        steps.push_child(self.verify_child_obj_well_defined_result(
            function,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?);
        let scalar_return =
            self.verify_iteration_scalar_return_result(operation, function, verify_state)?;
        let mode =
            self.verify_finite_aggregate_mode_result(operation, set, function, verify_state)?;
        steps.binder = Some(Box::new(
            SuccessVerifyBinderObjectWellDefinedResult::FiniteAggregate(Box::new(
                SuccessVerifyFiniteAggregateWellDefinedResult {
                    operation: operation.to_string(),
                    scalar_return: scalar_return.map(Box::new),
                    mode,
                },
            )),
        ));
        Ok(steps)
    }

    pub(in crate::verify) fn verify_finite_set_sum_obj_well_defined_result(
        &mut self,
        value: &SumOfFiniteSet,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_finite_aggregate_result(&value.set, &value.func, "finite_set_sum", verify_state)
    }

    pub(in crate::verify) fn verify_finite_set_product_obj_well_defined_result(
        &mut self,
        value: &ProductOfFiniteSet,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_finite_aggregate_result(
            &value.set,
            &value.func,
            "finite_set_product",
            verify_state,
        )
    }

    fn verify_reduce_operation_signature_result(
        &self,
        operation: &Obj,
        operation_name: &str,
    ) -> Result<SuccessVerifyReduceOperationSignatureResult, RuntimeError> {
        let body = self.get_fn_range_function_body(operation).ok_or_else(|| {
            RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{operation_name}: operation {operation} must have an unconditional homogeneous signature fn(x, y T) T"
                )),
            ))
        })?;
        if body.set_bound_parameters.number_of_params() != 2 || !body.dom_facts.is_empty() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{operation_name}: operation {operation} must have an unconditional homogeneous signature fn(x, y T) T"
                )),
            )));
        }
        let parameter_carriers = body
            .set_bound_parameters
            .iter()
            .flat_map(|group| {
                group
                    .params
                    .iter()
                    .map(|_| group.set_obj().clone())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let [left_parameter_carrier, right_parameter_carrier] = parameter_carriers.as_slice()
        else {
            unreachable!("two parameters were checked above")
        };
        if obj_equality_key(left_parameter_carrier) != obj_equality_key(right_parameter_carrier)
            || obj_equality_key(left_parameter_carrier) != obj_equality_key(body.ret_set.as_ref())
        {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{operation_name}: operation {operation} must have an unconditional homogeneous signature fn(x, y T) T"
                )),
            )));
        }
        Ok(SuccessVerifyReduceOperationSignatureResult {
            left_parameter_carrier: left_parameter_carrier.clone(),
            right_parameter_carrier: right_parameter_carrier.clone(),
            return_carrier: body.ret_set.as_ref().clone(),
        })
    }

    fn verify_reduce_iterand_return_carrier_result(
        &self,
        function: &Obj,
        carrier: &Obj,
        operation_name: &str,
    ) -> Result<Obj, RuntimeError> {
        let body = self.get_fn_range_function_body(function).ok_or_else(|| {
            RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{operation_name}: iterand {function} must be a unary function with a known function set"
                )),
            ))
        })?;
        if body.set_bound_parameters.number_of_params() != 1 {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{operation_name}: iterand {function} must be unary"
                )),
            )));
        }
        if obj_equality_key(body.ret_set.as_ref()) != obj_equality_key(carrier) {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{operation_name}: iterand return set {} must equal operation carrier {carrier}",
                    body.ret_set
                )),
            )));
        }
        Ok(body.ret_set.as_ref().clone())
    }

    fn verify_reduce_seed_membership_result(
        &mut self,
        seed: &Obj,
        carrier: &Obj,
        verify_state: &ProofSearchState,
        operation_name: &str,
    ) -> Result<SuccessVerifyFactForObjWellDefinedResult, RuntimeError> {
        let seed_fact: AtomicFact =
            InFact::new(seed.clone(), carrier.clone(), default_line_file()).into();
        let result = self.verify_atomic_fact(&seed_fact, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{operation_name}: seed {seed} is not verified to belong to operation carrier {carrier}"
                )),
            )));
        }
        super::success_obj_fact_check(result)
    }

    fn verify_reduce_interval_mode_result(
        &mut self,
        function: &Obj,
        start: &Obj,
        end: &Obj,
        verify_state: &ProofSearchState,
        operation_name: &str,
    ) -> Result<SuccessVerifyReduceModeResult, RuntimeError> {
        let empty_fact: AtomicFact =
            LessFact::new(end.clone(), start.clone(), default_line_file()).into();
        let empty_result = self.verify_atomic_fact(&empty_fact, verify_state)?;
        if empty_result.is_success() {
            self.verify_empty_finite_set_aggregate_has_unary_iterand(operation_name, function)?;
            return Ok(SuccessVerifyReduceModeResult::Empty(Box::new(
                SuccessVerifyEmptyReduceResult {
                    empty_range_or_set: super::success_obj_fact_check(empty_result)?,
                },
            )));
        }
        let interval = self.verify_iteration_interval_result(
            function,
            start,
            end,
            verify_state,
            operation_name,
        )?;
        Ok(SuccessVerifyReduceModeResult::Interval(Box::new(
            SuccessVerifyIntervalReduceResult {
                interval: Box::new(interval),
            },
        )))
    }

    pub(in crate::verify) fn verify_reduce_obj_well_defined_result(
        &mut self,
        value: &Reduce,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps =
            self.verify_integer_range_children_result(&value.start, &value.end, verify_state)?;
        for (argument_index, child) in [value.func.as_ref(), value.op.as_ref(), value.seed.as_ref()]
            .into_iter()
            .enumerate()
        {
            steps.push_child(self.verify_child_obj_well_defined_result(
                child,
                verify_state,
                WellDefinedObjChildRole::ConstructorArgument {
                    argument_index: argument_index + 2,
                },
            )?);
        }
        let signature =
            self.verify_reduce_operation_signature_result(value.op.as_ref(), "reduce")?;
        let carrier = signature.return_carrier.clone();
        let iterand_return_carrier = self.verify_reduce_iterand_return_carrier_result(
            value.func.as_ref(),
            &carrier,
            "reduce",
        )?;
        let seed_membership = self.verify_reduce_seed_membership_result(
            value.seed.as_ref(),
            &carrier,
            verify_state,
            "reduce",
        )?;
        let mode = self.verify_reduce_interval_mode_result(
            value.func.as_ref(),
            value.start.as_ref(),
            value.end.as_ref(),
            verify_state,
            "reduce",
        )?;
        steps.binder = Some(Box::new(
            SuccessVerifyBinderObjectWellDefinedResult::Reduce(Box::new(
                SuccessVerifyReduceWellDefinedResult {
                    operation: "reduce".to_string(),
                    signature,
                    iterand_return_carrier,
                    seed_membership,
                    operation_laws: None,
                    mode,
                },
            )),
        ));
        Ok(steps)
    }

    fn bind_reduce_law_parameter_result(
        &mut self,
        binding: &SymbolBinding,
        parameter: Obj,
        carrier: &Obj,
        parameter_index: usize,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyBinderPremiseResult, RuntimeError> {
        self.store_parameter_binding(binding, BindingScope::LocalBinder)?;
        let proposition: Fact = InFact::new(parameter, carrier.clone(), default_line_file()).into();
        let well_definedness = self.verify_fact_well_defined_result(&proposition, verify_state)?;
        let Fact::AtomicFact(atomic) = proposition.clone() else {
            unreachable!("reduce-law parameter membership is atomic")
        };
        let mut infers = self
            .store_atomic_fact_without_well_defined_verified_and_infer_with_reason(
                atomic,
                InferReason::ParameterDefinition.store_reason(),
            )?;
        self.attach_known_fact_ids_to_infer_result(&mut infers)?;
        Ok(SuccessVerifyBinderPremiseResult::new(
            WellDefinedBinderPremiseRole::ParameterMembership {
                parameter_group_index: 0,
                parameter_index,
            },
            Some(binding.id()),
            proposition,
            well_definedness,
            infers,
        ))
    }

    fn verify_finite_set_reduce_operation_laws_result(
        &mut self,
        operation: &Obj,
        carrier: &Obj,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyFiniteReduceOperationLawsResult, RuntimeError> {
        let operation = operation.clone();
        let carrier = carrier.clone();
        self.run_in_local_env(|runtime| {
            let parameter_carrier = runtime.verify_child_obj_well_defined_result(
                &carrier,
                verify_state,
                WellDefinedObjChildRole::BinderParameterCarrier {
                    parameter_group_index: 0,
                },
            )?;
            let x_name = runtime.generate_random_unused_name();
            let y_name = runtime.generate_random_unused_name();
            let z_name = runtime.generate_random_unused_name();
            let (x_binding, x) = runtime.fresh_bound_param(x_name)?;
            let (y_binding, y) = runtime.fresh_bound_param(y_name)?;
            let (z_binding, z) = runtime.fresh_bound_param(z_name)?;
            let parameters = vec![
                runtime.bind_reduce_law_parameter_result(
                    &x_binding,
                    x.clone(),
                    &carrier,
                    0,
                    verify_state,
                )?,
                runtime.bind_reduce_law_parameter_result(
                    &y_binding,
                    y.clone(),
                    &carrier,
                    1,
                    verify_state,
                )?,
                runtime.bind_reduce_law_parameter_result(
                    &z_binding,
                    z.clone(),
                    &carrier,
                    2,
                    verify_state,
                )?,
            ];

            let xy = runtime
                .instantiate_reduce_function_at(&operation, &[x.clone(), y.clone()])?
                .ok_or_else(|| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(
                            "finite_set_reduce: could not instantiate operation".to_string(),
                        ),
                    ))
                })?;
            let yz = runtime
                .instantiate_reduce_function_at(&operation, &[y.clone(), z.clone()])?
                .ok_or_else(|| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(
                            "finite_set_reduce: could not instantiate operation".to_string(),
                        ),
                    ))
                })?;
            let left_assoc = runtime
                .instantiate_reduce_function_at(&operation, &[xy, z.clone()])?
                .ok_or_else(|| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(
                            "finite_set_reduce: could not instantiate nested operation"
                                .to_string(),
                        ),
                    ))
                })?;
            let right_assoc = runtime
                .instantiate_reduce_function_at(&operation, &[x.clone(), yz])?
                .ok_or_else(|| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(
                            "finite_set_reduce: could not instantiate nested operation"
                                .to_string(),
                        ),
                    ))
                })?;
            let law_state = ProofSearchState::initial();
            let associativity_fact: AtomicFact =
                EqualFact::new(left_assoc, right_assoc, default_line_file()).into();
            let associativity_result =
                runtime.verify_atomic_fact(&associativity_fact, &law_state)?;
            if associativity_result.is_unknown() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "finite_set_reduce: operation {operation} is not verified associative on {carrier}"
                    )),
                )));
            }
            let associativity = super::success_obj_fact_check(associativity_result)?;

            let xy = runtime
                .instantiate_reduce_function_at(&operation, &[x.clone(), y.clone()])?
                .ok_or_else(|| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(
                            "finite_set_reduce: could not instantiate operation".to_string(),
                        ),
                    ))
                })?;
            let yx = runtime
                .instantiate_reduce_function_at(&operation, &[y, x])?
                .ok_or_else(|| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(
                            "finite_set_reduce: could not instantiate operation".to_string(),
                        ),
                    ))
                })?;
            let commutativity_fact: AtomicFact =
                EqualFact::new(xy, yx, default_line_file()).into();
            let commutativity_result =
                runtime.verify_atomic_fact(&commutativity_fact, &law_state)?;
            if commutativity_result.is_unknown() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "finite_set_reduce: operation {operation} is not verified commutative on {carrier}"
                    )),
                )));
            }
            let commutativity = super::success_obj_fact_check(commutativity_result)?;
            Ok(SuccessVerifyFiniteReduceOperationLawsResult {
                parameter_carrier,
                parameters,
                associativity,
                commutativity,
            })
        })
    }

    fn verify_finite_reduce_domain_coverage_result(
        &mut self,
        function: &Obj,
        set: &Obj,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyFiniteReduceDomainCoverageResult, RuntimeError> {
        let body = self.get_fn_range_function_body(function).ok_or_else(|| {
            RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "finite_set_reduce: {function} must be a unary function with a known function set"
                )),
            ))
        })?;
        if body.set_bound_parameters.number_of_params() != 1 || !body.dom_facts.is_empty() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "finite_set_reduce: {function} must be an unconditional unary function; use an explicit restriction for a conditional domain"
                )),
            )));
        }
        let binding = body.set_bound_parameters.collect_param_bindings();
        let binding = binding.first().ok_or_else(|| {
            RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(
                    "finite_set_reduce: cannot resolve the iterand domain".to_string(),
                ),
            ))
        })?;
        let domain =
            Self::unary_param_set_from_params_def(&body.set_bound_parameters, binding.name())
                .ok_or_else(|| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(
                            "finite_set_reduce: cannot resolve the iterand domain".to_string(),
                        ),
                    ))
                })?;
        if obj_equality_key(&domain) == obj_equality_key(set) {
            return Ok(SuccessVerifyFiniteReduceDomainCoverageResult::Exact(
                Box::new(SuccessVerifyExactFiniteReduceDomainResult {
                    aggregate_set: set.clone(),
                    iterand_domain: domain,
                }),
            ));
        }
        let coverage: AtomicFact =
            SubsetFact::new(set.clone(), domain.clone(), default_line_file()).into();
        let result = self.verify_atomic_fact(&coverage, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "finite_set_reduce: cannot verify aggregate set {set} is contained in iterand domain {domain}"
                )),
            )));
        }
        Ok(SuccessVerifyFiniteReduceDomainCoverageResult::Subset(
            Box::new(SuccessVerifySubsetFiniteReduceDomainResult {
                aggregate_set: set.clone(),
                iterand_domain: domain,
                subset: super::success_obj_fact_check(result)?,
            }),
        ))
    }

    fn verify_finite_reduce_mode_result(
        &mut self,
        set: &Obj,
        function: &Obj,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyReduceModeResult, RuntimeError> {
        let empty_fact: AtomicFact =
            NotIsNonemptySetFact::new(set.clone(), default_line_file()).into();
        let empty_result = self.verify_atomic_fact(&empty_fact, verify_state)?;
        if empty_result.is_success() {
            self.verify_empty_finite_set_aggregate_has_unary_iterand(
                "finite_set_reduce",
                function,
            )?;
            return Ok(SuccessVerifyReduceModeResult::Empty(Box::new(
                SuccessVerifyEmptyReduceResult {
                    empty_range_or_set: super::success_obj_fact_check(empty_result)?,
                },
            )));
        }
        if let Obj::ListSet(list_set) = set {
            let body_memberships = self.verify_finite_aggregate_body_memberships_result(
                "finite_set_reduce",
                list_set,
                function,
                verify_state,
            )?;
            let mut applications = Vec::with_capacity(list_set.list.len());
            for element in &list_set.list {
                let application = self.reduce_callable_application_obj(
                    function,
                    &[element.as_ref().clone()],
                    "finite_set_reduce",
                )?;
                let dependency_index = applications.len();
                applications.push(
                    self.verify_child_obj_well_defined_result(
                        &application,
                        verify_state,
                        WellDefinedObjChildRole::VerificationDependency { dependency_index },
                    )
                    .map_err(|error| {
                        RuntimeError::from(WellDefinedRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_cause(
                                format!(
                                    "finite_set_reduce: iterand {function} is not defined at {element}"
                                ),
                                error,
                            ),
                        ))
                    })?,
                );
            }
            return Ok(SuccessVerifyReduceModeResult::Elements(Box::new(
                SuccessVerifyElementwiseReduceResult {
                    body_memberships,
                    applications,
                },
            )));
        }
        if let Obj::ClosedRange(range) = set {
            let interval = self.verify_iteration_interval_result(
                function,
                range.start.as_ref(),
                range.end.as_ref(),
                verify_state,
                "finite_set_reduce",
            )?;
            return Ok(SuccessVerifyReduceModeResult::Interval(Box::new(
                SuccessVerifyIntervalReduceResult {
                    interval: Box::new(interval),
                },
            )));
        }
        let coverage =
            self.verify_finite_reduce_domain_coverage_result(function, set, verify_state)?;
        self.verify_symbolic_finite_set_anonymous_iterand_return(
            "finite_set_reduce",
            function,
            verify_state,
        )?;
        Ok(SuccessVerifyReduceModeResult::Symbolic(Box::new(
            SuccessVerifySymbolicReduceResult { coverage },
        )))
    }

    pub(in crate::verify) fn verify_finite_set_reduce_obj_well_defined_result(
        &mut self,
        value: &FiniteSetReduce,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        for (argument_index, child) in [
            value.set.as_ref(),
            value.func.as_ref(),
            value.op.as_ref(),
            value.seed.as_ref(),
        ]
        .into_iter()
        .enumerate()
        {
            steps.push_child(self.verify_child_obj_well_defined_result(
                child,
                verify_state,
                WellDefinedObjChildRole::ConstructorArgument { argument_index },
            )?);
        }
        let finite_fact: AtomicFact =
            IsFiniteSetFact::new(value.set.as_ref().clone(), default_line_file()).into();
        let finite_result = self.verify_atomic_fact(&finite_fact, verify_state)?;
        if finite_result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "finite_set_reduce: set {} is not verified to be finite",
                    value.set
                )),
            )));
        }
        steps.push_fact_check(super::success_obj_fact_check(finite_result)?);
        let signature =
            self.verify_reduce_operation_signature_result(value.op.as_ref(), "finite_set_reduce")?;
        let carrier = signature.return_carrier.clone();
        let iterand_return_carrier = self.verify_reduce_iterand_return_carrier_result(
            value.func.as_ref(),
            &carrier,
            "finite_set_reduce",
        )?;
        let seed_membership = self.verify_reduce_seed_membership_result(
            value.seed.as_ref(),
            &carrier,
            verify_state,
            "finite_set_reduce",
        )?;
        let operation_laws = self.verify_finite_set_reduce_operation_laws_result(
            value.op.as_ref(),
            &carrier,
            verify_state,
        )?;
        let mode = self.verify_finite_reduce_mode_result(
            value.set.as_ref(),
            value.func.as_ref(),
            verify_state,
        )?;
        steps.binder = Some(Box::new(
            SuccessVerifyBinderObjectWellDefinedResult::Reduce(Box::new(
                SuccessVerifyReduceWellDefinedResult {
                    operation: "finite_set_reduce".to_string(),
                    signature,
                    iterand_return_carrier,
                    seed_membership,
                    operation_laws: Some(Box::new(operation_laws)),
                    mode,
                },
            )),
        ));
        Ok(steps)
    }

    /// Mathematical contract: `reduce(a,b,f,op,seed)` is an ascending left
    /// fold over the closed integer interval. It has the homogeneous carrier
    /// `T` defined by `op : T x T -> T`; `f` returns `T`, and `seed` is in
    /// `T`. Unlike the legacy `sum`/`product`, an empty interval is valid.
    pub(in crate::verify) fn verify_reduce_obj_well_defined(
        &mut self,
        x: &Reduce,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.start,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &x.end,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
        self.require_obj_in_z(&x.start, verify_state)?;
        self.require_obj_in_z(&x.end, verify_state)?;
        self.verify_child_obj_well_defined_and_store_cache(
            &x.func,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 2 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &x.op,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 3 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &x.seed,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 4 },
        )?;

        let carrier = self.verify_reduce_operation_signature(x.op.as_ref(), "reduce")?;
        self.verify_reduce_iterand_return_carrier(x.func.as_ref(), &carrier, "reduce")?;
        self.require_reduce_seed_in_carrier(x.seed.as_ref(), &carrier, verify_state, "reduce")?;

        let empty_fact: AtomicFact = LessFact::new(
            x.end.as_ref().clone(),
            x.start.as_ref().clone(),
            default_line_file(),
        )
        .into();
        if self
            .verify_atomic_fact(&empty_fact, verify_state)?
            .is_success()
        {
            return self
                .verify_empty_finite_set_aggregate_has_unary_iterand("reduce", x.func.as_ref());
        }

        self.verify_iterated_op_summand_under_integer_index_interval(
            x.func.as_ref(),
            x.start.as_ref(),
            x.end.as_ref(),
            verify_state,
            "reduce",
        )
    }

    /// Mathematical contract: `finite_set_reduce(S,f,op,seed)` is an
    /// order-independent fold. In addition to the homogeneous carrier checks
    /// used by `reduce`, `op` must be associative and commutative on that
    /// carrier; this prevents display order of a set literal becoming semantic.
    pub(in crate::verify) fn verify_finite_set_reduce_obj_well_defined(
        &mut self,
        x: &FiniteSetReduce,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.set,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        let finite_fact: AtomicFact =
            IsFiniteSetFact::new(x.set.as_ref().clone(), default_line_file()).into();
        if self
            .verify_atomic_fact(&finite_fact, verify_state)?
            .is_unknown()
        {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "finite_set_reduce: set {} is not verified to be finite",
                    x.set
                )),
            )));
        }

        self.verify_child_obj_well_defined_and_store_cache(
            &x.func,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &x.op,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 2 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &x.seed,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 3 },
        )?;
        let carrier = self.verify_reduce_operation_signature(x.op.as_ref(), "finite_set_reduce")?;
        self.verify_reduce_iterand_return_carrier(x.func.as_ref(), &carrier, "finite_set_reduce")?;
        self.require_reduce_seed_in_carrier(
            x.seed.as_ref(),
            &carrier,
            verify_state,
            "finite_set_reduce",
        )?;
        self.verify_finite_set_reduce_operation_laws(x.op.as_ref(), &carrier)?;

        let empty_fact: AtomicFact =
            NotIsNonemptySetFact::new(x.set.as_ref().clone(), default_line_file()).into();
        if self
            .verify_atomic_fact(&empty_fact, verify_state)?
            .is_success()
        {
            return self.verify_empty_finite_set_aggregate_has_unary_iterand(
                "finite_set_reduce",
                x.func.as_ref(),
            );
        }

        if let Obj::ListSet(list_set) = x.set.as_ref() {
            self.verify_finite_list_anonymous_iterand_return(
                "finite_set_reduce",
                list_set,
                x.func.as_ref(),
                verify_state,
            )?;
            for element in &list_set.list {
                let application = self.reduce_callable_application_obj(
                    x.func.as_ref(),
                    &[element.as_ref().clone()],
                    "finite_set_reduce",
                )?;
                self.verify_obj_well_defined_as_verification_dependency(&application, verify_state)
                    .map_err(|e| {
                        RuntimeError::from(WellDefinedRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_cause(
                                format!(
                                    "finite_set_reduce: iterand {} is not defined at {}",
                                    x.func, element
                                ),
                                e,
                            ),
                        ))
                    })?;
            }
            return Ok(());
        }

        if let Obj::ClosedRange(range) = x.set.as_ref() {
            return self.verify_iterated_op_summand_under_integer_index_interval(
                x.func.as_ref(),
                range.start.as_ref(),
                range.end.as_ref(),
                verify_state,
                "finite_set_reduce",
            );
        }

        self.verify_finite_set_reduce_iterand_domain_covers_set(
            "finite_set_reduce",
            x.func.as_ref(),
            x.set.as_ref(),
            verify_state,
        )?;
        self.verify_symbolic_finite_set_anonymous_iterand_return(
            "finite_set_reduce",
            x.func.as_ref(),
            verify_state,
        )
    }

    /// A symbolic finite-set reduction may reuse a function on a larger
    /// carrier when the aggregate set is verified to be a subset of that
    /// carrier. Domain predicates remain disallowed here because proving them
    /// pointwise needs an explicit restriction function.
    fn verify_finite_set_reduce_iterand_domain_covers_set(
        &mut self,
        operation_name: &str,
        function: &Obj,
        set: &Obj,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        let Some(body) = self.get_fn_range_function_body(function) else {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{operation_name}: {function} must be a unary function with a known function set"
                )),
            )));
        };
        if body.set_bound_parameters.number_of_params() != 1 || !body.dom_facts.is_empty() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{operation_name}: {function} must be an unconditional unary function; use an explicit restriction for a conditional domain"
                )),
            )));
        }
        let binding = body.set_bound_parameters.collect_param_bindings();
        let Some(binding) = binding.first() else {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{operation_name}: cannot resolve the iterand domain"
                )),
            )));
        };
        let Some(domain) =
            Self::unary_param_set_from_params_def(&body.set_bound_parameters, binding.name())
        else {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{operation_name}: cannot resolve the iterand domain"
                )),
            )));
        };
        if obj_equality_key(&domain) == obj_equality_key(set) {
            return Ok(());
        }
        let coverage: AtomicFact =
            SubsetFact::new(set.clone(), domain.clone(), default_line_file()).into();
        if self
            .verify_atomic_fact(&coverage, verify_state)?
            .is_success()
        {
            return Ok(());
        }
        Err(RuntimeError::from(WellDefinedRuntimeError(
            RuntimeErrorStruct::new_with_just_msg(format!(
                "{operation_name}: cannot verify aggregate set {set} is contained in iterand domain {domain}"
            )),
        )))
    }

    /// Resolve the homogeneous carrier of an unconditional binary operation.
    /// The two parameter carriers and the return carrier must be the same set.
    pub fn reduce_carrier_from_operation(&self, operation: &Obj) -> Option<Obj> {
        let body = self.get_fn_range_function_body(operation)?;
        if body.set_bound_parameters.number_of_params() != 2 || !body.dom_facts.is_empty() {
            return None;
        }
        let mut parameter_sets = Vec::with_capacity(2);
        for group in body.set_bound_parameters.iter() {
            for _ in &group.params {
                parameter_sets.push(group.set_obj().clone());
            }
        }
        let [left_set, right_set] = parameter_sets.as_slice() else {
            return None;
        };
        if obj_equality_key(left_set) != obj_equality_key(right_set)
            || obj_equality_key(left_set) != obj_equality_key(body.ret_set.as_ref())
        {
            return None;
        }
        Some(left_set.clone())
    }

    fn verify_reduce_operation_signature(
        &self,
        operation: &Obj,
        operation_name: &str,
    ) -> Result<Obj, RuntimeError> {
        self.reduce_carrier_from_operation(operation).ok_or_else(|| {
            RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{operation_name}: operation {operation} must have an unconditional homogeneous signature fn(x, y T) T"
                )),
            ))
        })
    }

    fn verify_reduce_iterand_return_carrier(
        &self,
        function: &Obj,
        carrier: &Obj,
        operation_name: &str,
    ) -> Result<(), RuntimeError> {
        let Some(body) = self.get_fn_range_function_body(function) else {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{operation_name}: iterand {function} must be a unary function with a known function set"
                )),
            )));
        };
        if body.set_bound_parameters.number_of_params() != 1 {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{operation_name}: iterand {function} must be unary"
                )),
            )));
        }
        if obj_equality_key(body.ret_set.as_ref()) != obj_equality_key(carrier) {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{operation_name}: iterand return set {} must equal operation carrier {carrier}",
                    body.ret_set
                )),
            )));
        }
        Ok(())
    }

    fn require_reduce_seed_in_carrier(
        &mut self,
        seed: &Obj,
        carrier: &Obj,
        verify_state: &ProofSearchState,
        operation_name: &str,
    ) -> Result<(), RuntimeError> {
        let seed_fact: AtomicFact =
            InFact::new(seed.clone(), carrier.clone(), default_line_file()).into();
        if self
            .verify_atomic_fact(&seed_fact, verify_state)?
            .is_unknown()
        {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{operation_name}: seed {seed} is not verified to belong to operation carrier {carrier}"
                )),
            )));
        }
        Ok(())
    }

    pub fn reduce_callable_application_obj(
        &self,
        callable: &Obj,
        args: &[Obj],
        operation_name: &str,
    ) -> Result<Obj, RuntimeError> {
        if let Obj::FnObj(application) = callable {
            if !application.body.is_empty() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "{operation_name}: expected a bare function, not application {callable}"
                    )),
                )));
            }
            return Ok(FnObj::new(
                application.head.as_ref().clone(),
                vec![args.iter().cloned().map(Box::new).collect()],
            )
            .into());
        }
        let Some(head) = FnObjHead::from_callable_obj(callable.clone()) else {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{operation_name}: {callable} is not callable"
                )),
            )));
        };
        Ok(FnObj::new(head, vec![args.iter().cloned().map(Box::new).collect()]).into())
    }

    /// Instantiate an anonymous function body directly; retain named
    /// functions as ordinary applications so definition unfolding and known
    /// forall facts remain available to equality verification.
    pub fn instantiate_reduce_function_at(
        &mut self,
        function: &Obj,
        args: &[Obj],
    ) -> Result<Option<Obj>, RuntimeError> {
        if let Some(anonymous) = Self::summand_as_anonymous_fn(function) {
            if anonymous.body.set_bound_parameters.number_of_params() != args.len() {
                return Ok(None);
            }
            let args = args.to_vec();
            let substitutions = SetBoundParameterGroup::param_defs_and_args_to_param_to_arg_map(
                &anonymous.body.set_bound_parameters,
                &args,
            );
            return Ok(Some(self.inst_obj(
                anonymous.equal_to.as_ref(),
                &substitutions,
                SubstitutionMode::Exact,
            )?));
        }
        let application = self.reduce_callable_application_obj(function, args, "reduce")?;
        let already_checked_state = ProofSearchState::after_well_definedness();
        if let Some(unfolded) =
            self.unfold_known_fn_application_once(&application, &already_checked_state)?
        {
            return Ok(Some(unfolded));
        }
        Ok(Some(application))
    }

    fn summand_as_anonymous_fn(obj: &Obj) -> Option<&AnonymousFn> {
        match obj {
            Obj::AnonymousFn(anonymous) => Some(anonymous),
            Obj::FnObj(application) if application.body.is_empty() => {
                match application.head.as_ref() {
                    FnObjHead::AnonymousFnLiteral(anonymous) => Some(anonymous.as_ref()),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn verify_finite_set_reduce_operation_laws(
        &mut self,
        operation: &Obj,
        carrier: &Obj,
    ) -> Result<(), RuntimeError> {
        let operation = operation.clone();
        let carrier = carrier.clone();
        self.run_in_local_env(|rt| {
            let x_name = rt.generate_random_unused_name();
            let y_name = rt.generate_random_unused_name();
            let z_name = rt.generate_random_unused_name();
            let (x_binding, x) = rt.fresh_bound_param(x_name)?;
            let (y_binding, y) = rt.fresh_bound_param(y_name)?;
            let (z_binding, z) = rt.fresh_bound_param(z_name)?;
            let params = TypedParameterList::new(vec![TypedParameterGroup::new(
                vec![x_binding, y_binding, z_binding],
                ParamType::Obj(carrier.clone()),
            )]);
            rt.define_params_with_type(&params, false, BindingScope::LocalBinder)?;

            let Some(xy) = rt.instantiate_reduce_function_at(
                &operation,
                &[x.clone(), y.clone()],
            )? else {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(
                        "finite_set_reduce: could not instantiate operation".to_string(),
                    ),
                )));
            };
            let Some(yz) = rt.instantiate_reduce_function_at(
                &operation,
                &[y.clone(), z.clone()],
            )? else {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(
                        "finite_set_reduce: could not instantiate operation".to_string(),
                    ),
                )));
            };
            let Some(left_assoc) =
                rt.instantiate_reduce_function_at(&operation, &[xy, z.clone()])?
            else {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(
                        "finite_set_reduce: could not instantiate nested operation".to_string(),
                    ),
                )));
            };
            let Some(right_assoc) =
                rt.instantiate_reduce_function_at(&operation, &[x.clone(), yz])?
            else {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(
                        "finite_set_reduce: could not instantiate nested operation".to_string(),
                    ),
                )));
            };
            let law_state = ProofSearchState::initial();
            let associativity: AtomicFact =
                EqualFact::new(left_assoc, right_assoc, default_line_file()).into();
            if rt.verify_atomic_fact(&associativity, &law_state)?.is_unknown() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "finite_set_reduce: operation {operation} is not verified associative on {carrier}"
                    )),
                )));
            }

            let Some(xy) =
                rt.instantiate_reduce_function_at(&operation, &[x.clone(), y.clone()])?
            else {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(
                        "finite_set_reduce: could not instantiate operation".to_string(),
                    ),
                )));
            };
            let Some(yx) = rt.instantiate_reduce_function_at(&operation, &[y, x])? else {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(
                        "finite_set_reduce: could not instantiate operation".to_string(),
                    ),
                )));
            };
            let commutativity: AtomicFact =
                EqualFact::new(xy, yx, default_line_file()).into();
            if rt.verify_atomic_fact(&commutativity, &law_state)?.is_unknown() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "finite_set_reduce: operation {operation} is not verified commutative on {carrier}"
                    )),
                )));
            }
            Ok(())
        })
    }

    /// Mathematical contract: `sum(a,b,f)` requires well-defined integer
    /// endpoints with `a <= b` and a unary scalar-valued function defined at
    /// every integer of the closed interval.
    pub(in crate::verify) fn verify_sum_obj_well_defined(
        &mut self,
        x: &Sum,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.start,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &x.end,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
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
        self.verify_child_obj_well_defined_and_store_cache(
            &x.func,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 2 },
        )?;
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
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.set,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
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
        self.verify_child_obj_well_defined_and_store_cache(
            &x.func,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
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
                .is_success()
            {
                return self.verify_empty_finite_set_aggregate_has_unary_iterand(
                    "finite_set_sum",
                    &x.func,
                );
            }
            let range_sum: Obj = Sum::new(
                range.start.as_ref().clone(),
                range.end.as_ref().clone(),
                x.func.as_ref().clone(),
            )
            .into();
            return self
                .verify_obj_well_defined_as_verification_dependency(&range_sum, verify_state);
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
    /// unary, unconditional function whose defined domain is syntactically
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
        if body.set_bound_parameters.number_of_params() != 1 || !body.dom_facts.is_empty() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{}: {} must have domain {} exactly; pass an explicit restriction such as fn(x {}) T {{{}(x)}}",
                    operation, function, set, set, function
                )),
            )));
        }
        let Some(domain) = body.set_bound_parameters.first() else {
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
    /// unary iterand definition must specify a return set contained in `C`. For a
    /// dependent function set, the containment obligation is checked under
    /// the parameter memberships and domain assumptions of that function set.
    fn verify_iterated_function_has_scalar_return_set(
        &mut self,
        operation: &str,
        function: &Obj,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        let Some(mut body) = self.get_fn_range_function_body(function) else {
            // The operation-specific callable/domain check reports a more
            // precise diagnostic when the object has no known function set.
            return Ok(());
        };
        if body.set_bound_parameters.number_of_params() != 1 {
            return Ok(());
        }

        let bindings = body.set_bound_parameters.collect_param_bindings();
        let rename_map = self.visible_binding_conflict_rename_map(&bindings)?;
        if !rename_map.is_empty() {
            body = self.alpha_rename_fn_set_body(&body, &rename_map)?;
        }

        self.run_in_local_env(|rt| {
            for param in body.set_bound_parameters.iter() {
                rt.define_params_with_set_in_scope(param, BindingScope::LocalBinder)?;
            }
            for domain_fact in body.dom_facts.iter() {
                rt.store_quantifier_free_fact_with_well_defined_verification_and_infer(
                    domain_fact,
                    verify_state,
                )?;
            }
            rt.verify_obj_well_defined_as_verification_dependency(&body.ret_set, verify_state)?;

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
        if body.set_bound_parameters.number_of_params() != 1 {
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
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        let Some(body) = self.get_fn_range_function_body(func) else {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "finite_set_sum: summand must be a unary function; got {}",
                    func
                )),
            )));
        };
        if SetBoundParameterGroup::number_of_params(&body.set_bound_parameters) != 1 {
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
            self.verify_obj_well_defined_as_verification_dependency(&application, verify_state)
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
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.set,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
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
        self.verify_child_obj_well_defined_and_store_cache(
            &x.func,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
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
                .is_success()
            {
                return self.verify_empty_finite_set_aggregate_has_unary_iterand(
                    "finite_set_product",
                    &x.func,
                );
            }
            let range_product: Obj = Product::new(
                range.start.as_ref().clone(),
                range.end.as_ref().clone(),
                x.func.as_ref().clone(),
            )
            .into();
            return self
                .verify_obj_well_defined_as_verification_dependency(&range_product, verify_state);
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
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        let Some(body) = self.get_fn_range_function_body(func) else {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "finite_set_product: factor must be a unary function; got {}",
                    func
                )),
            )));
        };
        if SetBoundParameterGroup::number_of_params(&body.set_bound_parameters) != 1 {
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
            self.verify_obj_well_defined_as_verification_dependency(&application, verify_state)
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
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.start,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &x.end,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
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
        self.verify_child_obj_well_defined_and_store_cache(
            &x.func,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 2 },
        )?;
        self.verify_iterated_function_has_scalar_return_set("product", &x.func, verify_state)?;
        self.verify_iterated_op_summand_under_integer_index_interval(
            &x.func,
            x.start.as_ref(),
            x.end.as_ref(),
            verify_state,
            "product",
        )
    }

    /// Resolve the set `S` in `pname S` for the unary param from `set_bound_parameters`.
    pub(in crate::verify) fn unary_param_set_from_params_def(
        params_def: &[SetBoundParameterGroup],
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
    /// must lie in the iterand's defined parameter carrier. Example: a `N`
    /// iterand accepts `sum(m,n,f)` only when the nonnegative lower endpoint is
    /// provable.
    pub(in crate::verify) fn verify_closed_range_each_integer_satisfies_unary_param_set(
        &mut self,
        start: &Obj,
        end: &Obj,
        param_set: &Obj,
        verify_state: &ProofSearchState,
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
            Obj::StandardSet(StandardSet::ZStar)
            | Obj::StandardSet(StandardSet::QStar)
            | Obj::StandardSet(StandardSet::RStar)
            | Obj::StandardSet(StandardSet::CStar) => {
                vec![(start, StandardSet::NPos), (end, StandardSet::ZNeg)]
            }
            _ => Vec::new(),
        };
        for (endpoint, required_set) in endpoint_requirements {
            let fact: AtomicFact =
                InFact::new(endpoint.clone(), required_set.into(), default_line_file()).into();
            if self.verify_atomic_fact(&fact, verify_state)?.is_success() {
                return Ok(());
            }
        }

        let interval: Obj = ClosedRange::new(start.clone(), end.clone()).into();
        let subset_fact: AtomicFact =
            SubsetFact::new(interval, param_set.clone(), default_line_file()).into();
        if self
            .verify_atomic_fact(&subset_fact, verify_state)?
            .is_success()
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
    /// complete integer interval, satisfies every defined domain predicate
    /// there, and has a meaningful return carrier under those assumptions.
    pub(in crate::verify) fn verify_iterated_op_summand_with_stored_fn_set_body(
        &mut self,
        fs_body: FnSetBody,
        start: &Obj,
        end: &Obj,
        verify_state: &ProofSearchState,
        op: &str,
    ) -> Result<(), RuntimeError> {
        if SetBoundParameterGroup::number_of_params(&fs_body.set_bound_parameters) != 1 {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{op}: the function in the function set must be unary (one index)"
                )),
            )));
        }
        let param_bindings = fs_body.set_bound_parameters.collect_param_bindings();
        let param_binding = param_bindings[0].clone();
        let Some(param_set_for_index) = Self::unary_param_set_from_params_def(
            &fs_body.set_bound_parameters,
            param_binding.name(),
        ) else {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{op}: could not find index parameter in set_bound_parameters"
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
            for g in fs_body.set_bound_parameters.iter() {
                rt.define_params_with_set_in_scope(g, BindingScope::LocalBinder)
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
            let k = obj_for_bound_param_in_scope(param_binding);
            let le_lo = QuantifierFreeFact::AtomicFact(
                LessEqualFact::new(start_c.clone(), k.clone(), default_line_file()).into(),
            );
            let le_hi = QuantifierFreeFact::AtomicFact(
                LessEqualFact::new(k, end_c.clone(), default_line_file()).into(),
            );
            rt.store_quantifier_free_fact_without_well_defined_verified_and_infer(le_lo)
                .map_err(|e| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!("{op}: could not add lower bound in local check"),
                            e,
                        ),
                    ))
                })?;
            rt.store_quantifier_free_fact_without_well_defined_verified_and_infer(le_hi)
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
                    .verify_quantifier_free_fact(df, verify_state)
                    .map_err(|e| {
                        RuntimeError::from(WellDefinedRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_cause(
                                format!("{op}: function set domain check failed"),
                                e,
                            ),
                        ))
                    })?;
                if !result.is_success() {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "{op}: cannot verify function domain condition {df} on the whole integer range"
                        )),
                    )));
                }
                rt.store_quantifier_free_fact_without_well_defined_verified_and_infer(
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
            rt.verify_obj_well_defined_as_verification_dependency(
                &fs_body.ret_set,
                verify_state,
            )
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
        verify_state: &ProofSearchState,
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
    /// throughout it, and its body is meaningful and belongs to the defined
    /// return set under those local assumptions.
    pub(in crate::verify) fn verify_unary_iterated_anonymous_in_interval(
        &mut self,
        af: &AnonymousFn,
        start: &Obj,
        end: &Obj,
        verify_state: &ProofSearchState,
        op: &str,
    ) -> Result<(), RuntimeError> {
        if SetBoundParameterGroup::number_of_params(&af.body.set_bound_parameters) != 1 {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{op}: summation/product index function must be unary (one parameter)"
                )),
            )));
        }
        let param_bindings = af.body.set_bound_parameters.collect_param_bindings();
        let param_binding = param_bindings[0].clone();
        let Some(param_set_for_index) = Self::unary_param_set_from_params_def(
            &af.body.set_bound_parameters,
            param_binding.name(),
        ) else {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "{op}: could not find index parameter in set_bound_parameters"
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
            for g in af.body.set_bound_parameters.iter() {
                rt.define_params_with_set_in_scope(g, BindingScope::LocalBinder)
                    .map_err(|e| {
                        RuntimeError::from(WellDefinedRuntimeError(RuntimeErrorStruct::new_with_msg_and_cause(format!("{op}: could not bind index parameter in local well-defined check"), e)))
                    })?;
            }
            let k = obj_for_bound_param_in_scope(param_binding);
            let le_lo = QuantifierFreeFact::AtomicFact(
                LessEqualFact::new(start.clone(), k.clone(), default_line_file()).into(),
            );
            let le_hi = QuantifierFreeFact::AtomicFact(
                LessEqualFact::new(k, end.clone(), default_line_file()).into(),
            );
            rt.store_quantifier_free_fact_without_well_defined_verified_and_infer(le_lo)
                .map_err(|e| {
                    RuntimeError::from(WellDefinedRuntimeError(RuntimeErrorStruct::new_with_msg_and_cause(format!("{op}: could not add lower bound in local check"), e)))
                })?;
            rt.store_quantifier_free_fact_without_well_defined_verified_and_infer(le_hi)
                .map_err(|e| {
                    RuntimeError::from(WellDefinedRuntimeError(RuntimeErrorStruct::new_with_msg_and_cause(format!("{op}: could not add upper bound in local check"), e)))
                })?;
            for df in af.body.dom_facts.iter() {
                let result = rt
                    .verify_quantifier_free_fact(df, verify_state)
                    .map_err(|e| {
                        RuntimeError::from(WellDefinedRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_cause(
                                format!("{op}: anonymous iterand domain check failed"),
                                e,
                            ),
                        ))
                    })?;
                if !result.is_success() {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "{op}: cannot verify anonymous iterand domain condition {df} on the whole integer range"
                        )),
                    )));
                }
                rt.store_quantifier_free_fact_without_well_defined_verified_and_infer(
                    df.clone(),
                )
                .map_err(|e| {
                    RuntimeError::from(WellDefinedRuntimeError(RuntimeErrorStruct::new_with_msg_and_cause(format!("{op}: local dom of anonymous summand in integer range check failed"), e)))
                })?;
            }
            rt.verify_obj_well_defined_as_verification_dependency(
                &af.body.ret_set,
                verify_state,
            )
                .map_err(|e| {
                    RuntimeError::from(WellDefinedRuntimeError(RuntimeErrorStruct::new_with_msg_and_cause(format!("{op}: return set not well-defined on the integer range"), e)))
                })?;
            rt.verify_obj_well_defined_as_verification_dependency(
                &af.equal_to,
                verify_state,
            )
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
                        "{op}: iterand body {} is not verified to belong to defined return set {}",
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
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.start,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &x.end,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
        self.require_obj_in_z(&x.start, verify_state)?;
        self.require_obj_in_z(&x.end, verify_state)?;
        Ok(())
    }

    /// Mathematical contract: a closed integer range is meaningful when both
    /// endpoints are well-defined integers; it may be empty.
    pub(in crate::verify) fn verify_closed_range_well_defined(
        &mut self,
        x: &ClosedRange,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.start,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &x.end,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
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
        verify_state: &ProofSearchState,
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
            let substitutions = SetBoundParameterGroup::param_defs_and_args_to_param_to_arg_map(
                &anonymous.body.set_bound_parameters,
                &args,
            );
            let body =
                self.inst_obj(&anonymous.equal_to, &substitutions, SubstitutionMode::Exact)?;
            let return_set = self.inst_obj(
                &anonymous.body.ret_set,
                &substitutions,
                SubstitutionMode::Exact,
            )?;
            let return_membership: AtomicFact =
                InFact::new(body.clone(), return_set.clone(), default_line_file()).into();
            let result = self.verify_atomic_fact(&return_membership, verify_state)?;
            if result.is_unknown() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "{op}: iterand body {body} is not verified to belong to defined return set {return_set} at {}",
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
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        let Some(anonymous) = Self::summand_as_unary_anonymous_fn(func) else {
            return Ok(());
        };
        self.run_in_local_env(|rt| {
            for param in anonymous.body.set_bound_parameters.iter() {
                rt.define_params_with_set_in_scope(param, BindingScope::LocalBinder)?;
            }
            let bindings = anonymous.body.set_bound_parameters.collect_param_bindings();
            if let [binding] = bindings.as_slice() {
                if let Some(param_set) = Self::unary_param_set_from_params_def(
                    &anonymous.body.set_bound_parameters,
                    binding.name(),
                ) {
                    if rt.verify_iterand_domain_is_contained_in_return_set(
                        &param_set,
                        anonymous.body.ret_set.as_ref(),
                        verify_state,
                    )? {
                        let param_obj = obj_for_bound_param_in_scope(binding);
                        let domain_membership: AtomicFact =
                            InFact::new(param_obj.clone(), param_set, default_line_file()).into();
                        if rt
                            .verify_atomic_fact(&domain_membership, verify_state)?
                            .is_success()
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
            rt.verify_obj_well_defined_as_verification_dependency(
                &anonymous.equal_to,
                verify_state,
            )?;
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
                        "{op}: iterand body {} is not verified to belong to defined return set {}",
                        anonymous.equal_to, anonymous.body.ret_set
                    )),
                )));
            }
            Ok(())
        })
    }

    /// Mathematical contract: prove that every element admitted by the
    /// iterand domain also belongs to its defined return set, using either a
    /// subset proof or sound structural reductions of the domain expression.
    fn verify_iterand_domain_is_contained_in_return_set(
        &mut self,
        domain: &Obj,
        return_set: &Obj,
        verify_state: &ProofSearchState,
    ) -> Result<bool, RuntimeError> {
        let subset_fact: AtomicFact =
            SubsetFact::new(domain.clone(), return_set.clone(), default_line_file()).into();
        if self
            .verify_atomic_fact(&subset_fact, verify_state)?
            .is_success()
        {
            return Ok(true);
        }

        match domain {
            Obj::StandardSet(domain_set) => {
                let Obj::StandardSet(return_standard_set) = return_set else {
                    return Ok(false);
                };
                Ok(domain_set.is_subset_eq(return_standard_set))
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
                        .is_success()
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
            Obj::SetBuilder(builder) => self.verify_iterand_domain_is_contained_in_return_set(
                builder.param_set.as_ref(),
                return_set,
                verify_state,
            ),
            Obj::Range(_) | Obj::ClosedRange(_) => {
                let Obj::StandardSet(return_standard_set) = return_set else {
                    return Ok(false);
                };
                Ok(StandardSet::Z.is_subset_eq(return_standard_set))
            }
            _ => Ok(false),
        }
    }
}
