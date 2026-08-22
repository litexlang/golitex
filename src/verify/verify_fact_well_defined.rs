use crate::prelude::*;

impl Runtime {
    pub fn verify_fact_well_defined_result(
        &mut self,
        fact: &Fact,
        verify_state: &UseContextVerifyState,
    ) -> Result<SuccessVerifyFactWellDefinedResult, RuntimeError> {
        let verify_state = verify_state.without_known_forall_for_equality();
        let verify_state = &verify_state;
        let recursive =
            match fact {
                Fact::AtomicFact(atomic_fact) => {
                    self.verify_atomic_fact_well_defined_result(atomic_fact, verify_state)?
                }
                Fact::AndFact(and_fact) => {
                    let mut conjuncts = Vec::with_capacity(and_fact.facts.len());
                    for atomic_fact in and_fact.facts.iter() {
                        conjuncts.push(
                            self.verify_atomic_fact_well_defined_result(atomic_fact, verify_state)?,
                        );
                    }
                    SuccessVerifyFactWellDefinedProofResult::AndFact(Box::new(
                        SuccessVerifyAndFactWellDefinedResult {
                            statement: and_fact.clone(),
                            conjuncts,
                        },
                    ))
                }
                Fact::ChainFact(chain_fact) => {
                    let atomic_facts = chain_fact.facts()?;
                    let mut comparisons = Vec::with_capacity(atomic_facts.len());
                    for atomic_fact in atomic_facts.iter() {
                        comparisons.push(
                            self.verify_atomic_fact_well_defined_result(atomic_fact, verify_state)?,
                        );
                    }
                    SuccessVerifyFactWellDefinedProofResult::ChainFact(Box::new(
                        SuccessVerifyChainFactWellDefinedResult {
                            statement: chain_fact.clone(),
                            comparisons,
                        },
                    ))
                }
                Fact::OrFact(or_fact) => {
                    let mut branches = Vec::with_capacity(or_fact.facts.len());
                    for branch in or_fact.facts.iter() {
                        branches.push(self.verify_and_chain_atomic_fact_well_defined_result(
                            branch,
                            verify_state,
                        )?);
                    }
                    SuccessVerifyFactWellDefinedProofResult::OrFact(Box::new(
                        SuccessVerifyOrFactWellDefinedResult {
                            statement: or_fact.clone(),
                            branches,
                        },
                    ))
                }
                Fact::ExistFact(exist_fact) => {
                    self.verify_exist_fact_well_defined_result(exist_fact, verify_state)?
                }
                Fact::ForallFact(forall_fact) => {
                    self.verify_forall_fact_well_defined_result(forall_fact, verify_state)?
                }
                Fact::ForallFactWithIff(forall_fact) => {
                    let (forward, reverse) = forall_fact.to_two_forall_facts()?;
                    let forward =
                        self.verify_forall_fact_well_defined_result(&forward, verify_state)?;
                    let reverse =
                        self.verify_forall_fact_well_defined_result(&reverse, verify_state)?;
                    SuccessVerifyFactWellDefinedProofResult::ForallFactWithIff(Box::new(
                        SuccessVerifyForallFactWithIffWellDefinedResult {
                            statement: forall_fact.clone(),
                            forward: Box::new(forward),
                            reverse: Box::new(reverse),
                        },
                    ))
                }
                Fact::NotForall(not_forall) => {
                    let inner = self.verify_forall_fact_well_defined_result(
                        &not_forall.forall_fact,
                        verify_state,
                    )?;
                    SuccessVerifyFactWellDefinedProofResult::NotForallFact(Box::new(
                        SuccessVerifyNotForallFactWellDefinedResult {
                            statement: not_forall.clone(),
                            inner: Box::new(inner),
                        },
                    ))
                }
            };
        Ok(SuccessVerifyFactWellDefinedResult::new_recursive(recursive))
    }

    fn verify_atomic_fact_well_defined_result(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<SuccessVerifyFactWellDefinedProofResult, RuntimeError> {
        let arguments = atomic_fact.args_ref();
        let mut argument_results = Vec::with_capacity(arguments.len());
        for (argument_index, object) in arguments.iter().enumerate() {
            argument_results.push(SuccessVerifyFactObjectWellDefinedResult::new(
                argument_index,
                (*object).clone(),
                self.verify_obj_well_defined_result(object, verify_state)?,
            ));
        }
        let predicate =
            self.verify_atomic_predicate_well_defined_result(atomic_fact, verify_state)?;
        Ok(SuccessVerifyFactWellDefinedProofResult::AtomicFact(
            Box::new(SuccessVerifyAtomicFactWellDefinedResult::new(
                atomic_fact.clone(),
                argument_results,
                predicate,
            )),
        ))
    }

    fn verify_and_chain_atomic_fact_well_defined_result(
        &mut self,
        fact: &AndChainAtomicFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<SuccessVerifyFactWellDefinedProofResult, RuntimeError> {
        match fact {
            AndChainAtomicFact::AtomicFact(atomic_fact) => {
                self.verify_atomic_fact_well_defined_result(atomic_fact, verify_state)
            }
            AndChainAtomicFact::AndFact(and_fact) => self
                .verify_fact_well_defined_result(&and_fact.clone().into(), verify_state)
                .map(|result| *result.recursive.expect("new recursive WD result")),
            AndChainAtomicFact::ChainFact(chain_fact) => self
                .verify_fact_well_defined_result(&chain_fact.clone().into(), verify_state)
                .map(|result| *result.recursive.expect("new recursive WD result")),
        }
    }

    fn verify_exist_fact_well_defined_result(
        &mut self,
        exist_fact: &ExistFactEnum,
        verify_state: &UseContextVerifyState,
    ) -> Result<SuccessVerifyFactWellDefinedProofResult, RuntimeError> {
        let bindings = exist_fact.params_def_with_type().collect_param_bindings();
        let rename_map =
            self.visible_binding_conflict_rename_map(&bindings, ParamObjType::Exist)?;
        let working = if rename_map.is_empty() {
            exist_fact.clone()
        } else {
            self.alpha_rename_exist_fact(exist_fact, &rename_map)?
        };
        let (binder, body) = self.run_in_local_env(|runtime| -> Result<_, RuntimeError> {
            let binder = runtime.verify_fact_binder_result(
                working.params_def_with_type(),
                ParamObjType::Exist,
                verify_state,
            )?;
            let mut body = Vec::with_capacity(working.facts().len());
            for fact in working.facts() {
                body.push(runtime.verify_and_store_quantifier_free_wd_result(fact, verify_state)?);
            }
            Ok((binder, body))
        })?;
        Ok(SuccessVerifyFactWellDefinedProofResult::ExistFact(
            Box::new(SuccessVerifyExistFactWellDefinedResult {
                statement: exist_fact.clone(),
                binder,
                body,
            }),
        ))
    }

    fn verify_forall_fact_well_defined_result(
        &mut self,
        forall_fact: &ForallFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<SuccessVerifyFactWellDefinedProofResult, RuntimeError> {
        let (well_definedness, _) = self
            .verify_forall_fact_well_defined_and_collect_certificate(forall_fact, verify_state)?;
        Ok(*well_definedness
            .recursive
            .expect("forall precheck returns recursive WD evidence"))
    }

    pub(crate) fn verify_fact_binder_result(
        &mut self,
        parameter_definition: &ParamDefWithType,
        binding_kind: ParamObjType,
        verify_state: &UseContextVerifyState,
    ) -> Result<SuccessVerifyFactBinderResult, RuntimeError> {
        let mut parameter_groups = Vec::with_capacity(parameter_definition.len());
        for (group_index, group) in parameter_definition.iter().enumerate() {
            let carrier = match &group.param_type {
                ParamType::Obj(object) => Some(self.verify_child_obj_well_defined_result(
                    object,
                    verify_state,
                    WellDefinedObjChildRole::BinderParameterCarrier {
                        parameter_group_index: group_index,
                    },
                )?),
                ParamType::Set(_) | ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => None,
            };
            let mut parameters = Vec::with_capacity(group.params.len());
            for (parameter_index, binding) in group.params.iter().enumerate() {
                self.store_parameter_binding(binding, binding_kind)?;
                let proposition =
                    self.parameter_type_fact_for_binding(binding, &group.param_type, binding_kind)?;
                let well_definedness =
                    self.verify_fact_well_defined_result(&proposition, verify_state)?;
                let Fact::AtomicFact(atomic) = proposition.clone() else {
                    unreachable!("parameter type proposition is atomic")
                };
                let mut infers = self
                    .store_atomic_fact_without_well_defined_verified_and_infer_with_reason(
                        atomic,
                        InferReason::ParameterDefinition.store_reason(),
                    )?;
                self.attach_known_fact_ids_to_infer_result(&mut infers)?;
                parameters.push(SuccessVerifyBinderPremiseResult::new(
                    WellDefinedBinderPremiseRole::ParameterMembership {
                        parameter_group_index: group_index,
                        parameter_index,
                    },
                    Some(binding.id()),
                    proposition,
                    well_definedness,
                    infers,
                ));
            }
            parameter_groups.push(SuccessVerifyFactParameterGroupResult {
                group_index,
                parameter_type: group.param_type.clone(),
                carrier,
                parameters,
            });
        }
        Ok(SuccessVerifyFactBinderResult { parameter_groups })
    }

    pub(crate) fn verify_and_store_quantifier_free_wd_result(
        &mut self,
        fact: &QuantifierFreeFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<SuccessVerifyLocalFactWellDefinedResult, RuntimeError> {
        let proposition: Fact = fact.clone().into();
        let well_definedness = self.verify_fact_well_defined_result(&proposition, verify_state)?;
        let mut infers =
            self.store_quantifier_free_fact_without_well_defined_verified_and_infer(fact.clone())?;
        self.attach_known_fact_ids_to_infer_result(&mut infers)?;
        let fact_id = self.known_fact_id_for_fact(&proposition)?;
        Ok(SuccessVerifyLocalFactWellDefinedResult {
            proposition: proposition.clone(),
            well_definedness: well_definedness
                .recursive
                .expect("recursive quantifier-free WD result"),
            store: SuccessStoreFactResult {
                fact: proposition,
                fact_id,
                infers,
            },
        })
    }

    fn verify_and_store_fact_wd_result(
        &mut self,
        proposition: &Fact,
        verify_state: &UseContextVerifyState,
    ) -> Result<SuccessVerifyLocalFactWellDefinedResult, RuntimeError> {
        let well_definedness = self.verify_fact_well_defined_result(proposition, verify_state)?;
        let mut infers =
            self.store_without_well_defined_verification_and_infer(proposition.clone())?;
        self.attach_known_fact_ids_to_infer_result(&mut infers)?;
        let fact_id = self.known_fact_id_for_fact(proposition)?;
        Ok(SuccessVerifyLocalFactWellDefinedResult {
            proposition: proposition.clone(),
            well_definedness: well_definedness
                .recursive
                .expect("recursive local fact WD result"),
            store: SuccessStoreFactResult {
                fact: proposition.clone(),
                fact_id,
                infers,
            },
        })
    }

    /// Mathematical contract: a fact is well-defined when its predicate/fact
    /// form exists and every object, binder type, premise, and conclusion is
    /// meaningful in the scope introduced by that fact.
    pub fn verify_fact_well_defined(
        &mut self,
        fact: &Fact,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        let verify_state = verify_state.without_known_forall_for_equality();
        let verify_state = &verify_state;
        match fact {
            Fact::AtomicFact(atomic_fact) => {
                self.verify_atomic_fact_well_defined(atomic_fact, verify_state)
            }
            Fact::AndFact(and_fact) => self.verify_and_fact_well_defined(and_fact, verify_state),
            Fact::ChainFact(chain_fact) => {
                self.verify_chain_fact_well_defined(chain_fact, verify_state)
            }
            Fact::OrFact(or_fact) => self.verify_or_fact_well_defined(or_fact, verify_state),
            Fact::ExistFact(exist_fact) => {
                self.verify_exist_fact_well_defined(exist_fact, verify_state)
            }
            Fact::ForallFact(forall_fact) => {
                self.verify_forall_fact_well_defined(forall_fact, verify_state)
            }
            Fact::ForallFactWithIff(forall_fact_with_iff) => {
                self.verify_forall_fact_with_iff_well_defined(forall_fact_with_iff, verify_state)
            }
            Fact::NotForall(not_forall) => {
                self.verify_not_forall_fact_well_defined(not_forall, verify_state)
            }
        }
    }

    /// Mathematical contract: an atomic fact is well-defined when its
    /// predicate is defined at the supplied arity and every argument object is
    /// well-defined. Concrete proposition parameter carriers are proof-time
    /// requirements when the definition is unfolded, not part of this gate.
    pub fn verify_atomic_fact_well_defined(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_atomic_fact_well_defined_result(atomic_fact, verify_state)
            .map(|_| ())
    }

    /// Records the predicate/arity gate and every proof obligation imposed by
    /// a partial builtin predicate. Argument-object WD is owned separately by
    /// `SuccessVerifyAtomicFactWellDefinedResult::arguments`.
    fn verify_atomic_predicate_well_defined_result(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<SuccessVerifyAtomicPredicateWellDefinedResult, RuntimeError> {
        let name_string = atomic_fact.key();
        if matches!(atomic_fact, AtomicFact::EqualFact(_)) {
            return Ok(SuccessVerifyAtomicPredicateWellDefinedResult {
                name: name_string,
                expected_arity: 2,
                domain_checks: Vec::new(),
            });
        }

        let expected_len = if is_builtin_predicate(&name_string) {
            atomic_fact.is_builtin_predicate_and_return_expected_args_len()
        } else if let Some(predicate_definition) = self.get_prop_definition_by_name(&name_string) {
            predicate_definition.params_def_with_type.number_of_params()
        } else if let Some(abstract_prop_definition) =
            self.get_abstract_prop_definition_by_name(&name_string)
        {
            abstract_prop_definition.params.len()
        } else {
            return Err(
                WellDefinedRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!("fact `{}` not defined", name_string),
                    atomic_fact.line_file(),
                ))
                .into(),
            );
        };

        {
            let actual_args = atomic_fact.args_ref();
            if actual_args.len() != expected_len {
                return Err(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!(
                            "fact `{}` expects {} argument(s), but got {}",
                            name_string,
                            expected_len,
                            actual_args.len()
                        ),
                        atomic_fact.line_file(),
                    ),
                )
                .into());
            }
        }

        if let Some(domain_checks) =
            crate::verify::verify_choice_function_for_arg_types(self, atomic_fact, verify_state)?
        {
            return Ok(SuccessVerifyAtomicPredicateWellDefinedResult {
                name: name_string,
                expected_arity: expected_len,
                domain_checks,
            });
        }

        let mut domain_checks = Vec::new();
        if name_string == PRIME {
            let arg = atomic_fact.args_ref()[0];
            let in_n: AtomicFact =
                InFact::new(arg.clone(), StandardSet::N.into(), atomic_fact.line_file()).into();
            let result = self.verify_atomic_fact(&in_n, verify_state)?;
            if result.is_unknown() {
                return Err(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!("{} requires its argument to belong to N", atomic_fact),
                        atomic_fact.line_file(),
                    ),
                )
                .into());
            }
            domain_checks.push(SuccessVerifyAtomicPredicateDomainCheckResult {
                role: AtomicPredicateDomainCheckRole::PrimeNaturalArgument,
                result: Box::new(result),
            });
        }

        if name_string == COPRIME {
            for arg in atomic_fact.args_ref() {
                let in_n: AtomicFact = InFact::new(
                    (*arg).clone(),
                    StandardSet::N.into(),
                    atomic_fact.line_file(),
                )
                .into();
                let result = self.verify_atomic_fact(&in_n, verify_state)?;
                if result.is_unknown() {
                    return Err(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            format!("{} requires both arguments to belong to N", atomic_fact),
                            atomic_fact.line_file(),
                        ),
                    )
                    .into());
                }
                domain_checks.push(SuccessVerifyAtomicPredicateDomainCheckResult {
                    role: AtomicPredicateDomainCheckRole::CoprimeNaturalArgument,
                    result: Box::new(result),
                });
            }
        }

        if name_string == DVD {
            let expected_sets = [StandardSet::Z, StandardSet::ZStar];
            for (index, (arg, expected_set)) in
                atomic_fact.args_ref().iter().zip(expected_sets).enumerate()
            {
                let membership: AtomicFact =
                    InFact::new((*arg).clone(), expected_set.into(), atomic_fact.line_file())
                        .into();
                let result = self.verify_atomic_fact(&membership, verify_state)?;
                if result.is_unknown() {
                    return Err(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            format!(
                                "{} requires its first argument in Z and second argument in Z*",
                                atomic_fact
                            ),
                            atomic_fact.line_file(),
                        ),
                    )
                    .into());
                }
                domain_checks.push(SuccessVerifyAtomicPredicateDomainCheckResult {
                    role: if index == 0 {
                        AtomicPredicateDomainCheckRole::DivisibilityIntegerArgument
                    } else {
                        AtomicPredicateDomainCheckRole::DivisibilityNonzeroIntegerArgument
                    },
                    result: Box::new(result),
                });
            }
        }

        if matches!(
            atomic_fact,
            AtomicFact::LessFact(_)
                | AtomicFact::GreaterFact(_)
                | AtomicFact::LessEqualFact(_)
                | AtomicFact::GreaterEqualFact(_)
                | AtomicFact::NotLessFact(_)
                | AtomicFact::NotGreaterFact(_)
                | AtomicFact::NotLessEqualFact(_)
                | AtomicFact::NotGreaterEqualFact(_)
        ) {
            let args = atomic_fact.args_ref();
            let real_args: Vec<&Obj> = args.iter().copied().collect();
            let Some(results) = self.verify_objects_are_known_reals(
                real_args.as_slice(),
                &atomic_fact.line_file(),
                verify_state,
            )?
            else {
                return Err(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!(
                            "ordered comparison requires both operands to belong to R: {}",
                            atomic_fact
                        ),
                        atomic_fact.line_file(),
                    ),
                )
                .into());
            };
            for result in results {
                domain_checks.push(SuccessVerifyAtomicPredicateDomainCheckResult {
                    role: AtomicPredicateDomainCheckRole::OrderedRealCarrierEvidence,
                    result: Box::new(result),
                });
            }
        }

        if let Some(type_result) =
            self.verify_builtin_function_property_arg_types(atomic_fact, verify_state)?
        {
            if type_result.is_unknown() {
                return Err(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!(
                            "{} requires sets A and B and a function with type fn(x A) B",
                            atomic_fact
                        ),
                        atomic_fact.line_file(),
                    ),
                )
                .into());
            }
            domain_checks.push(SuccessVerifyAtomicPredicateDomainCheckResult {
                role: AtomicPredicateDomainCheckRole::FunctionPropertySignature,
                result: Box::new(type_result),
            });
        }

        Ok(SuccessVerifyAtomicPredicateWellDefinedResult {
            name: name_string,
            expected_arity: expected_len,
            domain_checks,
        })
    }

    /// Mathematical contract: a conjunction is well-defined when every
    /// conjunct is well-defined in the same context.
    pub fn verify_and_fact_well_defined(
        &mut self,
        and_fact: &AndFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_fact_well_defined_result(&and_fact.clone().into(), verify_state)
            .map(|_| ())
    }

    /// Mathematical contract: a comparison chain is well-defined when every
    /// adjacent atomic comparison produced by the chain is well-defined.
    pub fn verify_chain_fact_well_defined(
        &mut self,
        chain_fact: &ChainFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_fact_well_defined_result(&chain_fact.clone().into(), verify_state)
            .map(|_| ())
    }

    /// Mathematical contract: a disjunction is well-defined only when every
    /// branch is meaningful, independently of which branch is true.
    pub fn verify_or_fact_well_defined(
        &mut self,
        or_fact: &OrFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_fact_well_defined_result(&or_fact.clone().into(), verify_state)
            .map(|_| ())
    }

    /// Mathematical contract: `exist x T st {body}` is well-defined when each
    /// binder type is meaningful in dependency order and every body fact is
    /// meaningful under the bound-variable type facts, preceding body
    /// assumptions, and their sound inferred consequences.
    pub fn verify_exist_fact_well_defined(
        &mut self,
        exist_fact: &ExistFactEnum,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_fact_well_defined_result(&exist_fact.clone().into(), verify_state)
            .map(|_| ())
    }

    /// Mathematical contract: `forall x T: premises => conclusions` is
    /// well-defined when the binder types and premises are meaningful in order
    /// and every conclusion is meaningful under those local assumptions.
    pub fn verify_forall_fact_well_defined(
        &mut self,
        forall_fact: &ForallFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_forall_fact_well_defined_and_collect_certificate(forall_fact, verify_state)
            .map(|_| ())
    }

    /// Check a universal fact once and retain only sound side effects produced
    /// by conclusion well-definedness (for example, the return-carrier fact of
    /// a checked function application). Domain assumptions and conclusions are
    /// kept in the temporary preflight scope and never enter the certificate.
    pub fn verify_forall_fact_well_defined_and_collect_certificate(
        &mut self,
        forall_fact: &ForallFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<(SuccessVerifyFactWellDefinedResult, Environment), RuntimeError> {
        let bindings = forall_fact.params_def_with_type.collect_param_bindings();
        let rename_map =
            self.visible_binding_conflict_rename_map(&bindings, ParamObjType::Forall)?;
        let working = if rename_map.is_empty() {
            forall_fact.clone()
        } else {
            let renamed = self.alpha_rename_forall_fact(forall_fact, &rename_map)?;
            renamed
        };

        self.run_in_local_env(|rt| {
            let binder = rt.verify_fact_binder_result(
                &working.params_def_with_type,
                ParamObjType::Forall,
                verify_state,
            )?;
            let mut premises = Vec::with_capacity(working.dom_facts.len());
            for premise in &working.dom_facts {
                premises.push(rt.verify_and_store_fact_wd_result(premise, verify_state)?);
            }

            let mut certificate = Environment::new_empty_env();
            let mut conclusions = Vec::with_capacity(working.then_facts.len());
            for fact in working.then_facts.iter() {
                let proposition = fact.clone().to_fact();
                let checked = rt.run_in_local_env_and_take(|checking_rt| {
                    checking_rt.verify_fact_well_defined_result(&proposition, verify_state)
                });
                let (well_definedness, checked_side_effects) =
                    checked.map_err(|exec_stmt_error| {
                        RuntimeError::from(WellDefinedRuntimeError(RuntimeErrorStruct::new(
                            None,
                            String::new(),
                            fact.line_file(),
                            Some(exec_stmt_error),
                            vec![],
                        )))
                    })?;

                // The proof scope must receive the exact execution support
                // created while checking the conclusion. In particular, a
                // template occurrence is well-defined only after its local
                // instantiation has installed the public equality used by
                // definition reduction. The child does not own the forall
                // parameters or premises (it inherits them), so retaining its
                // complete checked effects cannot leak those assumptions.
                certificate.merge_committed_child(checked_side_effects.clone())?;
                rt.top_level_env()
                    .merge_committed_child(checked_side_effects)?;

                let mut infers = rt
                    .store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                        fact.clone(),
                    )
                    .map_err(|exec_stmt_error| {
                        RuntimeError::from(WellDefinedRuntimeError(RuntimeErrorStruct::new(
                            None,
                            String::new(),
                            fact.line_file(),
                            Some(exec_stmt_error),
                            vec![],
                        )))
                    })?;
                rt.attach_known_fact_ids_to_infer_result(&mut infers)?;
                let fact_id = rt.known_fact_id_for_fact(&proposition)?;
                conclusions.push(SuccessVerifyLocalFactWellDefinedResult {
                    proposition: proposition.clone(),
                    well_definedness: well_definedness
                        .recursive
                        .expect("recursive quantified conclusion WD result"),
                    store: SuccessStoreFactResult {
                        fact: proposition,
                        fact_id,
                        infers,
                    },
                });
            }
            let recursive = SuccessVerifyFactWellDefinedProofResult::ForallFact(Box::new(
                SuccessVerifyForallFactWellDefinedResult {
                    statement: forall_fact.clone(),
                    binder,
                    premises,
                    conclusions,
                },
            ));
            Ok((
                SuccessVerifyFactWellDefinedResult::new_recursive(recursive),
                certificate,
            ))
        })
    }

    /// Mathematical contract: the domain portion of a universal fact is
    /// well-defined when its dependent binder types and premises are
    /// meaningful in source order.
    pub fn verify_forall_fact_params_and_dom_well_defined(
        &mut self,
        forall_fact: &ForallFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.run_in_local_env(|rt| {
            rt.verify_forall_fact_params_and_dom_well_defined_inner(forall_fact, verify_state)
        })
    }

    /// Mathematical contract implementation: check the universal domain
    /// inside the already-created
    /// local scope, retaining each checked premise and its sound inferred
    /// consequences as assumptions for the obligations that follow it.
    fn verify_forall_fact_params_and_dom_well_defined_inner(
        &mut self,
        forall_fact: &ForallFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        let _parameter_infers = match self.define_params_with_type(
            &forall_fact.params_def_with_type,
            false,
            ParamObjType::Forall,
        ) {
            Ok(infers) => infers,
            Err(e) => {
                return Err(WellDefinedRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "failed to define parameters in forall fact".to_string(),
                    forall_fact.line_file.clone(),
                    Some(e),
                    vec![],
                ))
                .into())
            }
        };
        for dom_fact in forall_fact.dom_facts.iter() {
            let store_result = self.store_fact_with_well_defined_verification_and_infer(
                dom_fact.clone(),
                verify_state,
            );
            if let Err(exec_stmt_error) = store_result {
                return Err(WellDefinedRuntimeError(RuntimeErrorStruct::new(
                    None,
                    String::new(),
                    dom_fact.line_file(),
                    Some(exec_stmt_error),
                    vec![],
                ))
                .into());
            }
        }
        Ok(())
    }

    /// Mathematical contract: this non-quantified compound fact is
    /// well-defined exactly when its selected atomic/and/chain/or form is.
    pub fn verify_quantifier_free_fact_well_defined(
        &mut self,
        fact: &QuantifierFreeFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_fact_well_defined_result(&fact.clone().into(), verify_state)
            .map(|_| ())
    }

    /// Mathematical contract: this compound fact is well-defined exactly when
    /// its selected atomic/and/chain/or/exist form is.
    pub fn verify_exist_or_and_chain_atomic_fact_well_defined(
        &mut self,
        fact: &ExistOrAndChainAtomicFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_fact_well_defined_result(&fact.clone().to_fact(), verify_state)
            .map(|_| ())
    }

    /// Mathematical contract: a universal equivalence is well-defined only
    /// when both generated implication directions are independently
    /// well-defined.
    pub fn verify_forall_fact_with_iff_well_defined(
        &mut self,
        forall_fact_with_iff: &ForallFactWithIff,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_fact_well_defined_result(&forall_fact_with_iff.clone().into(), verify_state)
            .map(|_| ())
    }

    /// Mathematical contract: negating a universal fact adds no new object
    /// domain; it is well-defined exactly when the underlying universal is.
    pub fn verify_not_forall_fact_well_defined(
        &mut self,
        not_forall: &NotForallFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_fact_well_defined_result(&not_forall.clone().into(), verify_state)
            .map(|_| ())
    }
}
