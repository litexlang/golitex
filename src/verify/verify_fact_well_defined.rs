use crate::prelude::*;

impl Runtime {
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
        match atomic_fact {
            AtomicFact::EqualFact(equal_fact) => {
                self.verify_equal_fact_well_defined(equal_fact, verify_state)
            }
            _ => self.verify_non_equational_atomic_fact_well_defined(atomic_fact, verify_state),
        }
    }

    /// Mathematical contract: `left = right` is meaningful exactly when both
    /// sides denote well-defined objects; equality itself is untyped.
    fn verify_equal_fact_well_defined(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&equal_fact.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&equal_fact.right, verify_state)?;
        Ok(())
    }

    /// Mathematical contract: a non-equality predicate application is
    /// meaningful only at its declared arity with well-defined arguments.
    /// Builtin partial predicates additionally require their mathematical
    /// domains, such as real operands for order and `N` for primality.
    fn verify_non_equational_atomic_fact_well_defined(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        // 1. predicate is defined, expected args length is equal to actual args length
        let name_string = atomic_fact.key();
        if is_builtin_predicate(&name_string) {
            let expected_len = atomic_fact.is_builtin_predicate_and_return_expected_args_len();
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
        } else {
            let expected_len = if let Some(predicate_definition) =
                self.get_prop_definition_by_name(&name_string)
            {
                predicate_definition.params_def_with_type.number_of_params()
            } else if let Some(abstract_prop_definition) =
                self.get_abstract_prop_definition_by_name(&name_string)
            {
                abstract_prop_definition.params.len()
            } else {
                return Err(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!("fact `{}` not defined", name_string),
                        atomic_fact.line_file(),
                    ),
                )
                .into());
            };

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

        // 2. all args are well-defined
        for arg in atomic_fact.args_ref() {
            self.verify_obj_well_defined_and_store_cache(arg, verify_state)?;
        }

        if name_string == PRIME {
            let arg = atomic_fact.args_ref()[0];
            let in_n: AtomicFact =
                InFact::new(arg.clone(), StandardSet::N.into(), atomic_fact.line_file()).into();
            if self.verify_atomic_fact(&in_n, verify_state)?.is_unknown() {
                return Err(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!("{} requires its argument to belong to N", atomic_fact),
                        atomic_fact.line_file(),
                    ),
                )
                .into());
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
            if self
                .verify_objects_are_known_reals(
                    real_args.as_slice(),
                    &atomic_fact.line_file(),
                    verify_state,
                )?
                .is_none()
            {
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
        }

        Ok(())
    }

    /// Mathematical contract: a conjunction is well-defined when every
    /// conjunct is well-defined in the same context.
    pub fn verify_and_fact_well_defined(
        &mut self,
        and_fact: &AndFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        for fact in and_fact.facts.iter() {
            self.verify_atomic_fact_well_defined(fact, verify_state)?;
        }
        Ok(())
    }

    /// Mathematical contract: a comparison chain is well-defined when every
    /// adjacent atomic comparison produced by the chain is well-defined.
    pub fn verify_chain_fact_well_defined(
        &mut self,
        chain_fact: &ChainFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        let facts = chain_fact.facts()?;
        for fact in facts.iter() {
            self.verify_atomic_fact_well_defined(fact, verify_state)?;
        }
        Ok(())
    }

    /// Mathematical contract: a disjunction is well-defined only when every
    /// branch is meaningful, independently of which branch is true.
    pub fn verify_or_fact_well_defined(
        &mut self,
        or_fact: &OrFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        for fact in or_fact.facts.iter() {
            self.verify_and_chain_atomic_fact_well_defined(fact, verify_state)?;
        }
        Ok(())
    }

    /// Mathematical contract: this restricted compound fact is well-defined
    /// exactly when the atomic, conjunction, or chain form it contains is.
    fn verify_and_chain_atomic_fact_well_defined(
        &mut self,
        fact: &AndChainAtomicFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        match fact {
            AndChainAtomicFact::AtomicFact(a) => {
                self.verify_atomic_fact_well_defined(a, verify_state)?
            }
            AndChainAtomicFact::AndFact(a) => self.verify_and_fact_well_defined(a, verify_state)?,
            AndChainAtomicFact::ChainFact(c) => {
                self.verify_chain_fact_well_defined(c, verify_state)?
            }
        }
        Ok(())
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
        let bindings = exist_fact.params_def_with_type().collect_param_bindings();
        let rename_map =
            self.visible_binding_conflict_rename_map(&bindings, ParamObjType::Exist)?;
        if !rename_map.is_empty() {
            let renamed = self.alpha_rename_exist_fact(exist_fact, &rename_map)?;
            return self.verify_exist_fact_well_defined(&renamed, verify_state);
        }

        self.run_in_local_env(|rt| {
            if let Err(e) = rt.define_params_with_type(
                exist_fact.params_def_with_type(),
                false,
                ParamObjType::Exist,
            ) {
                return Err(WellDefinedRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "failed to define parameters in exist fact".to_string(),
                    exist_fact.line_file(),
                    Some(e),
                    vec![],
                ))
                .into());
            }

            for fact in exist_fact.facts() {
                match fact {
                    ExistBodyFact::AtomicFact(f) => {
                        let body_fact = OrAndChainAtomicFact::AtomicFact(f.clone());
                        rt.verify_or_and_chain_atomic_fact_well_defined(&body_fact, verify_state)?;
                        rt.store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                            body_fact,
                        )?;
                    }
                    ExistBodyFact::AndFact(f) => {
                        let body_fact = OrAndChainAtomicFact::AndFact(f.clone());
                        rt.verify_or_and_chain_atomic_fact_well_defined(&body_fact, verify_state)?;
                        rt.store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                            body_fact,
                        )?;
                    }
                    ExistBodyFact::ChainFact(f) => {
                        let body_fact = OrAndChainAtomicFact::ChainFact(f.clone());
                        rt.verify_or_and_chain_atomic_fact_well_defined(&body_fact, verify_state)?;
                        rt.store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                            body_fact,
                        )?;
                    }
                    ExistBodyFact::OrFact(f) => {
                        let body_fact = OrAndChainAtomicFact::OrFact(f.clone());
                        rt.verify_or_and_chain_atomic_fact_well_defined(&body_fact, verify_state)?;
                        rt.store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                            body_fact,
                        )?;
                    }
                    ExistBodyFact::InlineForall(f) => {
                        rt.verify_forall_fact_well_defined(f, verify_state)?;
                        rt.store_forall_fact_without_well_defined_verified_and_infer(f.clone())?;
                    }
                }
            }
            Ok(())
        })
    }

    /// Mathematical contract: `forall x T: premises => conclusions` is
    /// well-defined when the binder types and premises are meaningful in order
    /// and every conclusion is meaningful under those local assumptions.
    pub fn verify_forall_fact_well_defined(
        &mut self,
        forall_fact: &ForallFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        let bindings = forall_fact.params_def_with_type.collect_param_bindings();
        let rename_map =
            self.visible_binding_conflict_rename_map(&bindings, ParamObjType::Forall)?;
        if !rename_map.is_empty() {
            let renamed = self.alpha_rename_forall_fact(forall_fact, &rename_map)?;
            return self.verify_forall_fact_well_defined(&renamed, verify_state);
        }

        self.run_in_local_env(|rt| {
            rt.verify_forall_fact_well_defined_inner(forall_fact, verify_state)
        })
    }

    /// Check a universal fact once and retain only sound side effects produced
    /// by conclusion well-definedness (for example, the return-carrier fact of
    /// a checked function application). Domain assumptions and conclusions are
    /// kept in the temporary preflight scope and never enter the certificate.
    pub fn verify_forall_fact_well_defined_and_collect_certificate(
        &mut self,
        forall_fact: &ForallFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<Environment, RuntimeError> {
        let bindings = forall_fact.params_def_with_type.collect_param_bindings();
        let rename_map =
            self.visible_binding_conflict_rename_map(&bindings, ParamObjType::Forall)?;
        if !rename_map.is_empty() {
            let renamed = self.alpha_rename_forall_fact(forall_fact, &rename_map)?;
            return self
                .verify_forall_fact_well_defined_and_collect_certificate(&renamed, verify_state);
        }

        self.run_in_local_env(|rt| {
            rt.verify_forall_fact_params_and_dom_well_defined_inner(forall_fact, verify_state)?;

            let mut certificate = Environment::new_empty_env();
            for fact in forall_fact.then_facts.iter() {
                let checked = rt.run_in_local_env_and_take(|checking_rt| {
                    checking_rt
                        .verify_exist_or_and_chain_atomic_fact_well_defined(fact, verify_state)
                });
                let (_, mut checked_side_effects) = checked.map_err(|exec_stmt_error| {
                    RuntimeError::from(WellDefinedRuntimeError(RuntimeErrorStruct::new(
                        None,
                        String::new(),
                        fact.line_file(),
                        Some(exec_stmt_error),
                        vec![],
                    )))
                })?;

                checked_side_effects.retain_only_well_definedness_certificate_data();
                certificate.merge_committed_child(checked_side_effects.clone())?;
                rt.top_level_env()
                    .merge_committed_child(checked_side_effects)?;

                rt.store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
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
            }
            Ok(certificate)
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
        if let Err(e) = self.define_params_with_type(
            &forall_fact.params_def_with_type,
            false,
            ParamObjType::Forall,
        ) {
            return Err(WellDefinedRuntimeError(RuntimeErrorStruct::new(
                None,
                "failed to define parameters in forall fact".to_string(),
                forall_fact.line_file.clone(),
                Some(e),
                vec![],
            ))
            .into());
        }

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

    /// Mathematical contract implementation: in one local scope, bind the
    /// domain, assume its premises, then check every conclusion.
    fn verify_forall_fact_well_defined_inner(
        &mut self,
        forall_fact: &ForallFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_forall_fact_params_and_dom_well_defined_inner(forall_fact, verify_state)?;
        for fact in forall_fact.then_facts.iter() {
            if let Err(exec_stmt_error) = self
                .store_exist_or_and_chain_atomic_fact_with_well_defined_verification_and_infer(
                    fact,
                    verify_state,
                )
            {
                return Err(WellDefinedRuntimeError(RuntimeErrorStruct::new(
                    None,
                    String::new(),
                    fact.line_file(),
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
    pub fn verify_or_and_chain_atomic_fact_well_defined(
        &mut self,
        fact: &OrAndChainAtomicFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        match fact {
            OrAndChainAtomicFact::AtomicFact(a) => {
                self.verify_atomic_fact_well_defined(a, verify_state)?
            }
            OrAndChainAtomicFact::AndFact(a) => {
                self.verify_and_fact_well_defined(a, verify_state)?
            }
            OrAndChainAtomicFact::ChainFact(c) => {
                self.verify_chain_fact_well_defined(c, verify_state)?
            }
            OrAndChainAtomicFact::OrFact(o) => self.verify_or_fact_well_defined(o, verify_state)?,
        }
        Ok(())
    }

    /// Mathematical contract: this compound fact is well-defined exactly when
    /// its selected atomic/and/chain/or/exist form is.
    pub fn verify_exist_or_and_chain_atomic_fact_well_defined(
        &mut self,
        fact: &ExistOrAndChainAtomicFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        match fact {
            ExistOrAndChainAtomicFact::AtomicFact(a) => {
                self.verify_atomic_fact_well_defined(a, verify_state)?
            }
            ExistOrAndChainAtomicFact::AndFact(a) => {
                self.verify_and_fact_well_defined(a, verify_state)?
            }
            ExistOrAndChainAtomicFact::ChainFact(c) => {
                self.verify_chain_fact_well_defined(c, verify_state)?
            }
            ExistOrAndChainAtomicFact::OrFact(o) => {
                self.verify_or_fact_well_defined(o, verify_state)?
            }
            ExistOrAndChainAtomicFact::ExistFact(e) => {
                self.verify_exist_fact_well_defined(e, verify_state)?
            }
        }
        Ok(())
    }

    /// Mathematical contract: a universal equivalence is well-defined only
    /// when both generated implication directions are independently
    /// well-defined.
    pub fn verify_forall_fact_with_iff_well_defined(
        &mut self,
        forall_fact_with_iff: &ForallFactWithIff,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        let (forall_then_implies_iff, forall_iff_implies_then) =
            forall_fact_with_iff.to_two_forall_facts()?;
        self.verify_forall_fact_well_defined(&forall_then_implies_iff, verify_state)?;
        self.verify_forall_fact_well_defined(&forall_iff_implies_then, verify_state)
    }

    /// Mathematical contract: negating a universal fact adds no new object
    /// domain; it is well-defined exactly when the underlying universal is.
    pub fn verify_not_forall_fact_well_defined(
        &mut self,
        not_forall: &NotForallFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_forall_fact_well_defined(&not_forall.forall_fact, verify_state)
    }
}
