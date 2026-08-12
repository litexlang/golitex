use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub fn exec_def_algo_stmt(
        &mut self,
        def_algo_stmt: &DefAlgoStmt,
    ) -> Result<StmtResult, RuntimeError> {
        if self.current_execution_is_trusted_file() {
            self.store_def_algo(def_algo_stmt)?;
            return Ok(NonFactualStmtSuccess::new_with_stmt(def_algo_stmt.clone().into()).into());
        }

        self.run_in_local_env(|rt| rt.exec_def_algo_stmt_verify_process(def_algo_stmt))?;
        self.store_def_algo(def_algo_stmt)?;
        Ok(NonFactualStmtSuccess::new_with_stmt(def_algo_stmt.clone().into()).into())
    }

    fn exec_def_algo_stmt_verify_process(
        &mut self,
        def_algo_stmt: &DefAlgoStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let function_name_obj = self.declared_identifier_obj(&def_algo_stmt.name);
        let fn_set_where_algo_belongs = match self.get_object_in_fn_set(&function_name_obj) {
            Some(fn_set) => fn_set,
            None => {
                return Err(Self::def_algo_verify_exec_error_without_message(
                    def_algo_stmt,
                ));
            }
        };
        let (_, algo_param_to_forall_obj) = self.fresh_binder_retag_plan_for_bindings(
            &def_algo_stmt.param_bindings,
            ParamObjType::Forall,
        );

        let (requirement_facts_for_param, algo_param_defs_with_type) = self
            .collect_requirement_facts_and_algo_param_defs(
                def_algo_stmt,
                &fn_set_where_algo_belongs,
                &algo_param_to_forall_obj,
            )?;

        let fn_call_obj_for_verification =
            self.build_algo_verification_fn_call_obj(def_algo_stmt, &algo_param_to_forall_obj);
        let requirement_dom_facts = Self::requirement_facts_to_exist_or_and_chain_dom_facts(
            def_algo_stmt,
            &requirement_facts_for_param,
        )?;

        self.verify_each_def_algo_case_implies_return(
            def_algo_stmt,
            &algo_param_defs_with_type,
            &fn_call_obj_for_verification,
            &requirement_dom_facts,
            &algo_param_to_forall_obj,
        )?;

        self.verify_def_algo_default_implies_return(
            def_algo_stmt,
            &algo_param_defs_with_type,
            &fn_call_obj_for_verification,
            &requirement_dom_facts,
            &algo_param_to_forall_obj,
        )?;

        self.verify_def_algo_case_coverage_when_no_default_return(
            def_algo_stmt,
            &algo_param_defs_with_type,
            &requirement_dom_facts,
            &algo_param_to_forall_obj,
        )?;

        Ok(NonFactualStmtSuccess::new_with_stmt(def_algo_stmt.clone().into()).into())
    }

    fn def_algo_verify_exec_error_without_message(def_algo_stmt: &DefAlgoStmt) -> RuntimeError {
        short_exec_error(def_algo_stmt.clone().into(), "", None, vec![])
    }

    fn def_algo_verify_exec_error_with_message_and_optional_cause(
        def_algo_stmt: &DefAlgoStmt,
        message: String,
        cause: Option<RuntimeError>,
    ) -> RuntimeError {
        short_exec_error(def_algo_stmt.clone().into(), message, cause, vec![])
    }

    fn collect_requirement_facts_and_algo_param_defs(
        &self,
        def_algo_stmt: &DefAlgoStmt,
        fn_set_where_algo_belongs: &FnSetBody,
        algo_param_to_forall_obj: &HashMap<String, Obj>,
    ) -> Result<(Vec<Fact>, ParamDefWithType), RuntimeError> {
        self.requirement_facts_and_param_defs_for_fn_set_with_dom(
            def_algo_stmt,
            fn_set_where_algo_belongs,
            algo_param_to_forall_obj,
        )
    }

    fn requirement_facts_and_param_defs_for_fn_set_with_dom(
        &self,
        def_algo_stmt: &DefAlgoStmt,
        fn_set_with_dom: &FnSetBody,
        algo_param_to_forall_obj: &HashMap<String, Obj>,
    ) -> Result<(Vec<Fact>, ParamDefWithType), RuntimeError> {
        let mut args_for_algo_params: Vec<Obj> =
            Vec::with_capacity(def_algo_stmt.param_bindings.len());
        for param_binding in def_algo_stmt.param_bindings.iter() {
            args_for_algo_params
                .push(algo_param_to_forall_obj[param_binding.name()].clone());
        }

        let param_satisfy_fn_param_set_facts_atomic =
            ParamGroupWithSet::facts_for_args_satisfy_param_def_with_set_vec(
                self,
                &fn_set_with_dom.params_def_with_set,
                &args_for_algo_params,
                ParamObjType::BinderRetag(BinderRetagSource::FnSet),
            )
            .map_err(|runtime_error| {
                Self::def_algo_verify_exec_error_with_message_and_optional_cause(
                    def_algo_stmt,
                    "algo verify: failed to build param in-set facts".to_string(),
                    Some(runtime_error),
                )
            })?;

        let fn_set_param_bindings = fn_set_with_dom.params_def_with_set.collect_param_bindings();
        if fn_set_param_bindings.len() != def_algo_stmt.param_bindings.len() {
            return Err(
                Self::def_algo_verify_exec_error_with_message_and_optional_cause(
                    def_algo_stmt,
                    format!(
                        "algo verify: number of params mismatch (algo params: {}, fn set params: {})",
                        def_algo_stmt.param_bindings.len(),
                        fn_set_param_bindings.len()
                    ),
                    None,
                ),
            );
        }

        let mut fn_set_param_name_to_algo_arg_obj: HashMap<String, Obj> = HashMap::new();
        for (fn_set_param_binding, algo_param_binding) in fn_set_param_bindings
            .iter()
            .zip(def_algo_stmt.param_bindings.iter())
        {
            insert_symbol_substitution(
                &mut fn_set_param_name_to_algo_arg_obj,
                fn_set_param_binding,
                algo_param_to_forall_obj[&algo_param_binding.substitution_key()].clone(),
            );
        }

        let mut requirement_facts: Vec<Fact> = Vec::new();
        let mut algo_param_defs_with_type: Vec<ParamGroupWithParamType> =
            Vec::with_capacity(fn_set_with_dom.params_def_with_set.len());
        let mut active_fn_set_param_map = HashMap::new();

        for param_def_with_set in fn_set_with_dom.params_def_with_set.iter() {
            let mut mapped_param_names: Vec<String> =
                Vec::with_capacity(param_def_with_set.params.len());
            for fn_set_param_binding in param_def_with_set.params.iter() {
                let fn_set_param_name = fn_set_param_binding.name();
                match fn_set_param_name_to_algo_arg_obj.get(fn_set_param_name) {
                    Some(Obj::Atom(AtomObj::Identifier(identifier))) => {
                        mapped_param_names.push(identifier.name.clone());
                    }
                    Some(Obj::Atom(AtomObj::FnSet(p))) => {
                        mapped_param_names.push(p.name().to_string());
                    }
                    Some(Obj::Atom(AtomObj::Forall(p))) => {
                        mapped_param_names.push(p.name().to_string());
                    }
                    _ => {
                        return Err(
                            Self::def_algo_verify_exec_error_with_message_and_optional_cause(
                                def_algo_stmt,
                                "algo verify: param map internal error".to_string(),
                                None,
                            ),
                        );
                    }
                }
            }
            let instantiated_param_type = ParamType::Obj(
                self.inst_obj(
                    param_def_with_set.set_obj(),
                    &active_fn_set_param_map,
                    ParamObjType::BinderRetag(BinderRetagSource::FnSet),
                )
                .map_err(|runtime_error| {
                    Self::def_algo_verify_exec_error_with_message_and_optional_cause(
                        def_algo_stmt,
                        "algo verify: failed to instantiate fn set param set".to_string(),
                        Some(runtime_error),
                    )
                })?,
            );
            algo_param_defs_with_type.push(
                self.fresh_param_group_with_type(mapped_param_names, instantiated_param_type)?,
            );
            for fn_set_param_binding in &param_def_with_set.params {
                let fn_set_param_name = fn_set_param_binding.name();
                insert_symbol_substitution(
                    &mut active_fn_set_param_map,
                    fn_set_param_binding,
                    fn_set_param_name_to_algo_arg_obj[fn_set_param_name].clone(),
                );
            }
        }

        for in_fact_atomic in param_satisfy_fn_param_set_facts_atomic.iter() {
            requirement_facts.push(in_fact_atomic.clone().into());
        }
        for dom_fact in fn_set_with_dom.dom_facts.iter() {
            let instantiated_dom_fact = self
                .inst_or_and_chain_atomic_fact(
                    dom_fact,
                    &fn_set_param_name_to_algo_arg_obj,
                    ParamObjType::BinderRetag(BinderRetagSource::FnSet),
                    None,
                )
                .map_err(|runtime_error| {
                    Self::def_algo_verify_exec_error_with_message_and_optional_cause(
                        def_algo_stmt,
                        "algo verify: failed to instantiate fn set dom fact".to_string(),
                        Some(runtime_error),
                    )
                })?;
            requirement_facts.push(instantiated_dom_fact.into());
        }

        Ok((
            requirement_facts,
            ParamDefWithType::new(algo_param_defs_with_type),
        ))
    }

    fn build_algo_verification_fn_call_obj(
        &self,
        def_algo_stmt: &DefAlgoStmt,
        algo_param_to_forall_obj: &HashMap<String, Obj>,
    ) -> Obj {
        let mut fn_call_arg_boxes: Vec<Box<Obj>> =
            Vec::with_capacity(def_algo_stmt.param_bindings.len());
        for param_binding in def_algo_stmt.param_bindings.iter() {
            fn_call_arg_boxes.push(Box::new(
                algo_param_to_forall_obj[param_binding.name()].clone(),
            ));
        }
        let function_head = FnObjHead::given_an_atom_return_a_fn_obj_head(
            self.declared_identifier_obj(&def_algo_stmt.name),
        )
        .expect("declared algorithm name is a function head");
        FnObj::new(function_head, vec![fn_call_arg_boxes]).into()
    }

    fn requirement_facts_to_exist_or_and_chain_dom_facts(
        def_algo_stmt: &DefAlgoStmt,
        requirement_facts: &[Fact],
    ) -> Result<Vec<ExistOrAndChainAtomicFact>, RuntimeError> {
        let mut requirement_dom_facts: Vec<ExistOrAndChainAtomicFact> =
            Vec::with_capacity(requirement_facts.len());
        for requirement_fact in requirement_facts.iter() {
            let requirement_dom_fact = match requirement_fact {
                Fact::AtomicFact(atomic_fact) => atomic_fact.clone().into(),
                Fact::AndFact(and_fact) => and_fact.clone().into(),
                Fact::ChainFact(chain_fact) => chain_fact.clone().into(),
                Fact::OrFact(or_fact) => or_fact.clone().into(),
                Fact::ExistFact(exist_fact) => exist_fact.clone().into(),
                Fact::ForallFact(_) | Fact::ForallFactWithIff(_) | Fact::NotForall(_) => {
                    return Err(
                        Self::def_algo_verify_exec_error_with_message_and_optional_cause(
                            def_algo_stmt,
                            "algo verify: requirement fact cannot be forall or not forall"
                                .to_string(),
                            None,
                        ),
                    );
                }
            };
            requirement_dom_facts.push(requirement_dom_fact);
        }
        Ok(requirement_dom_facts)
    }

    fn forall_fact_for_def_algo_case(
        &self,
        algo_param_defs_with_type: &ParamDefWithType,
        requirement_dom_facts: &[ExistOrAndChainAtomicFact],
        algo_case: &AlgoCase,
        fn_call_obj: &Obj,
        algo_param_to_forall_obj: &HashMap<String, Obj>,
    ) -> Result<Fact, RuntimeError> {
        let inst_condition = self.inst_atomic_fact(
            &algo_case.condition,
            algo_param_to_forall_obj,
            ParamObjType::BinderRetag(BinderRetagSource::DefAlgo),
            None,
        )?;
        let inst_return_value = self.inst_obj(
            &algo_case.return_stmt.value,
            algo_param_to_forall_obj,
            ParamObjType::BinderRetag(BinderRetagSource::DefAlgo),
        )?;

        let mut case_dom_facts: Vec<Fact> = Vec::with_capacity(requirement_dom_facts.len() + 1);
        for requirement_dom_fact in requirement_dom_facts.iter() {
            case_dom_facts.push(requirement_dom_fact.clone().to_fact());
        }
        case_dom_facts.push(inst_condition.into());

        let case_then_facts = vec![EqualFact::new(
            fn_call_obj.clone(),
            inst_return_value,
            algo_case.line_file.clone(),
        )
        .into()];

        Ok(ForallFact::new_canonical_forall(
            algo_param_defs_with_type.clone(),
            case_dom_facts,
            case_then_facts,
            algo_case.line_file.clone(),
        )?
        .into())
    }

    fn verify_each_def_algo_case_implies_return(
        &mut self,
        def_algo_stmt: &DefAlgoStmt,
        algo_param_defs_with_type: &ParamDefWithType,
        fn_call_obj: &Obj,
        requirement_dom_facts: &[ExistOrAndChainAtomicFact],
        algo_param_to_forall_obj: &HashMap<String, Obj>,
    ) -> Result<(), RuntimeError> {
        let verify_state = UseContextVerifyState::new(0, false);
        for algo_case in def_algo_stmt.cases.iter() {
            let case_forall_fact = self.forall_fact_for_def_algo_case(
                algo_param_defs_with_type,
                requirement_dom_facts,
                algo_case,
                fn_call_obj,
                algo_param_to_forall_obj,
            )?;
            self.verify_fact_return_err_if_not_true(&case_forall_fact, &verify_state)
                .map_err(|runtime_error| {
                    Self::def_algo_verify_exec_error_with_message_and_optional_cause(
                        def_algo_stmt,
                        format!(
                            "algo verify: case `{}` does not imply expected return",
                            algo_case
                        ),
                        Some(runtime_error),
                    )
                })?;
        }
        Ok(())
    }

    fn verify_def_algo_default_implies_return(
        &mut self,
        def_algo_stmt: &DefAlgoStmt,
        algo_param_defs_with_type: &ParamDefWithType,
        fn_call_obj: &Obj,
        requirement_dom_facts: &[ExistOrAndChainAtomicFact],
        algo_param_to_forall_obj: &HashMap<String, Obj>,
    ) -> Result<(), RuntimeError> {
        let Some(default_return) = &def_algo_stmt.default_return else {
            return Ok(());
        };

        let mut dom_facts: Vec<Fact> = requirement_dom_facts
            .iter()
            .cloned()
            .map(ExistOrAndChainAtomicFact::to_fact)
            .collect();
        for algo_case in &def_algo_stmt.cases {
            let condition = self.inst_atomic_fact(
                &algo_case.condition,
                algo_param_to_forall_obj,
                ParamObjType::BinderRetag(BinderRetagSource::DefAlgo),
                None,
            )?;
            let negated_condition = condition.logical_negation().map_err(|runtime_error| {
                Self::def_algo_verify_exec_error_with_message_and_optional_cause(
                    def_algo_stmt,
                    format!(
                        "algo verify: default branch cannot negate case condition `{}`",
                        condition
                    ),
                    Some(runtime_error),
                )
            })?;
            dom_facts.push(negated_condition.into());
        }
        let return_value = self.inst_obj(
            &default_return.value,
            algo_param_to_forall_obj,
            ParamObjType::BinderRetag(BinderRetagSource::DefAlgo),
        )?;
        let verification_fact: Fact = ForallFact::new_canonical_forall(
            algo_param_defs_with_type.clone(),
            dom_facts,
            vec![EqualFact::new(
                fn_call_obj.clone(),
                return_value,
                default_return.line_file.clone(),
            )
            .into()],
            default_return.line_file.clone(),
        )?
        .into();

        self.verify_fact_return_err_if_not_true(
            &verification_fact,
            &UseContextVerifyState::new(0, false),
        )
        .map_err(|runtime_error| {
            Self::def_algo_verify_exec_error_with_message_and_optional_cause(
                def_algo_stmt,
                "algo verify: default return does not equal the declared function".to_string(),
                Some(runtime_error),
            )
        })?;
        Ok(())
    }

    fn verify_def_algo_case_coverage_when_no_default_return(
        &mut self,
        def_algo_stmt: &DefAlgoStmt,
        algo_param_defs_with_type: &ParamDefWithType,
        requirement_dom_facts: &[ExistOrAndChainAtomicFact],
        algo_param_to_forall_obj: &HashMap<String, Obj>,
    ) -> Result<(), RuntimeError> {
        if def_algo_stmt.default_return.is_some() {
            return Ok(());
        }

        if def_algo_stmt.cases.is_empty() {
            return Err(
                Self::def_algo_verify_exec_error_with_message_and_optional_cause(
                    def_algo_stmt,
                    "algo verify: no case and no default return".to_string(),
                    None,
                ),
            );
        }

        let mut case_conditions: Vec<AndChainAtomicFact> =
            Vec::with_capacity(def_algo_stmt.cases.len());
        for algo_case in def_algo_stmt.cases.iter() {
            let inst_condition = self.inst_atomic_fact(
                &algo_case.condition,
                algo_param_to_forall_obj,
                ParamObjType::BinderRetag(BinderRetagSource::DefAlgo),
                None,
            )?;
            case_conditions.push(inst_condition.into());
        }
        let coverage_or_fact = OrFact::new(case_conditions, def_algo_stmt.line_file.clone());
        let coverage_forall_fact = ForallFact::new_canonical_forall(
            algo_param_defs_with_type.clone(),
            requirement_dom_facts
                .iter()
                .cloned()
                .map(ExistOrAndChainAtomicFact::to_fact)
                .collect(),
            vec![ExistOrAndChainAtomicFact::OrFact(coverage_or_fact)],
            def_algo_stmt.line_file.clone(),
        )?
        .into();

        let verify_state = UseContextVerifyState::new(0, false);
        self.verify_fact_return_err_if_not_true(&coverage_forall_fact, &verify_state)
            .map_err(|runtime_error| {
                Self::def_algo_verify_exec_error_with_message_and_optional_cause(
                    def_algo_stmt,
                    "algo verify: cases do not cover all situations".to_string(),
                    Some(runtime_error),
                )
            })?;

        Ok(())
    }
}
