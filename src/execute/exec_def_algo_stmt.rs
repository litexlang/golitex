use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub fn exec_def_algo_stmt(
        &mut self,
        def_algo_stmt: &DefAlgoStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.run_in_local_env(|rt| rt.exec_def_algo_stmt_verify_process(def_algo_stmt))?;
        self.store_def_algo(def_algo_stmt)?;
        Ok(NonFactualStmtSuccess::new_with_stmt(def_algo_stmt.clone().into()).into())
    }

    fn exec_def_algo_stmt_verify_process(
        &mut self,
        def_algo_stmt: &DefAlgoStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let function_name_obj: Obj = Identifier::new(def_algo_stmt.name.clone()).into();
        let fn_set_where_algo_belongs = match self.get_object_in_fn_set(&function_name_obj) {
            Some(fn_set) => fn_set,
            None => {
                return Err(Self::def_algo_verify_exec_error_without_message(
                    def_algo_stmt,
                ));
            }
        };

        let (requirement_facts_for_param, algo_param_defs_with_type) = self
            .collect_requirement_facts_and_algo_param_defs(
                def_algo_stmt,
                &fn_set_where_algo_belongs,
            )?;

        let fn_call_obj_for_verification = Self::build_algo_verification_fn_call_obj(def_algo_stmt);
        let requirement_dom_facts = Self::requirement_facts_to_exist_or_and_chain_dom_facts(
            def_algo_stmt,
            &requirement_facts_for_param,
        )?;

        self.verify_each_def_algo_case_implies_return(
            def_algo_stmt,
            &algo_param_defs_with_type,
            &fn_call_obj_for_verification,
            &requirement_dom_facts,
        )?;

        self.verify_def_algo_case_coverage_when_no_default_return(
            def_algo_stmt,
            &algo_param_defs_with_type,
            &requirement_dom_facts,
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
    ) -> Result<(Vec<Fact>, ParamDefWithType), RuntimeError> {
        self.requirement_facts_and_param_defs_for_fn_set_with_dom(
            def_algo_stmt,
            fn_set_where_algo_belongs,
        )
    }

    fn requirement_facts_and_param_defs_for_fn_set_with_dom(
        &self,
        def_algo_stmt: &DefAlgoStmt,
        fn_set_with_dom: &FnSetBody,
    ) -> Result<(Vec<Fact>, ParamDefWithType), RuntimeError> {
        let mut args_for_algo_params: Vec<Obj> = Vec::with_capacity(def_algo_stmt.params.len());
        for param_name in def_algo_stmt.params.iter() {
            args_for_algo_params.push(obj_for_bound_param_in_scope(
                param_name.clone(),
                ParamObjType::Forall,
            ));
        }

        let param_satisfy_fn_param_set_facts_atomic =
            ParamGroupWithSet::facts_for_args_satisfy_param_def_with_set_vec(
                self,
                &fn_set_with_dom.params_def_with_set,
                &args_for_algo_params,
                ParamObjType::Forall,
            )
            .map_err(|runtime_error| {
                Self::def_algo_verify_exec_error_with_message_and_optional_cause(
                    def_algo_stmt,
                    "algo verify: failed to build param in-set facts".to_string(),
                    Some(runtime_error),
                )
            })?;

        let fn_set_param_names = fn_set_with_dom.get_params();
        if fn_set_param_names.len() != def_algo_stmt.params.len() {
            return Err(
                Self::def_algo_verify_exec_error_with_message_and_optional_cause(
                    def_algo_stmt,
                    format!(
                    "algo verify: number of params mismatch (algo params: {}, fn set params: {})",
                    def_algo_stmt.params.len(),
                    fn_set_param_names.len()
                ),
                    None,
                ),
            );
        }

        let mut fn_set_param_name_to_algo_arg_obj: HashMap<String, Obj> = HashMap::new();
        for (fn_set_param_name, algo_param_name) in
            fn_set_param_names.iter().zip(def_algo_stmt.params.iter())
        {
            fn_set_param_name_to_algo_arg_obj.insert(
                fn_set_param_name.clone(),
                obj_for_bound_param_in_scope(algo_param_name.clone(), ParamObjType::Forall),
            );
        }

        let mut requirement_facts: Vec<Fact> = Vec::new();
        let mut algo_param_defs_with_type: Vec<ParamGroupWithParamType> =
            Vec::with_capacity(fn_set_with_dom.params_def_with_set.len());

        for param_def_with_set in fn_set_with_dom.params_def_with_set.iter() {
            let mut mapped_param_names: Vec<String> =
                Vec::with_capacity(param_def_with_set.params.len());
            for fn_set_param_name in param_def_with_set.params.iter() {
                match fn_set_param_name_to_algo_arg_obj.get(fn_set_param_name) {
                    Some(Obj::Atom(AtomObj::Identifier(identifier))) => {
                        mapped_param_names.push(identifier.name.clone());
                    }
                    Some(Obj::Atom(AtomObj::FnSet(p))) => {
                        mapped_param_names.push(p.name.clone());
                    }
                    Some(Obj::Atom(AtomObj::Forall(p))) => {
                        mapped_param_names.push(p.name.clone());
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
            let instantiated_param_type = match &param_def_with_set.param_type {
                ParamGroupWithSetTypeEnum::Set(set) => ParamType::Obj(
                    self.inst_obj(
                        set,
                        &fn_set_param_name_to_algo_arg_obj,
                        ParamObjType::Forall,
                    )
                    .map_err(|runtime_error| {
                        Self::def_algo_verify_exec_error_with_message_and_optional_cause(
                            def_algo_stmt,
                            "algo verify: failed to instantiate fn set param set".to_string(),
                            Some(runtime_error),
                        )
                    })?,
                ),
                ParamGroupWithSetTypeEnum::Struct(struct_ty) => self
                    .inst_param_type(
                        &ParamType::Struct(struct_ty.clone()),
                        &fn_set_param_name_to_algo_arg_obj,
                        ParamObjType::Forall,
                    )
                    .map_err(|runtime_error| {
                        Self::def_algo_verify_exec_error_with_message_and_optional_cause(
                            def_algo_stmt,
                            "algo verify: failed to instantiate fn set struct param type"
                                .to_string(),
                            Some(runtime_error),
                        )
                    })?,
            };
            algo_param_defs_with_type.push(ParamGroupWithParamType::new(
                mapped_param_names,
                instantiated_param_type,
            ));
        }

        for in_fact_atomic in param_satisfy_fn_param_set_facts_atomic.iter() {
            requirement_facts.push(in_fact_atomic.clone().into());
        }
        for dom_fact in fn_set_with_dom.dom_facts.iter() {
            let instantiated_dom_fact = self
                .inst_or_and_chain_atomic_fact(
                    dom_fact,
                    &fn_set_param_name_to_algo_arg_obj,
                    ParamObjType::Forall,
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

    fn build_algo_verification_fn_call_obj(def_algo_stmt: &DefAlgoStmt) -> Obj {
        let mut fn_call_arg_boxes: Vec<Box<Obj>> = Vec::with_capacity(def_algo_stmt.params.len());
        for algo_param_name in def_algo_stmt.params.iter() {
            fn_call_arg_boxes.push(Box::new(obj_for_bound_param_in_scope(
                algo_param_name.clone(),
                ParamObjType::Forall,
            )));
        }
        FnObj::new(
            FnObjHead::Identifier(Identifier::new(def_algo_stmt.name.clone())),
            vec![fn_call_arg_boxes],
        )
        .into()
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

    fn def_algo_verification_forall_param_map(algo_param_names: &[String]) -> HashMap<String, Obj> {
        let mut param_to_arg_map = HashMap::with_capacity(algo_param_names.len());
        for name in algo_param_names.iter() {
            param_to_arg_map.insert(
                name.clone(),
                obj_for_bound_param_in_scope(name.clone(), ParamObjType::Forall),
            );
        }
        param_to_arg_map
    }

    fn forall_fact_for_def_algo_case(
        &self,
        algo_param_defs_with_type: &ParamDefWithType,
        requirement_dom_facts: &[ExistOrAndChainAtomicFact],
        algo_case: &AlgoCase,
        fn_call_obj: &Obj,
        algo_param_names: &[String],
    ) -> Result<Fact, RuntimeError> {
        let param_to_arg_map = Self::def_algo_verification_forall_param_map(algo_param_names);
        let inst_condition = self.inst_atomic_fact(
            &algo_case.condition,
            &param_to_arg_map,
            ParamObjType::Forall,
            None,
        )?;
        let inst_return_value = self.inst_obj(
            &algo_case.return_stmt.value,
            &param_to_arg_map,
            ParamObjType::Forall,
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

        Ok(ForallFact::new(
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
    ) -> Result<(), RuntimeError> {
        let verify_state = VerifyState::new(0, false);
        for algo_case in def_algo_stmt.cases.iter() {
            let case_forall_fact = self.forall_fact_for_def_algo_case(
                algo_param_defs_with_type,
                requirement_dom_facts,
                algo_case,
                fn_call_obj,
                &def_algo_stmt.params,
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

    fn verify_def_algo_case_coverage_when_no_default_return(
        &mut self,
        def_algo_stmt: &DefAlgoStmt,
        algo_param_defs_with_type: &ParamDefWithType,
        requirement_dom_facts: &[ExistOrAndChainAtomicFact],
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

        let param_to_arg_map = Self::def_algo_verification_forall_param_map(&def_algo_stmt.params);
        let mut case_conditions: Vec<AndChainAtomicFact> =
            Vec::with_capacity(def_algo_stmt.cases.len());
        for algo_case in def_algo_stmt.cases.iter() {
            let inst_condition = self.inst_atomic_fact(
                &algo_case.condition,
                &param_to_arg_map,
                ParamObjType::Forall,
                None,
            )?;
            case_conditions.push(inst_condition.into());
        }
        let coverage_or_fact = OrFact::new(case_conditions, def_algo_stmt.line_file.clone());
        let coverage_forall_fact = ForallFact::new(
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

        let verify_state = VerifyState::new(0, false);
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
