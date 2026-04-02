use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub fn exec_def_algo_stmt(
        &mut self,
        def_algo_stmt: &DefAlgoStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        self._exec_def_algo_stmt_verify_process(def_algo_stmt)?;
        self.store_def_algo(def_algo_stmt)?;
        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::DefAlgoStmt(def_algo_stmt.clone()),
                InferResult::new(),
                vec![],
            ),
        ))
    }

    fn _exec_def_algo_stmt_verify_process(
        &mut self,
        def_algo_stmt: &DefAlgoStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        self.push_env();

        let result = self.exec_def_algo_stmt_verify_process_body(def_algo_stmt);

        self.pop_env();

        result
    }

    fn exec_def_algo_stmt_verify_process_body(
        &mut self,
        def_algo_stmt: &DefAlgoStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        let function_name_obj = Obj::Identifier(Identifier::new(def_algo_stmt.name.clone()));
        let fn_set_where_algo_belongs =
            match self.get_fn_set_where_fn_belongs_to(&function_name_obj) {
                Some(fn_set) => fn_set,
                None => {
                    return Err(Self::def_algo_verify_exec_error_without_message(
                        def_algo_stmt,
                    ));
                }
            };

        let (requirement_facts_for_param, algo_param_defs_with_type) =
            self.collect_requirement_facts_and_algo_param_defs(
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

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::DefAlgoStmt(def_algo_stmt.clone()),
                InferResult::new(),
                vec![],
            ),
        ))
    }

    fn def_algo_verify_exec_error_without_message(def_algo_stmt: &DefAlgoStmt) -> ExecStmtError {
        ExecStmtError::new_with_stmt(
            Stmt::DefAlgoStmt(def_algo_stmt.clone()),
            "".to_string(),
            None,
            vec![],
        )
    }

    fn def_algo_verify_exec_error_with_message_and_optional_cause(
        def_algo_stmt: &DefAlgoStmt,
        message: String,
        cause: Option<RuntimeError>,
    ) -> ExecStmtError {
        ExecStmtError::with_message_and_cause(
            Stmt::DefAlgoStmt(def_algo_stmt.clone()),
            message,
            cause,
            vec![],
        )
    }

    fn collect_requirement_facts_and_algo_param_defs(
        &self,
        def_algo_stmt: &DefAlgoStmt,
        fn_set_where_algo_belongs: &FnSetWithParams,
    ) -> Result<(Vec<Fact>, Vec<ParamDefWithParamType>), ExecStmtError> {
        self.requirement_facts_and_param_defs_for_fn_set_with_dom(
            def_algo_stmt,
            fn_set_where_algo_belongs,
        )
    }

    fn requirement_facts_and_param_defs_for_fn_set_with_dom(
        &self,
        def_algo_stmt: &DefAlgoStmt,
        fn_set_with_dom: &FnSetWithParams,
    ) -> Result<(Vec<Fact>, Vec<ParamDefWithParamType>), ExecStmtError> {
        let mut args_for_algo_params: Vec<Obj> = Vec::with_capacity(def_algo_stmt.params.len());
        for param_name in def_algo_stmt.params.iter() {
            args_for_algo_params.push(Obj::Identifier(Identifier::new(param_name.clone())));
        }

        let param_satisfy_fn_param_set_facts_atomic =
            ParamDefWithParamSet::facts_for_args_satisfy_param_def_with_set_vec(
                self,
                &fn_set_with_dom.params_def_with_set,
                &args_for_algo_params,
            )
            .map_err(|runtime_error| {
                Self::def_algo_verify_exec_error_with_message_and_optional_cause(
                    def_algo_stmt,
                    "algo verify: failed to build param in-set facts".to_string(),
                    Some(runtime_error),
                )
            })?;

        let fn_set_param_names = fn_set_with_dom.params();
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
                Obj::Identifier(Identifier::new(algo_param_name.clone())),
            );
        }

        let mut requirement_facts: Vec<Fact> = Vec::new();
        let mut algo_param_defs_with_type: Vec<ParamDefWithParamType> =
            Vec::with_capacity(fn_set_with_dom.params_def_with_set.len());

        for param_def_with_set in fn_set_with_dom.params_def_with_set.iter() {
            let mut mapped_param_names: Vec<String> =
                Vec::with_capacity(param_def_with_set.0.len());
            for fn_set_param_name in param_def_with_set.0.iter() {
                match fn_set_param_name_to_algo_arg_obj.get(fn_set_param_name) {
                    Some(Obj::Identifier(identifier)) => {
                        mapped_param_names.push(identifier.name.clone());
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
            let instantiated_param_set = self
                .inst_obj(&param_def_with_set.1, &fn_set_param_name_to_algo_arg_obj)
                .map_err(|runtime_error| {
                    Self::def_algo_verify_exec_error_with_message_and_optional_cause(
                        def_algo_stmt,
                        "algo verify: failed to instantiate fn set param set".to_string(),
                        Some(runtime_error),
                    )
                })?;
            algo_param_defs_with_type.push(ParamDefWithParamType(
                mapped_param_names,
                ParamType::Obj(instantiated_param_set),
            ));
        }

        for in_fact_atomic in param_satisfy_fn_param_set_facts_atomic.iter() {
            requirement_facts.push(Fact::AtomicFact(in_fact_atomic.clone()));
        }
        for dom_fact in fn_set_with_dom.dom_facts.iter() {
            let instantiated_dom_fact = self
                .inst_or_and_chain_atomic_fact(dom_fact, &fn_set_param_name_to_algo_arg_obj)
                .map_err(|runtime_error| {
                    Self::def_algo_verify_exec_error_with_message_and_optional_cause(
                        def_algo_stmt,
                        "algo verify: failed to instantiate fn set dom fact".to_string(),
                        Some(runtime_error),
                    )
                })?;
            requirement_facts.push(instantiated_dom_fact.to_fact());
        }

        Ok((requirement_facts, algo_param_defs_with_type))
    }

    fn build_algo_verification_fn_call_obj(def_algo_stmt: &DefAlgoStmt) -> Obj {
        let mut fn_call_arg_boxes: Vec<Box<Obj>> = Vec::with_capacity(def_algo_stmt.params.len());
        for algo_param_name in def_algo_stmt.params.iter() {
            fn_call_arg_boxes.push(Box::new(Obj::Identifier(Identifier::new(
                algo_param_name.clone(),
            ))));
        }
        Obj::FnObj(FnObj::new(
            Atom::Identifier(Identifier::new(def_algo_stmt.name.clone())),
            vec![fn_call_arg_boxes],
        ))
    }

    fn requirement_facts_to_exist_or_and_chain_dom_facts(
        def_algo_stmt: &DefAlgoStmt,
        requirement_facts: &[Fact],
    ) -> Result<Vec<ExistOrAndChainAtomicFact>, ExecStmtError> {
        let mut requirement_dom_facts: Vec<ExistOrAndChainAtomicFact> =
            Vec::with_capacity(requirement_facts.len());
        for requirement_fact in requirement_facts.iter() {
            let requirement_dom_fact = match requirement_fact {
                Fact::AtomicFact(atomic_fact) => {
                    ExistOrAndChainAtomicFact::AtomicFact(atomic_fact.clone())
                }
                Fact::AndFact(and_fact) => ExistOrAndChainAtomicFact::AndFact(and_fact.clone()),
                Fact::ChainFact(chain_fact) => {
                    ExistOrAndChainAtomicFact::ChainFact(chain_fact.clone())
                }
                Fact::OrFact(or_fact) => ExistOrAndChainAtomicFact::OrFact(or_fact.clone()),
                Fact::ExistFact(exist_fact) => {
                    ExistOrAndChainAtomicFact::ExistFact(exist_fact.clone())
                }
                Fact::ForallFact(_) | Fact::ForallFactWithIff(_) => {
                    return Err(
                        Self::def_algo_verify_exec_error_with_message_and_optional_cause(
                            def_algo_stmt,
                            "algo verify: requirement fact cannot be forall".to_string(),
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
        algo_param_defs_with_type: &[ParamDefWithParamType],
        requirement_dom_facts: &[ExistOrAndChainAtomicFact],
        algo_case: &AlgoCase,
        fn_call_obj: &Obj,
    ) -> Fact {
        let mut case_dom_facts: Vec<ExistOrAndChainAtomicFact> =
            Vec::with_capacity(requirement_dom_facts.len() + 1);
        for requirement_dom_fact in requirement_dom_facts.iter() {
            case_dom_facts.push(requirement_dom_fact.clone());
        }
        case_dom_facts.push(ExistOrAndChainAtomicFact::AtomicFact(
            algo_case.condition.clone(),
        ));

        let case_then_facts = vec![ExistOrAndChainAtomicFact::AtomicFact(
            AtomicFact::EqualFact(EqualFact::new(
                fn_call_obj.clone(),
                algo_case.return_stmt.value.clone(),
                algo_case.line_file.clone(),
            )),
        )];

        Fact::ForallFact(ForallFact::new(
            algo_param_defs_with_type.to_vec(),
            case_dom_facts,
            case_then_facts,
            algo_case.line_file.clone(),
        ))
    }

    fn verify_each_def_algo_case_implies_return(
        &mut self,
        def_algo_stmt: &DefAlgoStmt,
        algo_param_defs_with_type: &[ParamDefWithParamType],
        fn_call_obj: &Obj,
        requirement_dom_facts: &[ExistOrAndChainAtomicFact],
    ) -> Result<(), ExecStmtError> {
        let verify_state = VerifyState::new(0, false);
        for algo_case in def_algo_stmt.cases.iter() {
            let case_forall_fact = Self::forall_fact_for_def_algo_case(
                algo_param_defs_with_type,
                requirement_dom_facts,
                algo_case,
                fn_call_obj,
            );
            self.verify_fact_return_err_if_not_true(&case_forall_fact, &verify_state)
                .map_err(|runtime_error| {
                    Self::def_algo_verify_exec_error_with_message_and_optional_cause(
                        def_algo_stmt,
                        format!(
                            "algo verify: case `{}` does not imply expected return",
                            algo_case
                        ),
                        Some(runtime_error.into()),
                    )
                })?;
        }
        Ok(())
    }

    fn verify_def_algo_case_coverage_when_no_default_return(
        &mut self,
        def_algo_stmt: &DefAlgoStmt,
        algo_param_defs_with_type: &[ParamDefWithParamType],
        requirement_dom_facts: &[ExistOrAndChainAtomicFact],
    ) -> Result<(), ExecStmtError> {
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
            case_conditions.push(AndChainAtomicFact::AtomicFact(algo_case.condition.clone()));
        }
        let coverage_or_fact = OrFact::new(case_conditions, def_algo_stmt.line_file.clone());
        let coverage_forall_fact = Fact::ForallFact(ForallFact::new(
            algo_param_defs_with_type.to_vec(),
            requirement_dom_facts.to_vec(),
            vec![ExistOrAndChainAtomicFact::OrFact(coverage_or_fact)],
            def_algo_stmt.line_file.clone(),
        ));

        let verify_state = VerifyState::new(0, false);
        self.verify_fact_return_err_if_not_true(&coverage_forall_fact, &verify_state)
            .map_err(|runtime_error| {
                Self::def_algo_verify_exec_error_with_message_and_optional_cause(
                    def_algo_stmt,
                    "algo verify: cases do not cover all situations".to_string(),
                    Some(runtime_error.into()),
                )
            })?;

        Ok(())
    }
}
