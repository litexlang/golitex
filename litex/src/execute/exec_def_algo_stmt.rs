use crate::error::ExecStmtError;
use crate::execute::Runtime;
use crate::fact::AndChainAtomicFact;
use crate::fact::{
    AtomicFact, EqualFact, ExistOrAndChainAtomicFact, Fact, ForallFact, InFact, OrFact,
};
use crate::infer::InferResult;
use crate::obj::{Atom, FnObj, FnSetObj, Identifier, Obj};
use crate::result::NonErrStmtExecResult;
use crate::result::NonFactualStmtSuccess;
use crate::stmt::define_algorithm_stmt::DefAlgoStmt;
use crate::stmt::parameter_def::ParamDefWithParamSet;
use crate::stmt::parameter_def::{ParamDefWithParamType, ParamType};
use crate::stmt::Stmt;
use crate::verify::VerifyState;
use std::collections::HashMap;

impl<'a> Runtime<'a> {
    pub fn exec_def_algo_stmt(
        &mut self,
        def_algo_stmt: &DefAlgoStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        self.exec_def_algo_stmt_verify_process(def_algo_stmt)?;
        self.store_def_algo(def_algo_stmt)?;
        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::DefAlgoStmt(def_algo_stmt.clone()),
                InferResult::new(),
                vec![],
            ),
        ))
    }

    fn exec_def_algo_stmt_verify_process(
        &mut self,
        def_algo_stmt: &DefAlgoStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        self.runtime_context.push_env();

        let result = self.exec_def_algo_stmt_verify_process_body(def_algo_stmt);

        self.runtime_context.pop_env();

        result
    }

    fn exec_def_algo_stmt_verify_process_body(
        &mut self,
        def_algo_stmt: &DefAlgoStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        let set_where_fn_belongs_to =
            match self
                .runtime_context
                .get_fn_set_where_fn_belongs_to(&Atom::Identifier(Identifier::new(
                    def_algo_stmt.name.clone(),
                ))) {
                Some(fn_set) => fn_set,
                None => {
                    return Err(ExecStmtError::new(
                        Stmt::DefAlgoStmt(def_algo_stmt.clone()),
                        None,
                        vec![],
                    ))
                }
            };

        let (requirement_facts_for_parma, algo_param_defs_with_type): (
            Vec<Fact>,
            Vec<ParamDefWithParamType>,
        ) = match set_where_fn_belongs_to {
            FnSetObj::FnSetWithoutParams(set_where_fn_belongs_to_as_short_form) => {
                if set_where_fn_belongs_to_as_short_form.param_sets.len()
                    != def_algo_stmt.params.len()
                {
                    return Err(ExecStmtError::new(
                        Stmt::DefAlgoStmt(def_algo_stmt.clone()),
                        None,
                        vec![],
                    ));
                }

                let mut param_satisfy_fn_param_set_facts = vec![];
                let mut algo_param_defs_with_type_local = vec![];

                for (param_name, param_set) in def_algo_stmt
                    .params
                    .iter()
                    .zip(set_where_fn_belongs_to_as_short_form.param_sets.iter())
                {
                    let in_fact = Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                        crate::obj::Obj::Identifier(Identifier::new(param_name.clone())),
                        param_set.as_ref().clone(),
                        def_algo_stmt.line_file,
                    )));
                    param_satisfy_fn_param_set_facts.push(in_fact);
                    algo_param_defs_with_type_local.push(ParamDefWithParamType(
                        vec![param_name.clone()],
                        ParamType::Obj(param_set.as_ref().clone()),
                    ));
                }

                (
                    param_satisfy_fn_param_set_facts,
                    algo_param_defs_with_type_local,
                )
            }
            FnSetObj::FnSetWithDom(set_where_fn_belongs_to_as_short_form) => {
                let args_for_algo_params: Vec<Obj> = {
                    let mut args: Vec<Obj> = Vec::with_capacity(def_algo_stmt.params.len());
                    for param_name in def_algo_stmt.params.iter() {
                        args.push(Obj::Identifier(Identifier::new(param_name.clone())));
                    }
                    args
                };

                let param_satisfy_fn_param_set_facts_atomic =
                    ParamDefWithParamSet::facts_for_args_satisfy_param_def_with_set_vec(
                        &set_where_fn_belongs_to_as_short_form.params_def_with_set,
                        &args_for_algo_params,
                    )
                    .map_err(|runtime_error| {
                        ExecStmtError::with_message_and_cause(
                            Stmt::DefAlgoStmt(def_algo_stmt.clone()),
                            "algo verify: failed to build param in-set facts".to_string(),
                            Some(runtime_error),
                            vec![],
                        )
                    })?;

                let mut param_to_arg_map: HashMap<String, Obj> = HashMap::new();
                let fn_set_param_names = set_where_fn_belongs_to_as_short_form.params();
                if fn_set_param_names.len() != def_algo_stmt.params.len() {
                    return Err(ExecStmtError::with_message_and_cause(
                        Stmt::DefAlgoStmt(def_algo_stmt.clone()),
                        format!(
                            "algo verify: number of params mismatch (algo params: {}, fn set params: {})",
                            def_algo_stmt.params.len(),
                            fn_set_param_names.len()
                        ),
                        None,
                        vec![],
                    ));
                }
                for (fn_set_param_name, algo_param_name) in
                    fn_set_param_names.iter().zip(def_algo_stmt.params.iter())
                {
                    param_to_arg_map.insert(
                        fn_set_param_name.clone(),
                        Obj::Identifier(Identifier::new(algo_param_name.clone())),
                    );
                }

                let mut requirement_facts: Vec<Fact> = Vec::new();
                let mut algo_param_defs_with_type_local: Vec<ParamDefWithParamType> =
                    Vec::with_capacity(
                        set_where_fn_belongs_to_as_short_form
                            .params_def_with_set
                            .len(),
                    );

                for param_def_with_set in set_where_fn_belongs_to_as_short_form
                    .params_def_with_set
                    .iter()
                {
                    let mut mapped_param_names: Vec<String> =
                        Vec::with_capacity(param_def_with_set.0.len());
                    for fn_set_param_name in param_def_with_set.0.iter() {
                        match param_to_arg_map.get(fn_set_param_name) {
                            Some(Obj::Identifier(identifier)) => {
                                mapped_param_names.push(identifier.name.clone());
                            }
                            _ => {
                                return Err(ExecStmtError::with_message_and_cause(
                                    Stmt::DefAlgoStmt(def_algo_stmt.clone()),
                                    "algo verify: param map internal error".to_string(),
                                    None,
                                    vec![],
                                ));
                            }
                        }
                    }
                    let instantiated_param_set =
                        param_def_with_set.1.instantiate(&param_to_arg_map);
                    algo_param_defs_with_type_local.push(ParamDefWithParamType(
                        mapped_param_names,
                        ParamType::Obj(instantiated_param_set),
                    ));
                }

                for in_fact_atomic in param_satisfy_fn_param_set_facts_atomic.iter() {
                    requirement_facts.push(Fact::AtomicFact(in_fact_atomic.clone()));
                }
                for dom_fact in set_where_fn_belongs_to_as_short_form.dom_facts.iter() {
                    let instantiated_dom_fact = dom_fact.instantiate(&param_to_arg_map);
                    requirement_facts.push(instantiated_dom_fact.to_fact());
                }
                (requirement_facts, algo_param_defs_with_type_local)
            }
        };

        let mut fn_call_args: Vec<Box<Obj>> = Vec::with_capacity(def_algo_stmt.params.len());
        for algo_param_name in def_algo_stmt.params.iter() {
            fn_call_args.push(Box::new(Obj::Identifier(Identifier::new(
                algo_param_name.clone(),
            ))));
        }
        let fn_call_obj = Obj::FnObj(FnObj::new(
            Atom::Identifier(Identifier::new(def_algo_stmt.name.clone())),
            vec![fn_call_args],
        ));

        let mut requirement_dom_facts: Vec<ExistOrAndChainAtomicFact> =
            Vec::with_capacity(requirement_facts_for_parma.len());
        for requirement_fact in requirement_facts_for_parma.iter() {
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
                    return Err(ExecStmtError::with_message_and_cause(
                        Stmt::DefAlgoStmt(def_algo_stmt.clone()),
                        "algo verify: requirement fact cannot be forall".to_string(),
                        None,
                        vec![],
                    ));
                }
            };
            requirement_dom_facts.push(requirement_dom_fact);
        }

        for algo_case in def_algo_stmt.cases.iter() {
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
                    algo_case.line_file,
                )),
            )];
            let case_forall_fact = Fact::ForallFact(ForallFact::new(
                algo_param_defs_with_type.clone(),
                case_dom_facts,
                case_then_facts,
                algo_case.line_file,
            ));

            self.verify_fact_return_err_if_not_true(&case_forall_fact, &VerifyState::new(0, false))
                .map_err(|runtime_error| {
                    ExecStmtError::with_message_and_cause(
                        Stmt::DefAlgoStmt(def_algo_stmt.clone()),
                        format!(
                            "algo verify: case `{}` does not imply expected return",
                            algo_case
                        ),
                        Some(runtime_error.into()),
                        vec![],
                    )
                })?;
        }

        if def_algo_stmt.default_return.is_none() {
            if def_algo_stmt.cases.is_empty() {
                return Err(ExecStmtError::with_message_and_cause(
                    Stmt::DefAlgoStmt(def_algo_stmt.clone()),
                    "algo verify: no case and no default return".to_string(),
                    None,
                    vec![],
                ));
            }

            let mut case_conditions: Vec<crate::fact::AndChainAtomicFact> =
                Vec::with_capacity(def_algo_stmt.cases.len());
            for algo_case in def_algo_stmt.cases.iter() {
                case_conditions.push(AndChainAtomicFact::AtomicFact(algo_case.condition.clone()));
            }
            let coverage_or_fact = OrFact::new(case_conditions, def_algo_stmt.line_file);
            let coverage_forall_fact = Fact::ForallFact(ForallFact::new(
                algo_param_defs_with_type.clone(),
                requirement_dom_facts.clone(),
                vec![ExistOrAndChainAtomicFact::OrFact(coverage_or_fact)],
                def_algo_stmt.line_file,
            ));
            self.verify_fact_return_err_if_not_true(
                &coverage_forall_fact,
                &VerifyState::new(0, false),
            )
            .map_err(|runtime_error| {
                ExecStmtError::with_message_and_cause(
                    Stmt::DefAlgoStmt(def_algo_stmt.clone()),
                    "algo verify: cases do not cover all situations".to_string(),
                    Some(runtime_error.into()),
                    vec![],
                )
            })?;
        }

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::DefAlgoStmt(def_algo_stmt.clone()),
                InferResult::new(),
                vec![],
            ),
        ))
    }
}
