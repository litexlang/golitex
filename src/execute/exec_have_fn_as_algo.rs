use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub(crate) fn exec_have_fn_equal_stmt_as_algo(
        &mut self,
        stmt: &HaveFnEqualStmt,
    ) -> Result<(), RuntimeError> {
        let params = ParamGroupWithSet::collect_param_names(
            &stmt.equal_to_anonymous_fn.body.params_def_with_set,
        );
        let param_to_def_algo_obj = Self::def_algo_param_obj_map(&params);
        let default_return_value = self
            .inst_obj(
                stmt.equal_to_anonymous_fn.equal_to.as_ref(),
                &param_to_def_algo_obj,
                ParamObjType::FnSet,
            )
            .map_err(|e| {
                short_exec_error(
                    stmt.clone().into(),
                    "have fn as algo: failed to rewrite generated algo return parameters"
                        .to_string(),
                    Some(e),
                    vec![],
                )
            })?;
        let default_return = AlgoReturn::new(default_return_value, stmt.line_file.clone());
        let def_algo_stmt = DefAlgoStmt::new(
            stmt.name.clone(),
            params,
            vec![],
            Some(default_return),
            stmt.line_file.clone(),
        );
        self.exec_generated_algo_from_have_fn(stmt.clone().into(), &def_algo_stmt)
    }

    pub(crate) fn exec_have_fn_equal_case_by_case_stmt_as_algo(
        &mut self,
        stmt: &HaveFnEqualCaseByCaseStmt,
    ) -> Result<(), RuntimeError> {
        let def_algo_stmt = self.def_algo_stmt_from_have_fn_cases(
            stmt.clone().into(),
            &stmt.name,
            &stmt.fn_set_clause,
            &stmt.cases,
            &stmt.equal_tos,
            &stmt.line_file,
        )?;
        self.exec_generated_algo_from_have_fn(stmt.clone().into(), &def_algo_stmt)
    }

    pub(crate) fn exec_have_fn_by_induc_stmt_as_algo(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<(), RuntimeError> {
        let flat = stmt.to_have_fn_equal_case_by_case_stmt();
        let def_algo_stmt = self.def_algo_stmt_from_have_fn_cases(
            stmt.clone().into(),
            &flat.name,
            &flat.fn_set_clause,
            &flat.cases,
            &flat.equal_tos,
            &flat.line_file,
        )?;
        self.exec_generated_algo_from_have_fn(stmt.clone().into(), &def_algo_stmt)
    }

    fn exec_generated_algo_from_have_fn(
        &mut self,
        owner_stmt: Stmt,
        def_algo_stmt: &DefAlgoStmt,
    ) -> Result<(), RuntimeError> {
        self.exec_def_algo_stmt(def_algo_stmt)
            .map(|_| ())
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(owner_stmt, e))
    }

    fn def_algo_stmt_from_have_fn_cases(
        &self,
        owner_stmt: Stmt,
        name: &str,
        fn_set_clause: &FnSetClause,
        cases: &[AndChainAtomicFact],
        equal_tos: &[Obj],
        line_file: &LineFile,
    ) -> Result<DefAlgoStmt, RuntimeError> {
        if cases.len() != equal_tos.len() {
            return Err(short_exec_error(
                owner_stmt,
                "have fn as algo: number of cases does not match number of return expressions"
                    .to_string(),
                None,
                vec![],
            ));
        }

        let params = ParamGroupWithSet::collect_param_names(&fn_set_clause.params_def_with_set);
        let param_to_def_algo_obj = Self::def_algo_param_obj_map(&params);
        let mut algo_cases = Vec::with_capacity(cases.len());
        for (case, equal_to) in cases.iter().zip(equal_tos.iter()) {
            let case_lf = case.line_file();
            let inst_case = self
                .inst_and_chain_atomic_fact(
                    case,
                    &param_to_def_algo_obj,
                    ParamObjType::FnSet,
                    Some(&case_lf),
                )
                .map_err(|e| {
                    short_exec_error(
                        owner_stmt.clone(),
                        "have fn as algo: failed to rewrite generated algo case parameters"
                            .to_string(),
                        Some(e),
                        vec![],
                    )
                })?;
            let condition = Self::atomic_fact_for_as_algo_case(owner_stmt.clone(), &inst_case)?;
            let return_value = self
                .inst_obj(equal_to, &param_to_def_algo_obj, ParamObjType::FnSet)
                .map_err(|e| {
                    short_exec_error(
                        owner_stmt.clone(),
                        "have fn as algo: failed to rewrite generated algo return parameters"
                            .to_string(),
                        Some(e),
                        vec![],
                    )
                })?;
            let return_stmt = AlgoReturn::new(return_value, case_lf.clone());
            algo_cases.push(AlgoCase::new(condition, return_stmt, case_lf));
        }

        Ok(DefAlgoStmt::new(
            name.to_string(),
            params,
            algo_cases,
            None,
            line_file.clone(),
        ))
    }

    fn atomic_fact_for_as_algo_case(
        owner_stmt: Stmt,
        case: &AndChainAtomicFact,
    ) -> Result<AtomicFact, RuntimeError> {
        match case {
            AndChainAtomicFact::AtomicFact(a) => Ok(a.clone()),
            AndChainAtomicFact::AndFact(_) | AndChainAtomicFact::ChainFact(_) => Err(
                short_exec_error(
                    owner_stmt,
                    format!(
                        "have fn as algo: generated algo case `{}` is not atomic; generated algo cases currently require atomic case conditions",
                        case
                    ),
                    None,
                    vec![],
                ),
            ),
        }
    }

    fn def_algo_param_obj_map(params: &[String]) -> HashMap<String, Obj> {
        let mut param_to_def_algo_obj = HashMap::with_capacity(params.len());
        for param in params.iter() {
            param_to_def_algo_obj.insert(
                param.clone(),
                obj_for_bound_param_in_scope(param.clone(), ParamObjType::DefAlgo),
            );
        }
        param_to_def_algo_obj
    }
}
