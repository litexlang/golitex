use crate::prelude::*;

impl Runtime {
    pub fn exec_stmt(&mut self, stmt: &Stmt) -> Result<NonErrStmtExecResult, RuntimeError> {
        match stmt {
            Stmt::DefLetStmt(d) => self.def_let_stmt(d).map_err(RuntimeError::from),
            Stmt::DefPropStmt(d) => self.def_prop_stmt(d).map_err(RuntimeError::from),
            Stmt::DefAbstractPropStmt(d) => {
                self.def_abstract_prop_stmt(d).map_err(RuntimeError::from)
            }
            Stmt::HaveObjInNonemptySetStmt(d) => self
                .have_obj_in_nonempty_set_or_param_type_stmt(d)
                .map_err(RuntimeError::from),
            Stmt::HaveObjEqualStmt(d) => self.have_obj_equal_stmt(d).map_err(RuntimeError::from),
            Stmt::HaveExistObjStmt(d) => self.have_exist_obj_stmt(d).map_err(RuntimeError::from),
            Stmt::HaveFnEqualStmt(d) => self.have_fn_equal_stmt(d).map_err(RuntimeError::from),
            Stmt::HaveFnEqualCaseByCaseStmt(d) => self
                .have_fn_equal_case_by_case_stmt(d)
                .map_err(RuntimeError::from),
            Stmt::HaveFnByInducStmt(d) => self
                .have_fn_by_induc_stmt(d)
                .map_err(RuntimeError::from),
            Stmt::DefParamTypeStructStmt(d) => self
                .def_param_type_struct_stmt(d)
                .map_err(RuntimeError::from),
            Stmt::DefFamilyStmt(d) => self.def_family_stmt(d).map_err(RuntimeError::from),
            Stmt::DefAlgoStmt(d) => self.exec_def_algo_stmt(d).map_err(RuntimeError::from),
            Stmt::KnowStmt(know_stmt) => self.exec_know_stmt(know_stmt).map_err(RuntimeError::from),
            Stmt::Fact(fact) => self.exec_fact(fact).map_err(RuntimeError::from),
            Stmt::ClaimStmt(s) => self.exec_claim_stmt(s),
            Stmt::ProveStmt(s) => self.exec_prove_stmt(s),
            Stmt::ImportStmt(s) => self.exec_import_stmt(s),
            Stmt::DoNothingStmt(s) => self.exec_do_nothing_stmt(s),
            Stmt::RunFileStmt(s) => self.exec_run_file_stmt(s),
            Stmt::EvalStmt(s) => {
                self._exec_eval_stmt(s)?;
                return Err(RuntimeError::ExecStmtError(
                    RuntimeErrorStruct::exec_stmt_new_with_stmt(
                        Stmt::EvalStmt(s.clone()),
                        "eval: obj_to_eval must be a fnObj".to_string(),
                        None,
                        vec![],
                    ),
                ));
            }
            Stmt::WitnessExistFact(s) => self.exec_witness_exist_fact(s),
            Stmt::WitnessNonemptySet(s) => self.exec_witness_nonempty_set(s),
            Stmt::ByCasesStmt(s) => self.exec_by_cases_stmt(s),
            Stmt::ByContraStmt(s) => self.exec_by_contra_stmt(s),
            Stmt::ByEnumerateStmt(s) => self.exec_by_enumerate_stmt(s),
            Stmt::ByInducStmt(s) => self.exec_by_induc_stmt(s),
            Stmt::ByForStmt(s) => self.exec_by_for_stmt(s),
            Stmt::ByExtensionStmt(s) => self.exec_by_extension_stmt(s),
            Stmt::ByFnStmt(s) => self.exec_by_fn_stmt(s),
            Stmt::ByTuple(s) => self.exec_by_tuple_stmt(s),
        }
    }

    pub fn stmt_unsupported(stmt: Stmt) -> Result<NonErrStmtExecResult, RuntimeError> {
        Err(RuntimeError::from(
            RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                stmt,
                "unimplemented".to_string(),
                None,
                vec![],
            ),
        ))
    }
}
