use crate::prelude::*;

impl Runtime {
    pub fn exec_stmt(&mut self, stmt: &Stmt) -> Result<NonErrStmtExecResult, RuntimeError> {
        match stmt {
            Stmt::DefLetStmt(d) => self.def_let_stmt(d).map_err(RuntimeError::from),
            Stmt::DefPropWithMeaningStmt(d) => self
                .def_prop_with_meaning_stmt(d)
                .map_err(RuntimeError::from),
            Stmt::DefAbstractPropStmt(d) => self
                .def_abstract_prop_stmt(d)
                .map_err(RuntimeError::from),
            Stmt::HaveObjInNonemptySetStmt(d) => self
                .have_obj_in_nonempty_set_or_param_type_stmt(d)
                .map_err(RuntimeError::from),
            Stmt::HaveObjEqualStmt(d) => self.have_obj_equal_stmt(d).map_err(RuntimeError::from),
            Stmt::HaveExistObjStmt(d) => self.have_exist_obj_stmt(d).map_err(RuntimeError::from),
            Stmt::HaveFnEqualStmt(d) => self.have_fn_equal_stmt(d).map_err(RuntimeError::from),
            Stmt::HaveFnEqualCaseByCaseStmt(d) => self
                .have_fn_equal_case_by_case_stmt(d)
                .map_err(RuntimeError::from),
            Stmt::DefParamTypeStructStmt(d) => self.def_param_type_struct_stmt(d)
                .map_err(RuntimeError::from),
            Stmt::DefFamilyStmt(d) => self.def_family_stmt(d)
                .map_err(RuntimeError::from),
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
                return Err(RuntimeError::ExecStmtError(RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    Stmt::EvalStmt(s.clone()),
                    "eval: obj_to_eval must be a fnObj".to_string(),
                    None,
                    vec![],
                )));
            }
            Stmt::WitnessExistFact(s) => self.exec_witness_exist_fact(s),
            Stmt::WitnessNonemptySet(s) => self.exec_witness_nonempty_set(s),
            Stmt::ByCasesAxiomStmt(s) => self.exec_by_cases_axiom_stmt(s),
            Stmt::ByContraAxiomStmt(s) => self.exec_by_contra_axiom_stmt(s),
            Stmt::EnumerateAxiomStmt(s) => self.exec_enumerate_axiom_stmt(s),
            Stmt::ByInducAxiomStmt(s) => self.exec_by_induc_axiom_stmt(s),
            Stmt::ForAxiomStmt(s) => self.exec_for_axiom_stmt(s),
            Stmt::ByExtensionAxiomStmt(s) => self.exec_by_extension_axiom_stmt(s),
            Stmt::ByFnDefAxiomStmt(s) => self.exec_by_fn_def_axiom_stmt(s),
            Stmt::ByCartDefAxiomStmt(s) => self.exec_by_cart_def_axiom_stmt(s),
        }
    }

    pub fn stmt_unsupported(stmt: Stmt) -> Result<NonErrStmtExecResult, RuntimeError> {
        Err(RuntimeError::from(
            RuntimeErrorStruct::exec_stmt_with_message_and_cause(stmt, "unimplemented".to_string(), None, vec![]),
        ))
    }
}
