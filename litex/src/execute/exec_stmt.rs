use super::Runtime;
use crate::error::{ExecStmtError, RuntimeError};
use crate::result::NonErrStmtExecResult;
use crate::stmt::Stmt;

impl<'a> Runtime<'a> {
    pub fn exec_stmt(&mut self, stmt: &Stmt) -> Result<NonErrStmtExecResult, RuntimeError> {
        match stmt {
            Stmt::DefLetStmt(d) => self.def_let_stmt(d).map_err(RuntimeError::from),
            Stmt::DefPropWithMeaningStmt(d) => self
                .def_prop_with_meaning_stmt(d)
                .map_err(RuntimeError::from),
            Stmt::DefPropWithoutMeaningStmt(d) => self
                .def_prop_without_meaning_stmt(d)
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
            Stmt::DefStructWithFieldsStmt(d) => self
                .def_struct_with_fields_stmt(d)
                .map_err(RuntimeError::from),
            Stmt::DefStructWithNoFieldStmt(d) => self
                .def_struct_with_no_field_stmt(d)
                .map_err(RuntimeError::from),
            Stmt::DefAlgoStmt(d) => self.def_algo_stmt(d).map_err(RuntimeError::from),
            Stmt::KnowStmt(know_stmt) => self.exec_know_stmt(know_stmt).map_err(RuntimeError::from),
            Stmt::Fact(fact) => self.exec_fact(fact).map_err(RuntimeError::from),
            Stmt::ClaimStmt(s) => self.exec_claim_stmt(s),
            Stmt::ProveStmt(s) => self.exec_prove_stmt(s),
            Stmt::ImportStmt(s) => self.exec_import_stmt(s),
            Stmt::ClearStmt(s) => self.exec_clear_stmt(s),
            Stmt::DoNothingStmt(s) => self.exec_do_nothing_stmt(s),
            Stmt::RunFileStmt(s) => self.exec_run_file_stmt(s),
            Stmt::EvalStmt(s) => self.exec_eval_stmt(s),
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

    pub fn stmt_unsupported(
        stmt_type_name: String,
        line_file: (usize, usize),
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        Err(RuntimeError::ExecError(ExecStmtError::new(
            stmt_type_name,
            "unimplemented".to_string(),
            None,
            vec![],
            line_file,
        )))
    }
}
