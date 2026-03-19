use crate::error::{ExecError, StmtError};
use crate::stmt::Stmt;
use crate::result::NonErrStmtExecResult;
use super::Executor;

impl<'a> Executor<'a> {
    pub fn exec_stmt(&mut self, stmt: &Stmt) -> Result<NonErrStmtExecResult, StmtError> {
        match stmt {
            Stmt::DefLetStmt(d) => self.def_let_stmt(d).map_err(StmtError::from),
            Stmt::DefPropWithMeaningStmt(d) => self.def_prop_with_meaning_stmt(d).map_err(StmtError::from),
            Stmt::DefPropWithoutMeaningStmt(d) => self.def_prop_without_meaning_stmt(d).map_err(StmtError::from),
            Stmt::HaveObjInNonemptySetStmt(d) => self.have_obj_in_nonempty_set_or_param_type_stmt(d).map_err(StmtError::from),
            Stmt::HaveObjEqualStmt(d) => self.have_obj_equal_stmt(d).map_err(StmtError::from),
            Stmt::HaveExistObjStmt(d) => self.have_exist_obj_stmt(d).map_err(StmtError::from),
            Stmt::HaveFnEqualStmt(d) => self.have_fn_equal_stmt(d).map_err(StmtError::from),
            Stmt::HaveFnEqualCaseByCaseStmt(d) => self.have_fn_equal_case_by_case_stmt(d).map_err(StmtError::from),
            Stmt::DefStructWithFieldsStmt(d) => self.def_struct_with_fields_stmt(d).map_err(StmtError::from),
            Stmt::DefStructWithNoFieldStmt(d) => self.def_struct_with_no_field_stmt(d).map_err(StmtError::from),
            Stmt::DefAlgoStmt(d) => self.def_algo_stmt(d).map_err(StmtError::from),
            Stmt::KnowStmt(know_stmt) => self.exec_know_stmt(know_stmt).map_err(StmtError::from),
            Stmt::Fact(fact) => self.exec_fact(fact).map_err(StmtError::from),
            Stmt::ClaimStmt(s) => self.exec_claim_stmt(s),
            Stmt::ProveStmt(s) => self.exec_prove_stmt(s),
            Stmt::ImportStmt(s) => self.exec_import_stmt(s),
            Stmt::ClearStmt(s) => self.exec_clear_stmt(s),
            Stmt::DoNothingStmt(s) => self.exec_do_nothing_stmt(s),
            Stmt::RunFileStmt(s) => self.exec_run_file_stmt(s),
            Stmt::EvalStmt(s) => self.exec_eval_stmt(s),
            Stmt::WitnessExistFact(s) => self.exec_witness_exist_fact(s),
            Stmt::WitnessNonemptySet(s) => self.exec_witness_nonempty_set(s),
            Stmt::ProveCaseByCaseStmt(s) => self.exec_prove_case_by_case_stmt(s),
            Stmt::ProveByContradictionStmt(s) => self.exec_prove_by_contradiction_stmt(s),
            Stmt::ProveByEnumerationStmt(s) => self.exec_prove_by_enumeration_stmt(s),
            Stmt::ProveByInductionStmt(s) => self.exec_prove_by_induction_stmt(s),
            Stmt::ProveForStmt(s) => self.exec_prove_for_stmt(s),
            Stmt::ProveByEqualSetStmt(s) => self.exec_prove_by_equal_set_stmt(s),
            Stmt::ViewFnAsSetStmt(s) => self.exec_view_fn_as_set_stmt(s),
        }
    }

    pub fn stmt_unsupported(stmt_type_name: String, line_file: (usize, usize)) -> Result<NonErrStmtExecResult, StmtError> {
        Err(StmtError::ExecError(ExecError::new(stmt_type_name, "unimplemented".to_string(), None, line_file)))
    }
}
