use crate::prelude::*;

impl Runtime {
    pub fn exec_stmt(&mut self, stmt: &Stmt) -> Result<StmtResult, RuntimeError> {
        match stmt {
            Stmt::DefLetStmt(d) => self.exec_let_stmt(d),
            Stmt::DefPropStmt(d) => self.exec_def_prop_stmt(d),
            Stmt::DefAbstractPropStmt(d) => self.exec_def_abstract_prop_stmt(d),
            Stmt::HaveObjInNonemptySetStmt(d) => {
                self.exec_have_obj_in_nonempty_set_or_param_type_stmt(d)
            }
            Stmt::HaveObjEqualStmt(d) => self.exec_have_obj_equal_stmt(d),
            Stmt::HaveByExistStmt(d) => self.exec_have_exist_obj_stmt(d),
            Stmt::HaveFnEqualStmt(d) => self.exec_have_fn_equal_stmt(d),
            Stmt::HaveFnEqualCaseByCaseStmt(d) => self.exec_have_fn_equal_case_by_case_stmt(d),
            Stmt::HaveFnByInducStmt(d) => self.exec_have_fn_by_induc_stmt(d),
            Stmt::HaveFnByForallExistUniqueStmt(d) => {
                self.exec_have_fn_by_forall_exist_unique_stmt(d)
            }
            Stmt::DefFamilyStmt(d) => self.exec_def_family_stmt(d),
            Stmt::DefAlgoStmt(d) => self.exec_def_algo_stmt(d),
            Stmt::KnowStmt(know_stmt) => self.exec_know_stmt(know_stmt),
            Stmt::Fact(fact) => self.exec_fact(fact),
            Stmt::ClaimStmt(s) => self.exec_claim_stmt(s),
            Stmt::ProveStmt(s) => self.exec_prove_stmt(s),
            Stmt::ImportStmt(s) => self.exec_import_stmt(s),
            Stmt::DoNothingStmt(s) => self.exec_do_nothing_stmt(s),
            Stmt::ClearStmt(s) => self.exec_clear_stmt(s),
            Stmt::RunFileStmt(s) => self.exec_run_file_stmt(s),
            Stmt::EvalStmt(s) => self.exec_eval_stmt(s),
            Stmt::WitnessExistFact(s) => self.exec_witness_exist_fact(s),
            Stmt::WitnessNonemptySet(s) => self.exec_witness_nonempty_set(s),
            Stmt::ByCasesStmt(s) => self.exec_by_cases_stmt(s),
            Stmt::ByContraStmt(s) => self.exec_by_contra_stmt(s),
            Stmt::ByEnumerateFiniteSetStmt(s) => self.exec_by_enumerate_finite_set_stmt(s),
            Stmt::ByInducStmt(s) => self.exec_by_induc_stmt(s),
            Stmt::ByForStmt(s) => self.exec_by_for_stmt(s),
            Stmt::ByExtensionStmt(s) => self.exec_by_extension_stmt(s),
            Stmt::ByFnAsSetStmt(s) => self.exec_by_fn_stmt(s),
            Stmt::ByFamilyAsSetStmt(s) => self.exec_by_family_stmt(s),
            Stmt::ByTupleAsSetStmt(s) => self.exec_by_tuple_stmt(s),
            Stmt::ByFnSetAsSetStmt(s) => self.exec_by_fn_set_stmt(s),
            Stmt::ByClosedRangeAsCasesStmt(s) => self.exec_by_closed_range_as_cases_stmt(s),
            Stmt::ByTransitivePropStmt(s) => self.exec_by_transitive_prop_stmt(s),
            Stmt::ByCommutativePropStmt(s) => self.exec_by_commutative_prop_stmt(s),
            Stmt::DefStructStmt(s) => self.exec_def_struct_stmt(s),
        }
    }

    pub fn stmt_unsupported(stmt: Stmt) -> Result<StmtResult, RuntimeError> {
        Err(short_exec_error(
            stmt,
            "unimplemented".to_string(),
            None,
            vec![],
        ))
    }
}
