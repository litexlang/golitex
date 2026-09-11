impl Runtime {
    pub fn exec_unsafe_stmt(
        &mut self,
        stmt: &UnsafeStmt,
    ) -> Result<ExecUnsafeStmtResult, RuntimeError> {
    }

    pub fn exec_trust_stmt(&mut self, stmt: &TrustStmt) -> Result<ExecTrustStmt, RuntimeError> {}
}
