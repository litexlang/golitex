impl Runtime {
    pub fn execute_stmt2(&mut self, stmt: &Stmt) -> Result<ExecStmtResult2, RuntimeError> {
        match Stmt {
            FactStmt(stmt) => execute_fact_statement2(stmt),
        }
    }
}
