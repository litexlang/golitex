use crate::prelude::*;

impl Runtime {
    pub fn exec_example_stmt(&mut self, stmt: &ExampleStmt) -> Result<StmtResult, RuntimeError> {
        self.exec_checked_goal_block(stmt.clone().into(), &stmt.fact, &stmt.proof, EXAMPLE)
    }
}
