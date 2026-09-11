use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};
use crate::prelude::*;

impl Runtime {
    pub fn exec_stmt(&mut self, stmt: &Stmt) -> RuntimeResult<()> {
        match stmt {
            Stmt::Fact(fact) => {
                self.execute_fact_statement2(fact)?;
                Ok(())
            }
            _ => Err(RuntimeError::Unsupported(
                "new_pipeline exec_stmt: only Fact is wired for the tracer".to_string(),
            )),
        }
    }
}
