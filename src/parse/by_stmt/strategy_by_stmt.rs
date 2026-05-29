use crate::prelude::*;

impl Runtime {
    pub fn parse_by_strategy_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(STRATEGY)?;
        let name = self.parse_module_qualified_reference_name(tb)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by strategy: unexpected token after strategy name".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(ByStrategyStmt::new(name, tb.line_file.clone()).into())
    }
}
