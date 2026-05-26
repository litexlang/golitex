use crate::prelude::*;

impl Runtime {
    pub fn parse_by_thm_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(THM)?;
        let name = tb.advance()?;
        is_valid_litex_name(&name).map_err(|msg| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone()),
            ))
        })?;
        let args = self.parse_braced_objs(tb)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by thm: unexpected token after theorem call".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(ByThmStmt::new(name, args, tb.line_file.clone()).into())
    }
}
