use crate::prelude::*;

impl Runtime {
    pub fn parse_eval_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(EVAL)?;
        let obj_to_eval = self.parse_obj(tb)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "eval: expected one expression".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(EvalStmt::new(obj_to_eval, tb.line_file.clone()).into())
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/parsing/statements/evaluation.rs"]
mod parse_eval_stmt_tests;
