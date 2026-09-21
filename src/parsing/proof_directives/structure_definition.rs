use crate::prelude::*;

impl Runtime {
    pub fn parse_release_struct_def_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(RELEASE)?;
        tb.skip_token(STRUCT)?;
        tb.skip_token(DEF)?;
        if tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "release struct def expects exactly one object".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        if !tb.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "release struct def does not accept an indented body".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        let obj = self.parse_obj(tb)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "release struct def expects exactly one object and has no `as &Struct` form"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(ReleaseStructDefStmt::new(obj, tb.line_file.clone()).into())
    }
}
