use crate::prelude::*;

impl Runtime {
    pub fn parse_alias_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(ALIAS)?;
        let alias_kind = tb.advance()?;
        let new_name = tb.advance()?;
        is_valid_litex_name(&new_name).map_err(|msg| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone()),
            ))
        })?;
        tb.skip_token(EQUIVALENT_SIGN)?;
        let target_name = self.parse_atomic_name(tb)?;
        if !tb.exceed_end_of_head() {
            return Err(alias_parse_error(
                "alias: unexpected token after target name".to_string(),
                tb.line_file.clone(),
            ));
        }
        if !tb.body.is_empty() {
            return Err(alias_parse_error(
                "alias: body is not allowed".to_string(),
                tb.line_file.clone(),
            ));
        }

        match alias_kind.as_str() {
            PROP => {
                self.insert_parsed_name_into_top_parsing_time_name_scope(
                    &new_name,
                    tb.line_file.clone(),
                )?;
                Ok(AliasPropStmt::new(new_name, target_name, tb.line_file.clone()).into())
            }
            THM => Ok(AliasThmStmt::new(new_name, target_name, tb.line_file.clone()).into()),
            _ => Err(alias_parse_error(
                format!("alias: expected `prop` or `thm`, got `{}`", alias_kind),
                tb.line_file.clone(),
            )),
        }
    }
}

fn alias_parse_error(message: String, line_file: LineFile) -> RuntimeError {
    RuntimeError::from(ParseRuntimeError(
        RuntimeErrorStruct::new_with_msg_and_line_file(message, line_file),
    ))
}
