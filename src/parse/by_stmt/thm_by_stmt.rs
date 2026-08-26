use crate::prelude::*;

impl Runtime {
    pub fn parse_release_thm_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(RELEASE)?;
        tb.skip_token(THM)?;
        let (name, args) = self.parse_theorem_call(tb)?;
        if !tb.exceed_end_of_head() || !tb.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "release thm accepts only a bare theorem call; use `by thm name(args) => fact` to select one consequence"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(ByThmStmt::new(name, args, None, tb.line_file.clone()).into())
    }

    pub fn parse_by_thm_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(THM)?;
        let (name, args) = self.parse_theorem_call(tb)?;
        let selected_facts = if tb.current_token_is_equal_to(RIGHT_ARROW) {
            if !tb.body.is_empty() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by thm: `=>` does not accept an indented body".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            tb.skip_token(RIGHT_ARROW)?;
            if tb.exceed_end_of_head() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by thm: `=>` expects one atomic fact".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let fact = self.parse_atomic_fact(tb, true)?;
            if !tb.exceed_end_of_head() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by thm: `=>` expects exactly one atomic fact".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            Some(vec![fact.into()])
        } else if tb.current_token_is_equal_to(COLON) {
            tb.skip_token(COLON)?;
            if !tb.exceed_end_of_head() || tb.body.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by thm: expects exactly one `? <atomic fact>` goal block and no proof body"
                            .to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            Some(vec![self
                .parse_goal_atomic_fact_block(&mut tb.body[0], "by thm")?
                .into()])
        } else {
            if !tb.body.is_empty() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by thm does not accept an indented body".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            None
        };
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by thm: unexpected token after theorem call".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(ByThmStmt::new(name, args, selected_facts, tb.line_file.clone()).into())
    }

    /// Parse the shared `name(args)` portion of an explicit theorem call.
    pub fn parse_theorem_call(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<(AtomicName, Vec<Obj>), RuntimeError> {
        let name = if is_builtin_theorem_name(tb.current()?) && tb.token_at_add_index(1) != MOD_SIGN
        {
            AtomicName::WithoutMod(tb.advance()?)
        } else {
            self.parse_module_qualified_reference_name(tb)?
        };
        let args = self.parse_braced_objs(tb)?;
        Ok((name, args))
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/parse/by_stmt/thm_by_stmt/tests.rs"]
mod tests;
