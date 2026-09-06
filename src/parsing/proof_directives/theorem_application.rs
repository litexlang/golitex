use crate::prelude::*;

impl Runtime {
    pub fn parse_release_thm_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(RELEASE)?;
        tb.skip_token(THM)?;
        let call = self.parse_theorem_call(tb)?;
        if !tb.exceed_end_of_head() || !tb.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "release thm accepts only a bare theorem call; use `by thm name(args) => fact` to select one consequence"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(ReleaseThmStmt::new_with_call(call, tb.line_file.clone()).into())
    }

    pub fn parse_by_thm_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(THM)?;
        let call = self.parse_theorem_call(tb)?;
        if !tb.current_token_is_equal_to(RIGHT_ARROW) {
            if tb.exceed_end_of_head() && tb.body.is_empty() {
                // Keep the pre-`release thm` spelling source-compatible while
                // routing it through the canonical theorem-release statement.
                return Ok(ReleaseThmStmt::new_with_call(call, tb.line_file.clone()).into());
            }
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by thm accepts either a bare legacy theorem call or `=>` followed by one selected atomic fact; use `release thm name(args)` for the canonical bare spelling"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
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
        let selected_fact = self.parse_atomic_fact(tb, true)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by thm: `=>` expects exactly one atomic fact".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(ByThmStmt::new_with_call(call, selected_fact, tb.line_file.clone()).into())
    }

    /// Parse the shared `name` or `name(args)` portion of an explicit theorem call.
    pub fn parse_theorem_call(&mut self, tb: &mut TokenBlock) -> Result<TheoremCall, RuntimeError> {
        let name = if is_builtin_theorem_name(tb.current()?) && tb.token_at_add_index(1) != MOD_SIGN
        {
            AtomicName::WithoutMod(tb.advance()?)
        } else {
            self.parse_module_qualified_reference_name(tb)?
        };
        let arguments = if !tb.exceed_end_of_head() && tb.current_token_is_equal_to(LEFT_BRACE) {
            TheoremCallArguments::Parenthesized(self.parse_braced_objs(tb)?)
        } else {
            TheoremCallArguments::Bare
        };
        Ok(TheoremCall::new(name, arguments))
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/parsing/proof_directives/theorem_application/tests.rs"]
mod tests;
