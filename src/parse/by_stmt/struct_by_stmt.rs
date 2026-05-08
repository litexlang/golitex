use crate::prelude::*;

impl Runtime {
    pub fn parse_by_struct_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(STRUCT)?;
        let mut struct_bindings = Vec::new();
        let mut value_bindings = Vec::new();

        while tb.current()? != COLON {
            let name = tb.advance()?;
            if tb.current_token_is_equal_to(FROM) {
                tb.skip_token(FROM)?;
                let tuple = self.parse_obj(tb)?;
                tb.skip_token(AS)?;
                let struct_ty = self.parse_struct_type_after_as(tb)?;
                struct_bindings.push(ByStructBinding::new(name, tuple, struct_ty));
            } else if tb.current_token_is_equal_to(EQUAL) {
                tb.skip_token(EQUAL)?;
                let value = self.parse_obj(tb)?;
                value_bindings.push(ByStructValueBinding::new(name, value));
            } else {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by struct: expected `from` or `=` after parameter name".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }

            if tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
            } else if tb.current()? != COLON {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by struct: expected `,` or `:` after binding".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
        }
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by struct: unexpected tokens after `:`".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        if struct_bindings.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by struct: expected at least one struct binding".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        if tb.body.len() != 1 {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by struct: expects exactly one forall fact in the body".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        let fact = self.parse_fact(&mut tb.body[0])?;
        let forall_fact = match fact {
            Fact::ForallFact(f) => f,
            Fact::ForallFactWithIff(_) => {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by struct: forall with `<=>` is not allowed here".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            _ => {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by struct: body must be a single forall fact".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
        };

        Ok(ByStructStmt::new(
            struct_bindings,
            value_bindings,
            forall_fact,
            tb.line_file.clone(),
        )
        .into())
    }

    fn parse_struct_type_after_as(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<StructAsParamType, RuntimeError> {
        let name = if tb.token_at_add_index(1) == MOD_SIGN {
            let mod_name = tb.advance()?;
            tb.skip_token(MOD_SIGN)?;
            let name = tb.advance()?;
            NameOrNameWithMod::new_name_with_mod(mod_name, name)
        } else {
            NameOrNameWithMod::new_name(tb.advance()?)
        };
        let args = if !tb.exceed_end_of_head() && tb.current_token_is_equal_to(LEFT_BRACE) {
            self.parse_braced_objs(tb)?
        } else {
            vec![]
        };
        Ok(StructAsParamType::new(name, args))
    }
}
