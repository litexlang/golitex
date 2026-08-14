use crate::prelude::*;

impl Runtime {
    pub fn parse_by_for_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(FOR)?;
        if !tb.current_token_is_equal_to(COLON) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by for requires `by for:` followed by an indented `? forall ...` goal"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by for: expected `:` immediately after `for`".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        if tb.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by for: expects a body".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        let goal_block = tb.body.get_mut(0).ok_or_else(|| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by for: expected a `? forall ...` goal block".to_string(),
                    tb.line_file.clone(),
                ),
            ))
        })?;
        let forall_fact = self.parse_goal_forall_fact_block(goal_block, "by for")?;

        ByForStmt::new(forall_fact.clone(), vec![], forall_fact.line_file.clone())
            .expansion()
            .map_err(|msg| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        msg,
                        forall_fact.line_file.clone(),
                    ),
                ))
            })?;

        let bindings = forall_fact.params_def_with_type.collect_param_bindings();
        let lf = tb.line_file.clone();
        let proof: Vec<Stmt> = self.parse_stmts_with_existing_free_param_bindings(
            ParamObjType::Forall,
            &bindings,
            lf,
            |this| {
                tb.body
                    .iter_mut()
                    .skip(1)
                    .map(|b| this.parse_stmt(b))
                    .collect::<Result<_, _>>()
            },
        )?;

        Ok(ByForStmt::new(forall_fact, proof, tb.line_file.clone()).into())
    }
}
