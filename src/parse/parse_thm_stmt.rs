use crate::prelude::*;

impl Runtime {
    pub fn parse_def_thm_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        let keyword = THM;
        tb.skip_token(keyword)?;
        let thm_names = parse_thm_name_list(tb)?;
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!("{}: unexpected token after theorem name list", keyword),
                    tb.line_file.clone(),
                ),
            )));
        }
        if tb.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "{}: expects a `? forall ...` goal block and optional proof body",
                        keyword
                    ),
                    tb.line_file.clone(),
                ),
            )));
        }

        let (forall_fact, inline_proof_start) = {
            let goal_block = tb.body.get_mut(0).ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!("{}: expected a `? forall ...` goal block", keyword),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            self.parse_goal_forall_fact_block_with_inline_proof(goal_block, keyword)?
        };

        let names = forall_fact.params_def_with_type.collect_param_names();
        let lf = tb.line_file.clone();
        let prove_process: Vec<Stmt> = self.parse_stmts_with_optional_free_param_scope(
            ParamObjType::Forall,
            &names,
            lf,
            |this| {
                let mut proof = Vec::new();
                if inline_proof_start > 0 {
                    if let Some(goal_block) = tb.body.get_mut(0) {
                        for block in goal_block.body.iter_mut().skip(inline_proof_start) {
                            proof.push(this.parse_stmt(block)?);
                        }
                    }
                }
                for block in tb.body.iter_mut().skip(1) {
                    proof.push(this.parse_stmt(block)?);
                }
                Ok(proof)
            },
        )?;

        let stmt = DefThmStmt::new(thm_names, forall_fact, prove_process, tb.line_file.clone());
        Ok(stmt.into())
    }

    pub fn parse_def_axiom_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        let keyword = AXIOM;
        tb.skip_token(keyword)?;
        let axiom_names = parse_thm_name_list(tb)?;
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!("{}: unexpected token after axiom name list", keyword),
                    tb.line_file.clone(),
                ),
            )));
        }
        if tb.body.len() != 1 {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!("{}: expects exactly one `? forall ...` goal block", keyword),
                    tb.line_file.clone(),
                ),
            )));
        }

        let goal_block = tb.body.get_mut(0).ok_or_else(|| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!("{}: expected `?` goal block", keyword),
                    tb.line_file.clone(),
                ),
            ))
        })?;
        if !goal_block.current_token_is_equal_to(QUESTION_GOAL) {
            let message = if goal_block.current_token_is_equal_to("prove") {
                format!("{}: `prove` was removed; use `? forall ...`", keyword)
            } else {
                format!("{}: expected `? forall ...` goal block", keyword)
            };
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    message,
                    goal_block.line_file.clone(),
                ),
            )));
        }
        let forall_fact = self.parse_goal_forall_fact_block(goal_block, keyword)?;

        let stmt = DefThmStmt::new_axiom(axiom_names, forall_fact, tb.line_file.clone());
        Ok(stmt.into())
    }
}

fn parse_thm_name_list(tb: &mut TokenBlock) -> Result<Vec<String>, RuntimeError> {
    let mut names = Vec::new();
    loop {
        let name = tb.advance()?;
        is_valid_litex_name(&name).map_err(|msg| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone()),
            ))
        })?;
        names.push(name);
        if tb.current_token_is_equal_to(COMMA) {
            tb.skip_token(COMMA)?;
        } else {
            break;
        }
    }
    Ok(names)
}
