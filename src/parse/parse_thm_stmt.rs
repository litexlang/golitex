use crate::prelude::*;

impl Runtime {
    pub fn parse_def_thm_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        self.parse_def_thm_or_lemma_stmt(tb, DefThmKind::Thm)
    }

    pub fn parse_def_lemma_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        self.parse_def_thm_or_lemma_stmt(tb, DefThmKind::Lemma)
    }

    fn parse_def_thm_or_lemma_stmt(
        &mut self,
        tb: &mut TokenBlock,
        kind: DefThmKind,
    ) -> Result<Stmt, RuntimeError> {
        let keyword = match kind {
            DefThmKind::Thm => THM,
            DefThmKind::Lemma => LEMMA,
        };
        tb.skip_token(keyword)?;
        let mut thm_names = Vec::new();
        loop {
            let name = tb.advance()?;
            is_valid_litex_name(&name).map_err(|msg| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone()),
                ))
            })?;
            thm_names.push(name);
            if tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
            } else {
                break;
            }
        }
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
                        "{}: expects a `prove:` block and optional proof body",
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
                        format!("{}: expected `prove:` or `?` goal block", keyword),
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

        let stmt = match kind {
            DefThmKind::Thm => {
                DefThmStmt::new_thm(thm_names, forall_fact, prove_process, tb.line_file.clone())
            }
            DefThmKind::Lemma => {
                DefThmStmt::new_lemma(thm_names, forall_fact, prove_process, tb.line_file.clone())
            }
        };
        Ok(stmt.into())
    }
}
