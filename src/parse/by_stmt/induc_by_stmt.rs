use crate::prelude::*;

impl Runtime {
    pub fn parse_by_induc_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(INDUC)?;
        let param = tb.advance()?;
        if tb.current()? == IN {
            tb.skip_token(IN)?;
            let carrier_set = self.parse_obj(tb)?;
            return self.parse_by_finite_set_induc_stmt_after_param(tb, param, Some(carrier_set));
        }
        if tb.current()? == COLON {
            return self.parse_by_finite_set_induc_stmt_after_param(tb, param, None);
        }
        self.parse_induc_stmt_after_param(tb, param, false)
    }

    pub fn parse_strong_induc_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(STRONG_INDUC)?;
        self.parse_induc_stmt_after_keyword(tb, true)
    }

    fn parse_induc_stmt_after_keyword(
        &mut self,
        tb: &mut TokenBlock,
        strong: bool,
    ) -> Result<Stmt, RuntimeError> {
        let param = tb.advance()?;
        self.parse_induc_stmt_after_param(tb, param, strong)
    }

    fn parse_induc_stmt_after_param(
        &mut self,
        tb: &mut TokenBlock,
        param: String,
        strong: bool,
    ) -> Result<Stmt, RuntimeError> {
        tb.skip_token(FROM)?;
        let induc_from = self.parse_obj(tb)?;
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "induc: expected end of head".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        if tb.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "induc: expects one or more `? <fact>` goal blocks".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        let question_goal_count = tb
            .body
            .iter()
            .take_while(|block| {
                block.current_token_is_equal_to(QUESTION_GOAL)
                    && !Self::is_induc_structured_proof_block(block)
            })
            .count();
        if question_goal_count == 0 {
            return Err(Self::induc_parse_error(
                "induc: expects one or more `? <fact>` goal blocks before its proof".to_string(),
                tb.body[0].line_file.clone(),
            ));
        }
        let goal_body_skip = question_goal_count;
        let goal_line = tb.body[0].line_file.clone();
        let induc_param = [param.clone()];
        let mut to_prove: Vec<ExistOrAndChainAtomicFact> = Vec::new();
        self.parse_in_local_free_param_scope(
            ParamObjType::Induc,
            &induc_param,
            goal_line,
            |this| {
                for block in tb.body.iter_mut().take(question_goal_count) {
                    to_prove.push(
                        this.parse_question_goal_exist_or_and_chain_atomic_fact(block, "induc")?,
                    );
                }
                Ok(())
            },
        )?;

        let proof_line = tb.line_file.clone();
        let (proof, base_proof, step_proof) = self.with_optional_free_param_scope(
            ParamObjType::Induc,
            &induc_param,
            proof_line,
            |this| this.parse_induc_proof_blocks(tb, &param, &induc_from, strong, goal_body_skip),
        )?;

        Ok(ByInducStmt::new(
            to_prove,
            param,
            induc_from,
            proof,
            base_proof,
            step_proof,
            tb.line_file.clone(),
            strong,
        )
        .into())
    }

    fn parse_induc_proof_blocks(
        &mut self,
        tb: &mut TokenBlock,
        param: &str,
        induc_from: &Obj,
        strong: bool,
        goal_body_skip: usize,
    ) -> Result<(Vec<Stmt>, Option<Vec<Stmt>>, Option<Vec<Stmt>>), RuntimeError> {
        let mut proof: Vec<Stmt> = Vec::new();
        let mut base_proof: Option<Vec<Stmt>> = None;
        let mut step_proof: Option<Vec<Stmt>> = None;
        let mut structured_proof_seen = false;
        let step_keyword = Self::induc_step_proof_keyword(strong);

        for block in tb.body.iter_mut().skip(goal_body_skip) {
            if Self::is_induc_base_proof_block(block) {
                structured_proof_seen = true;
                if !proof.is_empty() {
                    return Err(Self::induc_parse_error(
                        format!(
                            "induc: unstructured proof statements cannot be mixed with `? from` / `? {}` blocks",
                            step_keyword
                        ),
                        block.line_file.clone(),
                    ));
                }
                if base_proof.is_some() {
                    return Err(Self::induc_parse_error(
                        "induc: duplicated `? from` block".to_string(),
                        block.line_file.clone(),
                    ));
                }
                self.verify_induc_base_proof_header(block, param, induc_from)?;
                base_proof = Some(self.parse_induc_structured_proof_body(block)?);
            } else if Self::is_induc_step_proof_block(block) {
                structured_proof_seen = true;
                Self::verify_induc_step_proof_keyword(block, step_keyword)?;
                if !proof.is_empty() {
                    return Err(Self::induc_parse_error(
                        format!(
                            "induc: unstructured proof statements cannot be mixed with `? from` / `? {}` blocks",
                            step_keyword
                        ),
                        block.line_file.clone(),
                    ));
                }
                if step_proof.is_some() {
                    return Err(Self::induc_parse_error(
                        format!("induc: duplicated `? {}` block", step_keyword),
                        block.line_file.clone(),
                    ));
                }
                block.skip_token(QUESTION_GOAL)?;
                block.skip_token(step_keyword)?;
                block.skip_token(COLON)?;
                if !block.exceed_end_of_head() {
                    return Err(Self::induc_parse_error(
                        format!("induc: expected end of `? {}` head", step_keyword),
                        block.line_file.clone(),
                    ));
                }
                step_proof = Some(self.parse_induc_structured_proof_body(block)?);
            } else {
                if structured_proof_seen {
                    return Err(Self::induc_parse_error(
                        format!(
                            "induc: unstructured proof statements cannot be mixed with `? from` / `? {}` blocks",
                            step_keyword
                        ),
                        block.line_file.clone(),
                    ));
                }
                proof.push(self.parse_stmt(block)?);
            }
        }

        if structured_proof_seen && (base_proof.is_none() || step_proof.is_none()) {
            return Err(Self::induc_parse_error(
                format!(
                    "induc: structured proof expects both `? from param = base:` and `? {}:` blocks",
                    step_keyword
                ),
                tb.line_file.clone(),
            ));
        }

        Ok((proof, base_proof, step_proof))
    }

    fn parse_induc_structured_proof_body(
        &mut self,
        block: &mut TokenBlock,
    ) -> Result<Vec<Stmt>, RuntimeError> {
        let mut proof = Vec::with_capacity(block.body.len());
        for body_block in block.body.iter_mut() {
            proof.push(self.parse_stmt(body_block)?);
        }
        Ok(proof)
    }

    fn verify_induc_base_proof_header(
        &mut self,
        block: &mut TokenBlock,
        param: &str,
        induc_from: &Obj,
    ) -> Result<(), RuntimeError> {
        block.skip_token(QUESTION_GOAL)?;
        block.skip_token(FROM)?;
        let header_fact =
            self.parse_header_fact_before_trailing_colon(block, "induc ? from", "", "")?;
        let Fact::AtomicFact(AtomicFact::EqualFact(equal_fact)) = header_fact else {
            return Err(Self::induc_parse_error(
                "induc: `? from` expects an equality fact".to_string(),
                block.line_file.clone(),
            ));
        };
        let expected_param = obj_for_bound_param_in_scope(param.to_string(), ParamObjType::Induc);
        if equal_fact.left.to_string() != expected_param.to_string()
            || equal_fact.right.to_string() != induc_from.to_string()
        {
            return Err(Self::induc_parse_error(
                format!("induc: `? from` must be `{} = {}`", param, induc_from),
                block.line_file.clone(),
            ));
        }
        Ok(())
    }

    fn is_induc_base_proof_block(block: &TokenBlock) -> bool {
        block.token_at_add_index(0) == QUESTION_GOAL && block.token_at_add_index(1) == FROM
    }

    fn is_induc_step_proof_block(block: &TokenBlock) -> bool {
        block.token_at_add_index(0) == QUESTION_GOAL
            && (block.token_at_add_index(1) == INDUC || block.token_at_add_index(1) == STRONG_INDUC)
    }

    fn is_induc_structured_proof_block(block: &TokenBlock) -> bool {
        Self::is_induc_base_proof_block(block) || Self::is_induc_step_proof_block(block)
    }

    fn induc_step_proof_keyword(strong: bool) -> &'static str {
        if strong {
            STRONG_INDUC
        } else {
            INDUC
        }
    }

    fn verify_induc_step_proof_keyword(
        block: &TokenBlock,
        expected: &str,
    ) -> Result<(), RuntimeError> {
        if block.token_at_add_index(1) == expected {
            return Ok(());
        }
        Err(Self::induc_parse_error(
            format!("induc: expected `? {}:` here", expected),
            block.line_file.clone(),
        ))
    }

    fn induc_parse_error(message: String, line_file: LineFile) -> RuntimeError {
        RuntimeError::from(ParseRuntimeError(
            RuntimeErrorStruct::new_with_msg_and_line_file(message, line_file),
        ))
    }
}
