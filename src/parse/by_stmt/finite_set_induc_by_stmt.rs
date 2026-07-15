use crate::prelude::*;

impl Runtime {
    /// Parses `by induc P:` as structural induction over all finite sets.
    /// `by induc n from m:` remains integer induction.
    pub fn parse_by_finite_set_induc_stmt_after_param(
        &mut self,
        tb: &mut TokenBlock,
        param: String,
    ) -> Result<Stmt, RuntimeError> {
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(Self::finite_set_induc_parse_error(
                "finite-set induc: expected end of head".to_string(),
                tb.line_file.clone(),
            ));
        }
        if tb.body.is_empty() {
            return Err(Self::finite_set_induc_parse_error(
                "finite-set induc: expects one or more `? <fact>` goal blocks".to_string(),
                tb.line_file.clone(),
            ));
        }

        let question_goal_count = tb
            .body
            .iter()
            .take_while(|block| {
                block.current_token_is_equal_to(QUESTION_GOAL)
                    && !Self::is_finite_set_induc_structured_proof_block(block)
            })
            .count();
        if question_goal_count == 0 {
            return Err(Self::finite_set_induc_parse_error(
                "finite-set induc: expects one or more `? <fact>` goal blocks before its proof"
                    .to_string(),
                tb.body[0].line_file.clone(),
            ));
        }

        let goal_line = tb.body[0].line_file.clone();
        let goal_param = [param.clone()];
        let mut to_prove = Vec::new();
        self.parse_in_local_free_param_scope(
            ParamObjType::Induc,
            &goal_param,
            goal_line,
            |this| {
                for block in tb.body.iter_mut().take(question_goal_count) {
                    to_prove.push(this.parse_question_goal_exist_or_and_chain_atomic_fact(
                        block,
                        "finite-set induc",
                    )?);
                }
                Ok(())
            },
        )?;

        let (base_proof, element_param, smaller_set_param, step_proof) =
            self.parse_finite_set_induc_proof_blocks(tb, &param, question_goal_count)?;

        Ok(ByFiniteSetInducStmt::new(
            to_prove,
            param,
            element_param,
            smaller_set_param,
            base_proof,
            step_proof,
            tb.line_file.clone(),
        )
        .into())
    }

    fn parse_finite_set_induc_proof_blocks(
        &mut self,
        tb: &mut TokenBlock,
        param: &str,
        goal_body_skip: usize,
    ) -> Result<(Vec<Stmt>, String, String, Vec<Stmt>), RuntimeError> {
        let mut base_proof: Option<Vec<Stmt>> = None;
        let mut step: Option<(String, String, Vec<Stmt>)> = None;

        for block in tb.body.iter_mut().skip(goal_body_skip) {
            if Self::is_finite_set_induc_base_proof_block(block) {
                if base_proof.is_some() {
                    return Err(Self::finite_set_induc_parse_error(
                        "finite-set induc: duplicated `? from` block".to_string(),
                        block.line_file.clone(),
                    ));
                }
                let names = [param.to_string()];
                let line_file = block.line_file.clone();
                base_proof = Some(self.parse_stmts_with_optional_free_param_scope(
                    ParamObjType::Induc,
                    &names,
                    line_file,
                    |this| {
                        this.verify_finite_set_induc_base_proof_header(block, param)?;
                        block
                            .body
                            .iter_mut()
                            .map(|body_block| this.parse_stmt(body_block))
                            .collect()
                    },
                )?);
                continue;
            }

            if Self::is_finite_set_induc_step_proof_block(block) {
                if step.is_some() {
                    return Err(Self::finite_set_induc_parse_error(
                        "finite-set induc: duplicated `? induc x, S:` block".to_string(),
                        block.line_file.clone(),
                    ));
                }
                let (element_param, smaller_set_param) =
                    self.parse_finite_set_induc_step_header(block, param)?;
                let names = [element_param.clone(), smaller_set_param.clone()];
                let line_file = block.line_file.clone();
                let proof = self.parse_stmts_with_optional_free_param_scope(
                    ParamObjType::Induc,
                    &names,
                    line_file,
                    |this| {
                        block
                            .body
                            .iter_mut()
                            .map(|body_block| this.parse_stmt(body_block))
                            .collect()
                    },
                )?;
                step = Some((element_param, smaller_set_param, proof));
                continue;
            }

            return Err(Self::finite_set_induc_parse_error(
                "finite-set induc: proof must use both `? from P = {}:` and `? induc x, S:` blocks"
                    .to_string(),
                block.line_file.clone(),
            ));
        }

        let base_proof = base_proof.ok_or_else(|| {
            Self::finite_set_induc_parse_error(
                "finite-set induc: missing `? from P = {}:` block".to_string(),
                tb.line_file.clone(),
            )
        })?;
        let (element_param, smaller_set_param, step_proof) = step.ok_or_else(|| {
            Self::finite_set_induc_parse_error(
                "finite-set induc: missing `? induc x, S:` block".to_string(),
                tb.line_file.clone(),
            )
        })?;
        Ok((base_proof, element_param, smaller_set_param, step_proof))
    }

    fn verify_finite_set_induc_base_proof_header(
        &mut self,
        block: &mut TokenBlock,
        param: &str,
    ) -> Result<(), RuntimeError> {
        block.skip_token(QUESTION_GOAL)?;
        block.skip_token(FROM)?;
        let header_fact =
            self.parse_header_fact_before_trailing_colon(block, "finite-set induc ? from", "", "")?;
        let Fact::AtomicFact(AtomicFact::EqualFact(equal_fact)) = header_fact else {
            return Err(Self::finite_set_induc_parse_error(
                "finite-set induc: `? from` expects an equality fact".to_string(),
                block.line_file.clone(),
            ));
        };
        let expected_param = obj_for_bound_param_in_scope(param.to_string(), ParamObjType::Induc);
        let empty_set: Obj = ListSet::new(vec![]).into();
        if equal_fact.left.to_string() != expected_param.to_string()
            || equal_fact.right.to_string() != empty_set.to_string()
        {
            return Err(Self::finite_set_induc_parse_error(
                format!("finite-set induc: `? from` must be `{} = {{}}`", param),
                block.line_file.clone(),
            ));
        }
        Ok(())
    }

    fn parse_finite_set_induc_step_header(
        &mut self,
        block: &mut TokenBlock,
        induction_param: &str,
    ) -> Result<(String, String), RuntimeError> {
        block.skip_token(QUESTION_GOAL)?;
        block.skip_token(INDUC)?;
        let element_param = block.advance()?;
        block.skip_token(COMMA)?;
        let smaller_set_param = block.advance()?;
        block.skip_token(COLON)?;
        if !block.exceed_end_of_head() {
            return Err(Self::finite_set_induc_parse_error(
                "finite-set induc: expected `? induc x, S:`".to_string(),
                block.line_file.clone(),
            ));
        }
        if element_param == smaller_set_param
            || element_param == induction_param
            || smaller_set_param == induction_param
        {
            return Err(Self::finite_set_induc_parse_error(
                "finite-set induc: `x`, `S`, and the induction parameter must have distinct names"
                    .to_string(),
                block.line_file.clone(),
            ));
        }
        Ok((element_param, smaller_set_param))
    }

    fn is_finite_set_induc_base_proof_block(block: &TokenBlock) -> bool {
        block.token_at_add_index(0) == QUESTION_GOAL && block.token_at_add_index(1) == FROM
    }

    fn is_finite_set_induc_step_proof_block(block: &TokenBlock) -> bool {
        block.token_at_add_index(0) == QUESTION_GOAL && block.token_at_add_index(1) == INDUC
    }

    fn is_finite_set_induc_structured_proof_block(block: &TokenBlock) -> bool {
        Self::is_finite_set_induc_base_proof_block(block)
            || Self::is_finite_set_induc_step_proof_block(block)
    }

    fn finite_set_induc_parse_error(message: String, line_file: LineFile) -> RuntimeError {
        RuntimeError::from(ParseRuntimeError(
            RuntimeErrorStruct::new_with_msg_and_line_file(message, line_file),
        ))
    }
}
