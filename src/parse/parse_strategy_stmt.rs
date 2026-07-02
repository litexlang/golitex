use crate::prelude::*;

impl Runtime {
    pub fn parse_def_strategy_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(STRATEGY)?;
        let mut strategy_names = Vec::new();
        loop {
            let name = tb.advance()?;
            is_valid_litex_name(&name).map_err(|msg| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone()),
                ))
            })?;
            strategy_names.push(name);
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
                    "strategy: unexpected token after strategy name list".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        if tb.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "strategy: expects a `prove:` block and optional proof body".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        let (forall_fact, inline_proof_start) = {
            let goal_block = tb.body.get_mut(0).ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "strategy: expected `prove:` or `?` goal block".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            self.parse_goal_forall_fact_block_with_inline_proof(goal_block, "strategy")?
        };
        validate_strategy_forall_fact(&forall_fact)?;

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

        Ok(DefStrategyStmt::new(
            strategy_names,
            forall_fact,
            prove_process,
            tb.line_file.clone(),
        )
        .into())
    }

    pub fn parse_stop_strategy_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(STOP)?;
        tb.skip_token(STRATEGY)?;
        let name = self.parse_module_qualified_reference_name(tb)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "stop strategy: unexpected token after strategy name".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(StopStrategyStmt::new(name, tb.line_file.clone()).into())
    }
}

fn validate_strategy_forall_fact(forall_fact: &ForallFact) -> Result<(), RuntimeError> {
    for dom_fact in forall_fact.dom_facts.iter() {
        if !matches!(dom_fact, Fact::AtomicFact(_)) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "strategy: forall dom-clause facts must be atomic".to_string(),
                    dom_fact.line_file(),
                ),
            )));
        }
    }

    if forall_fact.then_facts.len() != 1 {
        return Err(RuntimeError::from(ParseRuntimeError(
            RuntimeErrorStruct::new_with_msg_and_line_file(
                "strategy: forall then-clause must contain exactly one fact".to_string(),
                forall_fact.line_file.clone(),
            ),
        )));
    }

    let then_fact = forall_fact
        .then_facts
        .first()
        .expect("checked length above");
    if !matches!(then_fact, ExistOrAndChainAtomicFact::AtomicFact(_)) {
        return Err(RuntimeError::from(ParseRuntimeError(
            RuntimeErrorStruct::new_with_msg_and_line_file(
                "strategy: forall then-clause fact must be atomic".to_string(),
                then_fact.line_file(),
            ),
        )));
    }
    if matches!(
        then_fact,
        ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(_))
    ) {
        return Err(RuntimeError::from(ParseRuntimeError(
            RuntimeErrorStruct::new_with_msg_and_line_file(
                "strategy: forall then-clause fact must not be an equality fact".to_string(),
                then_fact.line_file(),
            ),
        )));
    }

    Ok(())
}
