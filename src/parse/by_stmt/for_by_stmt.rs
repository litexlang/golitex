use crate::prelude::*;

impl Runtime {
    pub fn parse_by_for_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(FOR)?;
        let mut params: Vec<String> = vec![];
        let mut param_sets: Vec<ClosedRangeOrRange> = vec![];
        while tb.current()? != COLON {
            params.push(tb.advance()?);
            let set_obj = self.parse_obj(tb)?;
            let cr = match set_obj {
                crate::obj::Obj::Range(r) => ClosedRangeOrRange::Range(r),
                crate::obj::Obj::ClosedRange(c) => ClosedRangeOrRange::ClosedRange(c),
                _ => {
                    return Err(RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "by for: param set must be range or closed_range".to_string(),
                        tb.line_file.clone(),
                        None,
                    ));
                }
            };
            param_sets.push(cr);
            if tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
            }
        }
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::new_parse_error_with_msg_position_previous_error(
                "by for: expected end of head after params".to_string(),
                tb.line_file.clone(),
                None,
            ));
        }
        if tb.body.is_empty() {
            return Err(RuntimeError::new_parse_error_with_msg_position_previous_error(
                "by for: expects at least one body block".to_string(),
                tb.line_file.clone(),
                None,
            ));
        }

        let first_is_prove = tb.body[0].header.get(0).map(|s| s.as_str()) == Some(PROVE);

        let (dom_facts, then_facts, proof) = if first_is_prove {
            let then_block = tb.body.get_mut(0).ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error("Expected body".to_string(), tb.line_file.clone(), None)
            })?;
            let then_fact_count_upper_bound = then_block.body.len();
            then_block.skip_token_and_colon_and_exceed_end_of_head(PROVE)?;
            let mut then_facts: Vec<ExistOrAndChainAtomicFact> =
                Vec::with_capacity(then_fact_count_upper_bound);
            for b in then_block.body.iter_mut() {
                then_facts.push(self.parse_exist_or_and_chain_atomic_fact(b)?);
            }
            let proof_block_count_upper_bound = tb.body.len().saturating_sub(1);
            let mut proof: Vec<Stmt> = Vec::with_capacity(proof_block_count_upper_bound);
            for b in tb.body.iter_mut().skip(1) {
                proof.push(self.parse_stmt(b)?);
            }
            (Vec::new(), then_facts, proof)
        } else {
            let mut arrow_idx = None;
            for (i, b) in tb.body.iter().enumerate() {
                if b.header.get(0).map(|s| s.as_str()) == Some(PROVE) {
                    arrow_idx = Some(i);
                    break;
                }
            }
            let arrow_idx = arrow_idx.ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error("by for: expects a =>: block".to_string(), tb.line_file.clone(), None)
            })?;

            let mut dom_facts: Vec<AtomicFact> = Vec::with_capacity(arrow_idx);
            for b in tb.body[0..arrow_idx].iter_mut() {
                dom_facts.push(self.parse_atomic_fact(b, true)?);
            }

            let then_block = tb.body.get_mut(arrow_idx).ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error("Expected body".to_string(), tb.line_file.clone(), None)
            })?;
            let then_fact_count_upper_bound = then_block.body.len();
            then_block.skip_token_and_colon_and_exceed_end_of_head(PROVE)?;
            let mut then_facts: Vec<ExistOrAndChainAtomicFact> =
                Vec::with_capacity(then_fact_count_upper_bound);
            for b in then_block.body.iter_mut() {
                then_facts.push(self.parse_exist_or_and_chain_atomic_fact(b)?);
            }

            let proof_block_count_upper_bound = tb.body.len().saturating_sub(arrow_idx + 1);
            let mut proof: Vec<Stmt> = Vec::with_capacity(proof_block_count_upper_bound);
            for b in tb.body.iter_mut().skip(arrow_idx + 1) {
                proof.push(self.parse_stmt(b)?);
            }
            (dom_facts, then_facts, proof)
        };

        Ok(Stmt::ByForStmt(ByForStmt::new(
            params,
            param_sets,
            dom_facts,
            then_facts,
            proof,
            tb.line_file.clone(),
        )))
    }
}
