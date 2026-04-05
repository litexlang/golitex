use crate::prelude::*;

impl Runtime {
    pub fn parse_by_cases_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(CASES)?;
        tb.skip_token(COLON)?;
        if tb.body.is_empty() {
            return Err(RuntimeError::new_parse_error_with_msg_position_previous_error(
                "cases: expects at least one body block".to_string(),
                tb.line_file.clone(),
                None,
            ));
        }
        let then_facts: Vec<Fact> = {
            let first = tb.body.get_mut(0).ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error("Expected body".to_string(), tb.line_file.clone(), None)
            })?;
            first.skip_token_and_colon_and_exceed_end_of_head(PROVE)?;
            first
                .body
                .iter_mut()
                .map(|b| self.parse_fact(b))
                .collect::<Result<_, _>>()?
        };
        let case_block_count = tb.body.len().saturating_sub(1);
        let mut cases: Vec<AndChainAtomicFact> = Vec::with_capacity(case_block_count);
        let mut proofs: Vec<Vec<Stmt>> = Vec::with_capacity(case_block_count);
        let mut impossible_facts: Vec<Option<AtomicFact>> = Vec::with_capacity(case_block_count);
        for block in tb.body.iter_mut().skip(1) {
            block.skip_token(CASE)?;
            let case = self.parse_and_chain_atomic_fact(block)?;
            block.skip_token(COLON)?;
            if !block.exceed_end_of_head() {
                return Err(RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "case: expected end of head after condition".to_string(),
                    block.line_file.clone(),
                    None,
                ));
            }
            cases.push(case);
            let n = block.body.len();
            if block.body.is_empty() {
                proofs.push(vec![]);
                impossible_facts.push(None);
                continue;
            }
            let (proof_stmts, impossible) =
                if block.body[n - 1].header.get(0).map(|s| s.as_str()) == Some(IMPOSSIBLE) {
                    let proof: Vec<Stmt> = block.body[0..n - 1]
                        .iter_mut()
                        .map(|b| self.parse_stmt(b))
                        .collect::<Result<_, _>>()?;
                    let last_block = block.body.get_mut(n - 1).ok_or_else(|| {
                        RuntimeError::new_parse_error_with_msg_position_previous_error("Expected body".to_string(), tb.line_file.clone(), None)
                    })?;
                    last_block.skip_token(IMPOSSIBLE)?;
                    let imp = self.parse_atomic_fact(last_block, true)?;
                    (proof, Some(imp))
                } else {
                    let proof: Vec<Stmt> = block
                        .body
                        .iter_mut()
                        .map(|b| self.parse_stmt(b))
                        .collect::<Result<_, _>>()?;
                    (proof, None)
                };
            proofs.push(proof_stmts);
            impossible_facts.push(impossible);
        }
        Ok(Stmt::ByCasesStmt(ByCasesStmt::new(
            cases,
            then_facts,
            proofs,
            impossible_facts,
            tb.line_file.clone(),
        )))
    }
}
