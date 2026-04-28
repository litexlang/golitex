use crate::parse::parse_helpers::collect_forall_param_names_from_facts;
use crate::prelude::*;

impl Runtime {
    pub fn parse_by_cases_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(CASES)?;
        // `by cases => goal:` — goal on the header line; body starts with `case` (no `prove:` block).
        let (then_facts, case_body_skip): (Vec<Fact>, usize) = if tb.current()? == RIGHT_ARROW {
            tb.skip_token(RIGHT_ARROW)?;
            let header = &tb.header;
            if header.len() < tb.parse_index + 2
                || header.last().map(|t| t.as_str()) != Some(COLON)
            {
                return Err(RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by cases => ... : expected a goal fact and a trailing `:` on the same line".to_string(),
                    tb.line_file.clone(),
                ))));
            }
            let colon_pos = header.len() - 1;
            let fact_tokens = header[tb.parse_index..colon_pos].to_vec();
            if fact_tokens.is_empty() {
                return Err(RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by cases => ... : expected a non-empty goal after `=>`".to_string(),
                    tb.line_file.clone(),
                ))));
            }
            let mut fact_tb = TokenBlock::new(fact_tokens, vec![], tb.line_file.clone());
            let fact = self.parse_fact(&mut fact_tb)?;
            if !fact_tb.exceed_end_of_head() {
                return Err(RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by cases => ... : unfinished tokens in goal".to_string(),
                    tb.line_file.clone(),
                ))));
            }
            tb.parse_index = colon_pos + 1;
            if !tb.exceed_end_of_head() {
                return Err(RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by cases => ... : unexpected tokens after `:`".to_string(),
                    tb.line_file.clone(),
                ))));
            }
            (vec![fact], 0)
        } else {
            tb.skip_token(COLON)?;
            if tb.body.is_empty() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file("cases: expects at least one body block".to_string(), tb.line_file.clone()),
                )));
            }
            let then_facts: Vec<Fact> = {
                let first = tb.body.get_mut(0).ok_or_else(|| {
                    RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file("Expected body".to_string(), tb.line_file.clone())))
                })?;
                first.skip_token_and_colon_and_exceed_end_of_head(PROVE)?;
                first
                    .body
                    .iter_mut()
                    .map(|b| self.parse_fact(b))
                    .collect::<Result<_, _>>()?
            };
            (then_facts, 1)
        };

        let min_body = case_body_skip + 1;
        if tb.body.len() < min_body {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "cases: expects at least one `case` arm".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        let forall_param_names = collect_forall_param_names_from_facts(&then_facts);
        let line_file = tb.line_file.clone();
        let (cases, proofs, impossible_facts) = if forall_param_names.is_empty() {
            self.parse_by_cases_case_and_proof_blocks(tb, case_body_skip)?
        } else {
            self.parse_in_local_free_param_scope(ParamObjType::Forall, &forall_param_names, line_file, |rt| {
                rt.parse_by_cases_case_and_proof_blocks(tb, case_body_skip)
            })?
        };
        Ok(ByCasesStmt::new(
            cases,
            then_facts,
            proofs,
            impossible_facts,
            tb.line_file.clone(),
        )
        .into())
    }

    /// Parses all `case ...:` arms (conditions, proof bodies, optional `impossible` facts).
    fn parse_by_cases_case_and_proof_blocks(
        &mut self,
        tb: &mut TokenBlock,
        case_body_skip: usize,
    ) -> Result<
        (
            Vec<AndChainAtomicFact>,
            Vec<Vec<Stmt>>,
            Vec<Option<AtomicFact>>,
        ),
        RuntimeError,
    > {
        let case_block_count = tb.body.len().saturating_sub(case_body_skip);
        let mut cases: Vec<AndChainAtomicFact> = Vec::with_capacity(case_block_count);
        let mut proofs: Vec<Vec<Stmt>> = Vec::with_capacity(case_block_count);
        let mut impossible_facts: Vec<Option<AtomicFact>> = Vec::with_capacity(case_block_count);
        for block in tb.body.iter_mut().skip(case_body_skip) {
            block.skip_token(CASE)?;
            let case = self.parse_and_chain_atomic_fact_allow_leading_not(block)?;
            block.skip_token(COLON)?;
            if !block.exceed_end_of_head() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file("case: expected end of head after condition".to_string(), block.line_file.clone()),
                )));
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
                        RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file("Expected body".to_string(), tb.line_file.clone())))
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
        Ok((cases, proofs, impossible_facts))
    }
}
