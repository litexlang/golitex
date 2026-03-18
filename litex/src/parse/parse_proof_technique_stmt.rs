use crate::error::ParsingError;
use crate::fact::{Fact, AndChainAtomicFact, ExistOrAndChainAtomicFact};
use crate::common::keywords::{
    CASE, CASES, COLON, COMMA, CONTRA, ENUM, EQUAL, EQUAL_SET, FOR, FROM, IMPOSSIBLE, INDUC, PROVE,
    RIGHT_ARROW, VIEW_FN_AS_SET,
};
use crate::execute::Executor;
use crate::stmt::proof_technique_stmt::{
    ClosedRangeOrRange, ProveByContradictionStmt, ProveByEnumerationStmt, ProveByEqualSetStmt,
    ProveByInductionStmt, ProveCaseByCaseStmt, ProveForStmt, ViewFnAsSetStmt,
};
use crate::stmt::Stmt;
use super::TokenBlock;

impl<'a> Executor<'a> {
    pub fn prove_case_by_case_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(CASES)?;
        tb.skip_token(COLON)?;
        if tb.body.is_empty() {
            return Err(ParsingError::new("cases: expects at least one body block".to_string(), tb.line_file_index, None));
        }
        let then_facts: Vec<Fact> = {
            let first = tb.body.get_mut(0).ok_or_else(|| ParsingError::new("Expected body".to_string(), tb.line_file_index, None))?;
            first.skip_token_and_colon_and_exceed_end_of_head(RIGHT_ARROW)?;
            first.body.iter_mut().map(|b| self.parse_fact(b)).collect::<Result<_, _>>()?
        };
        let mut cases: Vec<AndChainAtomicFact> = vec![];
        let mut proofs: Vec<Vec<Stmt>> = vec![];
        let mut impossible_facts: Vec<Option<ExistOrAndChainAtomicFact>> = vec![];
        for block in tb.body.iter_mut().skip(1) {
            block.skip_token(CASE)?;
            let case = self.parse_and_chain_atomic_fact(block)?;
            block.skip_token(COLON)?;
            if !block.exceed_end_of_head() {
                return Err(ParsingError::new("case: expected end of head after condition".to_string(), block.line_file_index, None));
            }
            cases.push(case);
            let n = block.body.len();
            if n == 0 {
                proofs.push(vec![]);
                impossible_facts.push(None);
                continue;
            }
            let (proof_stmts, impossible) = if block.body[n - 1].header.get(0).map(|s| s.as_str()) == Some(IMPOSSIBLE) {
                let proof: Vec<Stmt> = block.body[0..n - 1].iter_mut().map(|b| self.parse_stmt(b)).collect::<Result<_, _>>()?;
                let last_block = block.body.get_mut(n - 1).ok_or_else(|| ParsingError::new("Expected body".to_string(), tb.line_file_index, None))?;
                last_block.skip_token(IMPOSSIBLE)?;
                let imp = self.parse_exist_or_and_chain_atomic_fact(last_block)?;
                (proof, Some(imp))
            } else {
                let proof: Vec<Stmt> = block.body.iter_mut().map(|b| self.parse_stmt(b)).collect::<Result<_, _>>()?;
                (proof, None)
            };
            proofs.push(proof_stmts);
            impossible_facts.push(impossible);
        }
        Ok(Stmt::ProveCaseByCaseStmt(
            ProveCaseByCaseStmt::new(cases, then_facts, proofs, impossible_facts, tb.line_file_index),
        ))
    }

    pub fn prove_by_contradiction_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(CONTRA)?;
        let to_prove = self.parse_exist_or_and_chain_atomic_fact(tb)?.to_fact();
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(ParsingError::new("contra: expected end of head after to_prove".to_string(), tb.line_file_index, None));
        }
        if tb.body.len() < 1 {
            return Err(ParsingError::new("contra: expects at least one body block (impossible fact)".to_string(), tb.line_file_index, None));
        }
        let n = tb.body.len();
        let mut proof = vec![];
        for block in tb.body[0..n - 1].iter_mut() {
            proof.push(self.parse_stmt(block)?);
        }
        let mut last_block = tb.body.last_mut().ok_or_else(|| ParsingError::new("Expected body".to_string(), tb.line_file_index, None))?;
        last_block.skip_token(IMPOSSIBLE)?;
        let impossible_fact = self.parse_exist_or_and_chain_atomic_fact(&mut last_block)?;
        Ok(Stmt::ProveByContradictionStmt(
            ProveByContradictionStmt::new(to_prove, proof, impossible_fact, tb.line_file_index),
        ))
    }

    pub fn prove_by_enumeration_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(ENUM)?;
        let mut params: Vec<String> = vec![];
        let mut param_sets: Vec<crate::obj::Obj> = vec![];
        if tb.current_token_is_equal_to(COLON) {
            return Err(ParsingError::new("enum: expects at least one (param, set) pair".to_string(), tb.line_file_index, None));
        }
        while tb.current()? != COLON {
            params.push(tb.advance()?);
            param_sets.push(self.parse_obj(tb)?);
            if tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
            }
        }
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(ParsingError::new("enum: expected end of head after params".to_string(), tb.line_file_index, None));
        }
        let prove_idx = tb.body.iter().position(|b| b.header.get(0).map(|s| s.as_str()) == Some(PROVE));
        let (to_prove, proof) = if let Some(i) = prove_idx {
            let to_prove: Vec<Fact> = tb.body[0..i].iter_mut().map(|b| self.parse_fact(b)).collect::<Result<_, _>>()?;
            let prove_block = tb.body.get_mut(i).ok_or_else(|| ParsingError::new("Expected body".to_string(), tb.line_file_index, None))?;
            prove_block.skip_token_and_colon_and_exceed_end_of_head(PROVE)?;
            let proof: Vec<Stmt> = prove_block.body.iter_mut().map(|b| self.parse_stmt(b)).collect::<Result<_, _>>()?;
            (to_prove, proof)
        } else {
            (vec![], tb.body.iter_mut().map(|b| self.parse_stmt(b)).collect::<Result<_, _>>()?)
        };
        Ok(Stmt::ProveByEnumerationStmt(
            ProveByEnumerationStmt::new(params, param_sets, to_prove, proof, tb.line_file_index),
        ))
    }

    pub fn prove_by_induction_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(INDUC)?;
        let param = tb.advance()?;
        tb.skip_token(FROM)?;
        let induc_from = self.parse_obj(tb)?;
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(ParsingError::new("induc: expected end of head".to_string(), tb.line_file_index, None));
        }
        if tb.body.is_empty() {
            return Err(ParsingError::new("induc: expects at least one body block".to_string(), tb.line_file_index, None));
        }
        let fact: Vec<ExistOrAndChainAtomicFact> = {
            let then_block = tb.body.get_mut(0).ok_or_else(|| ParsingError::new("Expected body".to_string(), tb.line_file_index, None))?;
            then_block.skip_token_and_colon_and_exceed_end_of_head(RIGHT_ARROW)?;
            then_block.body.iter_mut().map(|b| self.parse_exist_or_and_chain_atomic_fact(b)).collect::<Result<_, _>>()?
        };
        let proof: Vec<Stmt> = tb.body.iter_mut().skip(1).map(|b| self.parse_stmt(b)).collect::<Result<_, _>>()?;
        Ok(Stmt::ProveByInductionStmt(
            ProveByInductionStmt::new(fact, param, proof, induc_from, tb.line_file_index),
        ))
    }

    pub fn prove_for_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
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
                    return Err(ParsingError::new(
                        "for: param set must be range or closed_range".to_string(),
                        tb.line_file_index,
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
            return Err(ParsingError::new("for: expected end of head after params".to_string(), tb.line_file_index, None));
        }
        if tb.body.is_empty() {
            return Err(ParsingError::new("for: expects at least one body block".to_string(), tb.line_file_index, None));
        }

        let mut dom_facts: Vec<ExistOrAndChainAtomicFact> = vec![];
        let mut then_facts: Vec<ExistOrAndChainAtomicFact> = vec![];
        let mut proof: Vec<Stmt> = vec![];

        let first_is_arrow = tb.body[0].header.get(0).map(|s| s.as_str()) == Some(RIGHT_ARROW);

        if first_is_arrow {
            // body[0] 是 =>:，其 body 是 then_facts；后面全是 proof
            let then_block = tb.body.get_mut(0).ok_or_else(|| ParsingError::new("Expected body".to_string(), tb.line_file_index, None))?;
            then_block.parse_index = 0;
            then_block.skip_token_and_colon_and_exceed_end_of_head(RIGHT_ARROW)?;
            for b in then_block.body.iter_mut() {
                then_facts.push(self.parse_exist_or_and_chain_atomic_fact(b)?);
            }
            for b in tb.body.iter_mut().skip(1) {
                proof.push(self.parse_stmt(b)?);
            }
        } else {
            // 前面若干 block 是 dom，直到 =>:；=>: 的 body 是 then_facts；再后面是 proof
            let mut arrow_idx = None;
            for (i, b) in tb.body.iter().enumerate() {
                if b.header.get(0).map(|s| s.as_str()) == Some(RIGHT_ARROW) {
                    arrow_idx = Some(i);
                    break;
                }
            }
            let arrow_idx = arrow_idx.ok_or_else(|| ParsingError::new("for: expects a =>: block".to_string(), tb.line_file_index, None))?;

            for b in tb.body[0..arrow_idx].iter_mut() {
                dom_facts.push(self.parse_exist_or_and_chain_atomic_fact(b)?);
            }

            let then_block = tb.body.get_mut(arrow_idx).ok_or_else(|| ParsingError::new("Expected body".to_string(), tb.line_file_index, None))?;
            then_block.parse_index = 0;
            then_block.skip_token_and_colon_and_exceed_end_of_head(RIGHT_ARROW)?;
            for b in then_block.body.iter_mut() {
                then_facts.push(self.parse_exist_or_and_chain_atomic_fact(b)?);
            }

            for b in tb.body.iter_mut().skip(arrow_idx + 1) {
                proof.push(self.parse_stmt(b)?);
            }
        }

        Ok(Stmt::ProveForStmt(ProveForStmt::new(
            params,
            param_sets,
            dom_facts,
            then_facts,
            proof,
            tb.line_file_index,
        )))
    }

    pub fn prove_equal_set_by_def_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(EQUAL_SET)?;
        let left = self.parse_obj(tb)?;
        tb.skip_token(EQUAL)?;
        let right = self.parse_obj(tb)?;
        tb.skip_token(COLON)?;
        let proof: Vec<Stmt> = tb.body.iter_mut().map(|b| self.parse_stmt(b)).collect::<Result<_, _>>()?;
        Ok(Stmt::ProveByEqualSetStmt(
            ProveByEqualSetStmt::new(left, right, proof, tb.line_file_index),
        ))
    }

    pub fn view_fn_as_set_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(VIEW_FN_AS_SET)?;
        let function = self.parse_obj(tb)?;
        Ok(Stmt::ViewFnAsSetStmt(ViewFnAsSetStmt::new(
            function,
            tb.line_file_index,
        )))
    }
}
