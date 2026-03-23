use super::TokenBlock;
use crate::common::keywords::{
    BY_CART_DEF, BY_CASES, BY_CONTRA, BY_EXTENSION, BY_FN_DEF, BY_INDUC, CASE, COLON, COMMA,
    ENUMERATE, EQUAL, FOR, FROM, IMPOSSIBLE, PROVE, RIGHT_ARROW,
};
use crate::error::ParsingError;
use crate::execute::Runtime;
use crate::fact::{AndChainAtomicFact, AtomicFact, ExistOrAndChainAtomicFact, Fact};
use crate::obj::Obj;
use crate::stmt::axiom_stmt::{
    ByCartDefAxiomStmt, ByCasesAxiomStmt, ByContraAxiomStmt, ByExtensionAxiomStmt,
    ByFnDefAxiomStmt, ByInducAxiomStmt, ClosedRangeOrRange, EnumerateAxiomStmt, ForAxiomStmt,
};
use crate::stmt::Stmt;

impl<'a> Runtime<'a> {
    pub fn parse_by_cases_axiom_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(BY_CASES)?;
        tb.skip_token(COLON)?;
        if tb.body.is_empty() {
            return Err(ParsingError::new(
                "cases: expects at least one body block".to_string(),
                tb.line_file,
                None,
            ));
        }
        let then_facts: Vec<Fact> = {
            let first = tb.body.get_mut(0).ok_or_else(|| {
                ParsingError::new("Expected body".to_string(), tb.line_file, None)
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
                return Err(ParsingError::new(
                    "case: expected end of head after condition".to_string(),
                    block.line_file,
                    None,
                ));
            }
            cases.push(case);
            let n = block.body.len();
            if n == 0 {
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
                        ParsingError::new("Expected body".to_string(), tb.line_file, None)
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
        Ok(Stmt::ByCasesAxiomStmt(ByCasesAxiomStmt::new(
            cases,
            then_facts,
            proofs,
            impossible_facts,
            tb.line_file,
        )))
    }

    pub fn parse_by_contra_axiom_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, ParsingError> {
        tb.skip_token(BY_CONTRA)?;
        let to_prove = self.parse_exist_or_and_chain_atomic_fact(tb)?.to_fact();
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(ParsingError::new(
                "contra: expected end of head after to_prove".to_string(),
                tb.line_file,
                None,
            ));
        }
        if tb.body.len() < 1 {
            return Err(ParsingError::new(
                "contra: expects at least one body block (impossible fact)".to_string(),
                tb.line_file,
                None,
            ));
        }
        let n = tb.body.len();
        let proof_stmt_block_count = n.saturating_sub(1);
        let mut proof = Vec::with_capacity(proof_stmt_block_count);
        for block in tb.body[0..n - 1].iter_mut() {
            proof.push(self.parse_stmt(block)?);
        }
        let mut last_block = tb
            .body
            .last_mut()
            .ok_or_else(|| ParsingError::new("Expected body".to_string(), tb.line_file, None))?;
        last_block.skip_token(IMPOSSIBLE)?;
        let impossible_fact = self.parse_atomic_fact(&mut last_block, true)?;
        Ok(Stmt::ByContraAxiomStmt(ByContraAxiomStmt::new(
            to_prove,
            proof,
            impossible_fact,
            tb.line_file,
        )))
    }

    pub fn parse_enumerate_axiom_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, ParsingError> {
        tb.skip_token(ENUMERATE)?;
        let mut params: Vec<String> = vec![];
        let mut param_sets: Vec<crate::obj::Obj> = vec![];
        if tb.current_token_is_equal_to(COLON) {
            return Err(ParsingError::new(
                "enum: expects at least one (param, set) pair".to_string(),
                tb.line_file,
                None,
            ));
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
            return Err(ParsingError::new(
                "enum: expected end of head after params".to_string(),
                tb.line_file,
                None,
            ));
        }
        let prove_idx = tb
            .body
            .iter()
            .position(|b| b.header.get(0).map(|s| s.as_str()) == Some(PROVE));
        let (to_prove, proof) = if let Some(i) = prove_idx {
            let to_prove: Vec<Fact> = tb.body[0..i]
                .iter_mut()
                .map(|b| self.parse_fact(b))
                .collect::<Result<_, _>>()?;
            let prove_block = tb.body.get_mut(i).ok_or_else(|| {
                ParsingError::new("Expected body".to_string(), tb.line_file, None)
            })?;
            prove_block.skip_token_and_colon_and_exceed_end_of_head(PROVE)?;
            let proof: Vec<Stmt> = prove_block
                .body
                .iter_mut()
                .map(|b| self.parse_stmt(b))
                .collect::<Result<_, _>>()?;
            (to_prove, proof)
        } else {
            (
                vec![],
                tb.body
                    .iter_mut()
                    .map(|b| self.parse_stmt(b))
                    .collect::<Result<_, _>>()?,
            )
        };
        Ok(Stmt::EnumerateAxiomStmt(EnumerateAxiomStmt::new(
            params,
            param_sets,
            to_prove,
            proof,
            tb.line_file,
        )))
    }

    pub fn parse_by_induc_axiom_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(BY_INDUC)?;
        let param = tb.advance()?;
        tb.skip_token(FROM)?;
        let induc_from = self.parse_obj(tb)?;
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(ParsingError::new(
                "induc: expected end of head".to_string(),
                tb.line_file,
                None,
            ));
        }
        if tb.body.is_empty() {
            return Err(ParsingError::new(
                "induc: expects at least one body block".to_string(),
                tb.line_file,
                None,
            ));
        }
        let fact: Vec<ExistOrAndChainAtomicFact> = {
            let then_block = tb.body.get_mut(0).ok_or_else(|| {
                ParsingError::new("Expected body".to_string(), tb.line_file, None)
            })?;
            then_block.skip_token_and_colon_and_exceed_end_of_head(RIGHT_ARROW)?;
            then_block
                .body
                .iter_mut()
                .map(|b| self.parse_exist_or_and_chain_atomic_fact(b))
                .collect::<Result<_, _>>()?
        };
        let proof: Vec<Stmt> = tb
            .body
            .iter_mut()
            .skip(1)
            .map(|b| self.parse_stmt(b))
            .collect::<Result<_, _>>()?;
        Ok(Stmt::ByInducAxiomStmt(ByInducAxiomStmt::new(
            fact,
            param,
            proof,
            induc_from,
            tb.line_file,
        )))
    }

    pub fn parse_for_axiom_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
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
                        tb.line_file,
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
            return Err(ParsingError::new(
                "for: expected end of head after params".to_string(),
                tb.line_file,
                None,
            ));
        }
        if tb.body.is_empty() {
            return Err(ParsingError::new(
                "for: expects at least one body block".to_string(),
                tb.line_file,
                None,
            ));
        }

        let first_is_arrow = tb.body[0].header.get(0).map(|s| s.as_str()) == Some(RIGHT_ARROW);

        let (dom_facts, then_facts, proof) = if first_is_arrow {
            // body[0] 是 =>:，其 body 是 then_facts；后面全是 proof
            let then_block = tb.body.get_mut(0).ok_or_else(|| {
                ParsingError::new("Expected body".to_string(), tb.line_file, None)
            })?;
            let then_fact_count_upper_bound = then_block.body.len();
            then_block.skip_token_and_colon_and_exceed_end_of_head(RIGHT_ARROW)?;
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
            // 前面若干 block 是 dom，直到 =>:；=>: 的 body 是 then_facts；再后面是 proof
            let mut arrow_idx = None;
            for (i, b) in tb.body.iter().enumerate() {
                if b.header.get(0).map(|s| s.as_str()) == Some(RIGHT_ARROW) {
                    arrow_idx = Some(i);
                    break;
                }
            }
            let arrow_idx = arrow_idx.ok_or_else(|| {
                ParsingError::new("for: expects a =>: block".to_string(), tb.line_file, None)
            })?;

            let mut dom_facts: Vec<ExistOrAndChainAtomicFact> = Vec::with_capacity(arrow_idx);
            for b in tb.body[0..arrow_idx].iter_mut() {
                dom_facts.push(self.parse_exist_or_and_chain_atomic_fact(b)?);
            }

            let then_block = tb.body.get_mut(arrow_idx).ok_or_else(|| {
                ParsingError::new("Expected body".to_string(), tb.line_file, None)
            })?;
            let then_fact_count_upper_bound = then_block.body.len();
            then_block.skip_token_and_colon_and_exceed_end_of_head(RIGHT_ARROW)?;
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

        Ok(Stmt::ForAxiomStmt(ForAxiomStmt::new(
            params,
            param_sets,
            dom_facts,
            then_facts,
            proof,
            tb.line_file,
        )))
    }

    pub fn parse_by_extension_axiom_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, ParsingError> {
        tb.skip_token(BY_EXTENSION)?;
        let left = self.parse_obj(tb)?;
        tb.skip_token(EQUAL)?;
        let right = self.parse_obj(tb)?;
        tb.skip_token(COLON)?;
        let proof: Vec<Stmt> = tb
            .body
            .iter_mut()
            .map(|b| self.parse_stmt(b))
            .collect::<Result<_, _>>()?;
        Ok(Stmt::ByExtensionAxiomStmt(ByExtensionAxiomStmt::new(
            left,
            right,
            proof,
            tb.line_file,
        )))
    }

    pub fn parse_by_fn_def_axiom_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, ParsingError> {
        tb.skip_token(BY_FN_DEF)?;
        let function = self.parse_obj(tb)?;
        Ok(Stmt::ByFnDefAxiomStmt(ByFnDefAxiomStmt::new(
            function,
            tb.line_file,
        )))
    }

    pub fn parse_by_cart_def_axiom_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, ParsingError> {
        tb.skip_token(BY_CART_DEF)?;
        let obj = self.parse_obj(tb)?;
        let cart = match obj {
            Obj::Cart(cart_value) => cart_value,
            _ => {
                return Err(ParsingError::new(
                    "by_cart_def: expected cart(...) object".to_string(),
                    tb.line_file,
                    None,
                ));
            }
        };
        Ok(Stmt::ByCartDefAxiomStmt(ByCartDefAxiomStmt::new(
            cart,
            tb.line_file,
        )))
    }
}
