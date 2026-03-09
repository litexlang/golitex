use crate::fact::AndFactOrSpecFact;
use crate::errors::ParsingError;
use crate::fact::Fact;
use crate::keywords::{
    CASE, CASES, COLON, COMMA, CONTRA, ENUM, EQUAL, EQUAL_SET, FOR, FROM, IMPOSSIBLE, INDUC, PROVE,
    RIGHT_ARROW, VIEW_FN_AS_SET,
};
use crate::fact::OrFactOrAndFactOrSpecFact;
use super::Parser;
use crate::stmt::proof_technique_stmt::{
    ClosedRangeOrRange, ProveByContradictionStmt, ProveByEnumerationStmt, ProveByEqualSetStmt,
    ProveByInductionStmt, ProveCaseByCaseStmt, ProveForStmt, ProofTechniqueStmt, ViewFnAsSetStmt,
};
use crate::stmt::Stmt;
use super::TokenBlock;

impl Parser {
    pub fn prove_case_by_case_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(CASES)?;
        tb.skip_token(COLON)?;
        if tb.body.is_empty() {
            return Err(ParsingError::new("cases: expects at least one body block", tb.line_file_index));
        }
        let then_facts: Vec<Fact> = {
            let first = tb.body.get_mut(0).unwrap();
            first.skip_token_and_colon_and_exceed_end_of_head(RIGHT_ARROW)?;
            first.body.iter_mut().map(|b| self.fact(b)).collect::<Result<_, _>>()?
        };
        let mut cases: Vec<AndFactOrSpecFact> = vec![];
        let mut proofs: Vec<Vec<Stmt>> = vec![];
        let mut impossible_facts: Vec<Option<OrFactOrAndFactOrSpecFact>> = vec![];
        for block in tb.body.iter_mut().skip(1) {
            block.skip_token(CASE)?;
            let case = self.and_spec_fact(block)?;
            block.skip_token(COLON)?;
            if !block.exceed_end_of_head() {
                return Err(ParsingError::new("case: expected end of head after condition", block.line_file_index));
            }
            cases.push(case);
            let n = block.body.len();
            if n == 0 {
                proofs.push(vec![]);
                impossible_facts.push(None);
                continue;
            }
            let (proof_stmts, impossible) = if block.body[n - 1].header.get(0).map(|s| s.as_str()) == Some(IMPOSSIBLE) {
                let proof: Vec<Stmt> = block.body[0..n - 1].iter_mut().map(|b| self.stmt(b)).collect::<Result<_, _>>()?;
                let last_block = block.body.get_mut(n - 1).unwrap();
                last_block.skip_token(IMPOSSIBLE)?;
                let imp = self.or_and_spec_fact(last_block)?;
                (proof, Some(imp))
            } else {
                let proof: Vec<Stmt> = block.body.iter_mut().map(|b| self.stmt(b)).collect::<Result<_, _>>()?;
                (proof, None)
            };
            proofs.push(proof_stmts);
            impossible_facts.push(impossible);
        }
        Ok(Stmt::ProofTechnique(ProofTechniqueStmt::ProveCaseByCase(
            ProveCaseByCaseStmt::new(cases, then_facts, proofs, impossible_facts, Some(tb.line_file_index)),
        )))
    }

    pub fn prove_by_contradiction_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(CONTRA)?;
        let to_prove = self.or_and_spec_fact(tb)?.to_fact();
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(ParsingError::new("contra: expected end of head after to_prove", tb.line_file_index));
        }
        if tb.body.len() < 1 {
            return Err(ParsingError::new("contra: expects at least one body block (impossible fact)", tb.line_file_index));
        }
        let n = tb.body.len();
        let mut proof = vec![];
        for block in tb.body[0..n - 1].iter_mut() {
            proof.push(self.stmt(block)?);
        }
        let mut last_block = tb.body.last_mut().unwrap();
        last_block.skip_token(IMPOSSIBLE)?;
        let impossible_fact = self.or_and_spec_fact(&mut last_block)?;
        Ok(Stmt::ProofTechnique(ProofTechniqueStmt::ProveByContradiction(
            ProveByContradictionStmt::new(to_prove, proof, impossible_fact, Some(tb.line_file_index)),
        )))
    }

    pub fn prove_by_enumeration_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(ENUM)?;
        let mut params: Vec<String> = vec![];
        let mut param_sets: Vec<crate::obj::Obj> = vec![];
        if tb.current()? == COLON {
            return Err(ParsingError::new("enum: expects at least one (param, set) pair", tb.line_file_index));
        }
        while tb.current()? != COLON {
            params.push(tb.advance()?);
            param_sets.push(self.obj(tb)?);
            if tb.current()? == COMMA {
                tb.skip_token(COMMA)?;
            }
        }
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(ParsingError::new("enum: expected end of head after params", tb.line_file_index));
        }
        let prove_idx = tb.body.iter().position(|b| b.header.get(0).map(|s| s.as_str()) == Some(PROVE));
        let (to_prove, proof) = if let Some(i) = prove_idx {
            let to_prove: Vec<Fact> = tb.body[0..i].iter_mut().map(|b| self.fact(b)).collect::<Result<_, _>>()?;
            let prove_block = tb.body.get_mut(i).unwrap();
            prove_block.skip_token_and_colon_and_exceed_end_of_head(PROVE)?;
            let proof: Vec<Stmt> = prove_block.body.iter_mut().map(|b| self.stmt(b)).collect::<Result<_, _>>()?;
            (to_prove, proof)
        } else {
            (vec![], tb.body.iter_mut().map(|b| self.stmt(b)).collect::<Result<_, _>>()?)
        };
        Ok(Stmt::ProofTechnique(ProofTechniqueStmt::ProveByEnumeration(
            ProveByEnumerationStmt::new(params, param_sets, to_prove, proof, Some(tb.line_file_index)),
        )))
    }

    pub fn prove_by_induction_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(INDUC)?;
        let param = tb.advance()?;
        tb.skip_token(FROM)?;
        let induc_from = self.obj(tb)?;
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(ParsingError::new("induc: expected end of head", tb.line_file_index));
        }
        if tb.body.is_empty() {
            return Err(ParsingError::new("induc: expects at least one body block", tb.line_file_index));
        }
        let fact: Vec<OrFactOrAndFactOrSpecFact> = {
            let then_block = tb.body.get_mut(0).unwrap();
            then_block.skip_token_and_colon_and_exceed_end_of_head(RIGHT_ARROW)?;
            then_block.body.iter_mut().map(|b| self.or_and_spec_fact(b)).collect::<Result<_, _>>()?
        };
        let proof: Vec<Stmt> = tb.body.iter_mut().skip(1).map(|b| self.stmt(b)).collect::<Result<_, _>>()?;
        Ok(Stmt::ProofTechnique(ProofTechniqueStmt::ProveByInduction(
            ProveByInductionStmt::new(fact, param, proof, induc_from, Some(tb.line_file_index)),
        )))
    }

    pub fn prove_for_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(FOR)?;
        let mut params: Vec<String> = vec![];
        let mut param_sets: Vec<ClosedRangeOrRange> = vec![];
        while tb.current()? != COLON {
            params.push(tb.advance()?);
            let set_obj = self.obj(tb)?;
            let cr = match set_obj {
                crate::obj::Obj::Range(r) => ClosedRangeOrRange::Range(r),
                crate::obj::Obj::ClosedRange(c) => ClosedRangeOrRange::ClosedRange(c),
                _ => {
                    return Err(ParsingError::new(
                        "for: param set must be range or closed_range",
                        tb.line_file_index,
                    ));
                }
            };
            param_sets.push(cr);
            if tb.current()? == COMMA {
                tb.skip_token(COMMA)?;
            }
        }
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(ParsingError::new("for: expected end of head after params", tb.line_file_index));
        }
        if tb.body.is_empty() {
            return Err(ParsingError::new("for: expects at least one body block", tb.line_file_index));
        }

        let mut dom_facts: Vec<OrFactOrAndFactOrSpecFact> = vec![];
        let mut then_facts: Vec<OrFactOrAndFactOrSpecFact> = vec![];
        let mut proof: Vec<Stmt> = vec![];

        let first_is_arrow = tb.body[0].header.get(0).map(|s| s.as_str()) == Some(RIGHT_ARROW);

        if first_is_arrow {
            // body[0] 是 =>:，其 body 是 then_facts；后面全是 proof
            let then_block = tb.body.get_mut(0).unwrap();
            then_block.parse_index = 0;
            then_block.skip_token_and_colon_and_exceed_end_of_head(RIGHT_ARROW)?;
            for b in then_block.body.iter_mut() {
                then_facts.push(self.or_and_spec_fact(b)?);
            }
            for b in tb.body.iter_mut().skip(1) {
                proof.push(self.stmt(b)?);
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
            let arrow_idx = arrow_idx.ok_or_else(|| ParsingError::new("for: expects a =>: block", tb.line_file_index))?;

            for b in tb.body[0..arrow_idx].iter_mut() {
                dom_facts.push(self.or_and_spec_fact(b)?);
            }

            let then_block = tb.body.get_mut(arrow_idx).unwrap();
            then_block.parse_index = 0;
            then_block.skip_token_and_colon_and_exceed_end_of_head(RIGHT_ARROW)?;
            for b in then_block.body.iter_mut() {
                then_facts.push(self.or_and_spec_fact(b)?);
            }

            for b in tb.body.iter_mut().skip(arrow_idx + 1) {
                proof.push(self.stmt(b)?);
            }
        }

        Ok(Stmt::ProofTechnique(ProofTechniqueStmt::ProveForStmt(ProveForStmt::new(
            params,
            param_sets,
            dom_facts,
            then_facts,
            proof,
            Some(tb.line_file_index),
        ))))
    }

    pub fn prove_equal_set_by_def_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(EQUAL_SET)?;
        let left = self.obj(tb)?;
        tb.skip_token(EQUAL)?;
        let right = self.obj(tb)?;
        tb.skip_token(COLON)?;
        let proof: Vec<Stmt> = tb.body.iter_mut().map(|b| self.stmt(b)).collect::<Result<_, _>>()?;
        Ok(Stmt::ProofTechnique(ProofTechniqueStmt::ProveByEqualSet(
            ProveByEqualSetStmt::new(left, right, proof, Some(tb.line_file_index)),
        )))
    }

    pub fn view_fn_as_set_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(VIEW_FN_AS_SET)?;
        let function = self.obj(tb)?;
        Ok(Stmt::ProofTechnique(ProofTechniqueStmt::ViewFnAsSet(ViewFnAsSetStmt::new(
            function,
            Some(tb.line_file_index),
        ))))
    }
}
