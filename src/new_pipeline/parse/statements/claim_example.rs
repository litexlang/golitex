use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::ast::stmt::{ClaimStmt, ExampleStmt, ProofBlockStmt, Stmt};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

use super::super::keywords::{CLAIM, EXAMPLE};

impl Runtime {
    // claim:
    //   ? <fact>
    //   <proof stmts…>
    pub(in super::super) fn parse_claim_stmt(&mut self, block: &TokenBlock) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(CLAIM)?;
        tb.expect_colon_end_of_header()?;
        if tb.body.is_empty() {
            return Err(tb.parse_error(
                "claim: expects a `? <fact>` goal block and optional proof body",
            ));
        }
        let mut goal = tb.body[0].clone();
        let fact = self.parse_goal_fact(&mut goal, "claim")?;
        let proof_blocks = &tb.body[1..];
        let proof = if let Some(params) = Self::forall_params_of_fact(&fact) {
            self.with_forall_params_occupied(params, &tb, |this| {
                this.parse_body_stmts(proof_blocks)
            })?
        } else {
            self.parse_body_stmts(proof_blocks)?
        };
        Ok(Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(ClaimStmt {
            fact,
            proof,
            line_file: LineFile::new(block.line, block.source_path.clone()),
        })))
    }

    // example:
    //   ? <fact>
    //   <proof stmts…>
    pub(in super::super) fn parse_example_stmt(&mut self, block: &TokenBlock) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(EXAMPLE)?;
        tb.expect_colon_end_of_header()?;
        if tb.body.is_empty() {
            return Err(tb.parse_error(
                "example: expects a `? <fact>` goal block and optional proof body",
            ));
        }
        let mut goal = tb.body[0].clone();
        let fact = self.parse_goal_fact(&mut goal, "example")?;
        let proof_blocks = &tb.body[1..];
        let proof = if let Some(params) = Self::forall_params_of_fact(&fact) {
            self.with_forall_params_occupied(params, &tb, |this| {
                this.parse_body_stmts(proof_blocks)
            })?
        } else {
            self.parse_body_stmts(proof_blocks)?
        };
        Ok(Stmt::ProofBlock(ProofBlockStmt::ExampleStmt(ExampleStmt {
            fact,
            proof,
            line_file: LineFile::new(block.line, block.source_path.clone()),
        })))
    }
}
