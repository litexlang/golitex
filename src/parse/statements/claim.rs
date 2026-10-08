use crate::ast::line_file::SourceLine;
use crate::ast::stmt::{ClaimStmt, ProofBlockStmt, Stmt};
use crate::runtime::{Runtime, RuntimeResult};
use crate::tokenize::TokenBlock;

use super::super::keywords::CLAIM;

impl Runtime {
    // claim:
    //   ? <fact>
    //   <proof stmts…>
    pub(in super::super) fn parse_claim_stmt(&mut self, block: &TokenBlock) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(CLAIM)?;
        tb.expect_colon_end_of_header()?;
        if tb.body.is_empty() {
            return Err(
                tb.parse_error("claim: expects a `? <fact>` goal block and optional proof body")
            );
        }
        let mut goal = tb.body[0].clone();
        let fact = self.parse_goal_fact(&mut goal, "claim")?;
        let proof_blocks = &tb.body[1..];
        let proof = if let Some(params) = Self::forall_params_of_fact(&fact) {
            self.with_forall_params_occupied(params, &tb, |this| {
                this.parse_body_stmts(proof_blocks)
            })?
        } else {
            self.push_parse_scope();
            let proof = self.parse_body_stmts(proof_blocks);
            self.pop_parse_scope();
            proof?
        };
        Ok(Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(ClaimStmt {
            fact,
            proof,
            line_file: SourceLine::new(block.line, self.code_source.clone()),
        })))
    }
}
