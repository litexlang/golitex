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
        let _ = std::fs::write(
            "/tmp/litex_claim_dbg.txt",
            format!(
                "claim body_len={} first_headers={:?}\n",
                tb.body.len(),
                tb.body
                    .iter()
                    .map(|b| b.header.get(0).cloned().unwrap_or_default())
                    .collect::<Vec<_>>()
            ),
        );
        let mut goal = tb.body[0].clone();
        let fact = self.parse_goal_fact(&mut goal, "claim")?;
        let _ = std::fs::write(
            "/tmp/litex_claim_dbg2.txt",
            format!("goal_ok proof_blocks={}\n", tb.body.len().saturating_sub(1)),
        );
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
            line_file: SourceLine::new(block.line, self.code_source.clone()),
        })))
    }
}
