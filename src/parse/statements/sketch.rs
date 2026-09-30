use crate::ast::line_file::SourceLine;
use crate::ast::stmt::{ProofBlockStmt, SketchStmt, Stmt};
use crate::runtime::{Runtime, RuntimeResult};
use crate::tokenize::TokenBlock;

use super::super::keywords::SKETCH;

impl Runtime {
    // sketch:
    //   <stmts…>
    pub(in super::super) fn parse_sketch_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(SKETCH)?;
        tb.expect_colon_end_of_header()?;
        self.push_parse_scope();
        let proof = self.parse_body_stmts(&tb.body);
        self.pop_parse_scope();
        let proof = proof?;
        Ok(Stmt::ProofBlock(ProofBlockStmt::SketchStmt(SketchStmt {
            proof,
            line_file: SourceLine::new(block.line, self.code_source.clone())
        })))
    }
}
