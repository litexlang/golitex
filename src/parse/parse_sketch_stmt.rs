use crate::prelude::*;

impl Runtime {
    pub fn parse_sketch_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(SKETCH)?;
        tb.skip_token(COLON)?;
        let result = self.run_in_local_proof_parsing_scope(|this| {
            let mut proof = Vec::with_capacity(tb.body.len());
            for block in tb.body.iter_mut() {
                proof.push(this.parse_stmt(block)?);
            }
            Ok(proof)
        });
        match result {
            Ok(proof) => Ok(SketchStmt::new(proof, tb.line_file.clone()).into()),
            Err(e) => Err(e),
        }
    }
}
