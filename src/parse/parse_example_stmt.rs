use crate::parse::parse_helpers::collect_forall_param_bindings_from_facts;
use crate::prelude::*;

impl Runtime {
    pub fn parse_example_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(EXAMPLE)?;
        if tb.current()? != COLON {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "example requires `example:` followed by an indented `? <fact>` goal"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        tb.skip_token(COLON)?;
        if tb.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "example: expects a `? <fact>` goal block and optional proof body".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        let (fact, inline_proof_start) = {
            let first = tb.body.get_mut(0).ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "example: expects a `? <fact>` goal block and optional proof body"
                            .to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            let (fact, inline_proof_start) =
                self.parse_goal_fact_block_with_inline_proof(first, "example")?;
            if matches!(&fact, Fact::ForallFactWithIff(_)) {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "example multiline fact cannot be iff".to_string(),
                        first.line_file.clone(),
                    ),
                )));
            }
            Ok::<(Fact, usize), RuntimeError>((fact, inline_proof_start))
        }?;

        let bindings = collect_forall_param_bindings_from_facts(std::slice::from_ref(&fact));
        let line_file = tb.line_file.clone();
        let proof = self.parse_stmts_with_existing_free_param_bindings(
            ParamObjType::Forall,
            &bindings,
            line_file,
            |this| {
                let mut proof = Vec::new();
                if inline_proof_start > 0 {
                    if let Some(first) = tb.body.get_mut(0) {
                        for block in first.body.iter_mut().skip(inline_proof_start) {
                            proof.push(this.parse_stmt(block)?);
                        }
                    }
                }
                for block in tb.body.iter_mut().skip(1) {
                    proof.push(this.parse_stmt(block)?);
                }
                Ok(proof)
            },
        )?;
        Ok(ExampleStmt::new(fact, proof, tb.line_file.clone()).into())
    }
}
