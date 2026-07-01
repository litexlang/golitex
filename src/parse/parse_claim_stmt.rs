use crate::parse::parse_helpers::collect_forall_param_names_from_facts;
use crate::prelude::*;

impl Runtime {
    pub fn parse_claim_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(CLAIM)?;
        if tb.current()? == COLON {
            Ok(self.parse_multiline_fact_claim(tb)?.into())
        } else {
            let fact = self.parse_header_fact_before_trailing_colon(
                tb,
                "claim",
                "claim => <fact>:",
                "claim <fact>:",
            )?;
            if matches!(&fact, Fact::ForallFactWithIff(_)) {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "claim multiline fact cannot be iff".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let names = collect_forall_param_names_from_facts(std::slice::from_ref(&fact));
            let lf = tb.line_file.clone();
            let proof: Vec<Stmt> = self.parse_stmts_with_optional_free_param_scope(
                ParamObjType::Forall,
                &names,
                lf,
                |this| {
                    tb.body
                        .iter_mut()
                        .map(|b| this.parse_stmt(b))
                        .collect::<Result<_, _>>()
                },
            )?;
            Ok(ClaimStmt::new(fact, proof, tb.line_file.clone()).into())
        }
    }

    fn parse_multiline_fact_claim(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<ClaimStmt, RuntimeError> {
        tb.skip_token(COLON)?;
        if tb.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "claim: expects a `prove:` block and optional proof body".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        let (fact, inline_proof_start) = {
            let first = tb.body.get_mut(0).ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "claim: expects a `prove:` block and optional proof body".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;

            let (f, inline_proof_start) =
                self.parse_goal_fact_block_with_inline_proof(first, "claim")?;
            if matches!(&f, Fact::ForallFactWithIff(_)) {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "claim multiline fact cannot be iff".to_string(),
                        first.line_file.clone(),
                    ),
                )));
            }
            Ok::<(Fact, usize), RuntimeError>((f, inline_proof_start))
        }?;

        let names = collect_forall_param_names_from_facts(std::slice::from_ref(&fact));
        let lf = tb.line_file.clone();
        let proof: Vec<Stmt> = self.parse_stmts_with_optional_free_param_scope(
            ParamObjType::Forall,
            &names,
            lf,
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
        Ok(ClaimStmt::new(fact, proof, tb.line_file.clone()))
    }
}
