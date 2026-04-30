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
        let fact = {
            let first = tb.body.get_mut(0).ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "claim: expects a `prove:` block and optional proof body".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;

            first.skip_token(PROVE)?;
            first.skip_token(COLON)?;

            let body_block = first.body.get_mut(0).ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "claim: `prove:` expects exactly one body block (the fact)".to_string(),
                        first.line_file.clone(),
                    ),
                ))
            })?;
            let f = self.parse_fact(body_block)?;
            if matches!(&f, Fact::ForallFactWithIff(_)) {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "claim multiline fact cannot be iff".to_string(),
                        first.line_file.clone(),
                    ),
                )));
            }
            Ok::<Fact, RuntimeError>(f)
        }?;

        let names = collect_forall_param_names_from_facts(std::slice::from_ref(&fact));
        let lf = tb.line_file.clone();
        let proof: Vec<Stmt> = self.parse_stmts_with_optional_free_param_scope(
            ParamObjType::Forall,
            &names,
            lf,
            |this| {
                tb.body
                    .iter_mut()
                    .skip(1)
                    .map(|b| this.parse_stmt(b))
                    .collect::<Result<_, _>>()
            },
        )?;
        Ok(ClaimStmt::new(fact, proof, tb.line_file.clone()))
    }
}
