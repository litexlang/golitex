use crate::prelude::*;

impl Runtime {
    pub fn parse_def_thm_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(THM)?;
        let name = tb.advance()?;
        is_valid_litex_name(&name).map_err(|msg| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone()),
            ))
        })?;
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "thm: expected `:` immediately after theorem name".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        if tb.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "thm: expects a `prove:` block and optional proof body".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        let forall_fact = {
            let prove_block = tb.body.get_mut(0).ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "thm: expected prove block".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            prove_block.skip_token_and_colon_and_exceed_end_of_head(PROVE)?;
            if prove_block.body.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "thm: `prove:` must contain exactly one forall fact".to_string(),
                        prove_block.line_file.clone(),
                    ),
                )));
            }
            let forall_block = prove_block.body.get_mut(0).ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "thm: missing forall block".to_string(),
                        prove_block.line_file.clone(),
                    ),
                ))
            })?;
            let fact = self.parse_fact(forall_block)?;
            match fact {
                Fact::ForallFact(forall_fact) => forall_fact,
                Fact::ForallFactWithIff(_) => {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "thm: forall with `<=>` is not allowed here".to_string(),
                            forall_block.line_file.clone(),
                        ),
                    )));
                }
                _ => {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "thm: `prove:` must be a single `forall` fact".to_string(),
                            forall_block.line_file.clone(),
                        ),
                    )));
                }
            }
        };

        let names = forall_fact.params_def_with_type.collect_param_names();
        let lf = tb.line_file.clone();
        let prove_process: Vec<Stmt> = self.parse_stmts_with_optional_free_param_scope(
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

        Ok(DefThmStmt::new(name, forall_fact, prove_process, tb.line_file.clone()).into())
    }
}
