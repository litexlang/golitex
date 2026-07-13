use crate::prelude::*;

impl Runtime {
    pub fn parse_by_for_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(FOR)?;
        if tb.current()? != COLON {
            let (fact, has_proof_body) = self.parse_header_fact_with_optional_trailing_colon(
                tb,
                "by for",
                "by for => <forall fact>:",
                "by for <forall fact>:",
            )?;
            let forall_fact = match fact {
                Fact::ForallFact(ff) => ff,
                Fact::ForallFactWithIff(_) => {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "by for: forall with `<=>` is not allowed here".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                _ => {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "by for: header shorthand must be a single `forall` fact".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
            };

            ByForStmt::new(forall_fact.clone(), vec![], forall_fact.line_file.clone())
                .expansion()
                .map_err(|msg| {
                    RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            msg,
                            forall_fact.line_file.clone(),
                        ),
                    ))
                })?;

            let names = forall_fact.params_def_with_type.collect_param_names();
            let lf = tb.line_file.clone();
            let proof: Vec<Stmt> = if has_proof_body {
                self.parse_stmts_with_optional_free_param_scope(
                    ParamObjType::Forall,
                    &names,
                    lf,
                    |this| {
                        tb.body
                            .iter_mut()
                            .map(|b| this.parse_stmt(b))
                            .collect::<Result<_, _>>()
                    },
                )?
            } else {
                vec![]
            };

            return Ok(ByForStmt::new(forall_fact, proof, tb.line_file.clone()).into());
        }
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by for: expected `:` immediately after `for`".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        if tb.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by for: expects a body".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        let goal_block = tb.body.get_mut(0).ok_or_else(|| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by for: expected a `? forall ...` goal block".to_string(),
                    tb.line_file.clone(),
                ),
            ))
        })?;
        let forall_fact = self.parse_goal_forall_fact_block(goal_block, "by for")?;

        ByForStmt::new(forall_fact.clone(), vec![], forall_fact.line_file.clone())
            .expansion()
            .map_err(|msg| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        msg,
                        forall_fact.line_file.clone(),
                    ),
                ))
            })?;

        let names = forall_fact.params_def_with_type.collect_param_names();
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

        Ok(ByForStmt::new(forall_fact, proof, tb.line_file.clone()).into())
    }
}
