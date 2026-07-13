use crate::prelude::*;

impl Runtime {
    pub fn parse_by_antisymmetric_prop_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        tb.skip_token(ANTISYMMETRIC_PROP)?;
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by antisymmetric_prop: expected end of head after `:`".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        if tb.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by antisymmetric_prop: expects a body".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        let goal_block = tb.body.get_mut(0).ok_or_else(|| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by antisymmetric_prop: expected a `? forall ...` goal block".to_string(),
                    tb.line_file.clone(),
                ),
            ))
        })?;
        let forall_fact = self.parse_goal_forall_fact_block(goal_block, "by antisymmetric_prop")?;

        let shape_check =
            ByAntisymmetricPropStmt::new(forall_fact.clone(), Vec::new(), tb.line_file.clone())
                .antisymmetric_prop_name();
        if let Err(msg) = shape_check {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(msg, forall_fact.line_file.clone()),
            )));
        }

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

        Ok(ByAntisymmetricPropStmt::new(forall_fact, proof, tb.line_file.clone()).into())
    }
}
