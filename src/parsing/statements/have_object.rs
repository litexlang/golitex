//! Ordinary object `have` definitions (`have x S`, `have x S = …`, `have …:`).

use crate::prelude::*;

impl Runtime {
    pub fn parse_have_obj_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(HAVE)?;
        let has_fact_body = self.have_obj_stmt_has_fact_body(tb)?;
        let binding_kind = if has_fact_body {
            BindingScope::LocalBinder
        } else {
            BindingScope::DefinitionBinding
        };
        let param_defs = self.parse_have_obj_param_defs_until_header_delimiter(tb, binding_kind)?;
        if param_defs.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "have expects at least one param type pair".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        let param_defs = TypedParameterList::new(param_defs);
        let have_param_names = param_defs.collect_param_names();

        if has_fact_body {
            let facts_result = (|| -> Result<Vec<QuantifierFreeFact>, RuntimeError> {
                tb.skip_token(COLON)?;
                if !tb.exceed_end_of_head() {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "`have ...:` facts must be written in an indented body".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                self.parse_quantifier_free_facts_in_body(tb)
            })();
            if !have_param_names.is_empty() {
                self.end_parsing_scope(&have_param_names);
            }
            let facts = facts_result?;
            self.register_collected_param_names_for_def_parse(
                &have_param_names,
                tb.line_file.clone(),
            )?;
            self.register_local_existing_identifier_bindings_for_parse(
                &param_defs.collect_param_bindings(),
                tb.line_file.clone(),
            )?;
            return Ok(
                HaveObjByExistFactsStmt::new(param_defs, facts, tb.line_file.clone()).into(),
            );
        }

        let register_result = self
            .register_collected_param_names_for_def_parse(&have_param_names, tb.line_file.clone());
        if register_result.is_err() && !have_param_names.is_empty() {
            self.end_parsing_scope(&have_param_names);
        }
        register_result?;

        if tb.current().map(|t| t != EQUAL).unwrap_or(true) {
            if !have_param_names.is_empty() {
                self.end_parsing_scope(&have_param_names);
            }
            self.register_local_existing_identifier_bindings_for_parse(
                &param_defs.collect_param_bindings(),
                tb.line_file.clone(),
            )?;
            Ok(HaveObjInNonemptySetOrParamTypeStmt::new(param_defs, tb.line_file.clone()).into())
        } else {
            tb.skip_token(EQUAL)?;
            let objs_result = (|| -> Result<Vec<Obj>, RuntimeError> {
                let mut objs_equal_to = vec![self.parse_obj(tb)?];
                while matches!(tb.current(), Ok(t) if t == COMMA) {
                    tb.skip_token(COMMA)?;
                    objs_equal_to.push(self.parse_obj(tb)?);
                }
                Ok(objs_equal_to)
            })();
            self.end_parsing_scope(&have_param_names);
            let objs_equal_to = objs_result?;
            self.register_local_existing_identifier_bindings_for_parse(
                &param_defs.collect_param_bindings(),
                tb.line_file.clone(),
            )?;
            Ok(HaveObjEqualStmt::new(param_defs, objs_equal_to, tb.line_file.clone()).into())
        }
    }

    fn have_obj_stmt_has_fact_body(&mut self, tb: &TokenBlock) -> Result<bool, RuntimeError> {
        let mut dry_tb = tb.clone();
        self.run_in_local_parsing_time_name_scope(|this| {
            let param_defs = this.parse_have_obj_param_defs_until_header_delimiter(
                &mut dry_tb,
                BindingScope::DefinitionBinding,
            )?;
            if param_defs.is_empty() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "have expects at least one param type pair".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            Ok(dry_tb.current_token_is_equal_to(COLON))
        })
    }

    fn parse_have_obj_param_defs_until_header_delimiter(
        &mut self,
        tb: &mut TokenBlock,
        binding_scope: BindingScope,
    ) -> Result<Vec<TypedParameterGroup>, RuntimeError> {
        let mut param_defs: Vec<TypedParameterGroup> = vec![];
        loop {
            match tb.current() {
                Ok(t) if t == EQUAL || t == COLON => break,
                Err(_) => break,
                Ok(_) => {}
            }
            param_defs
                .push(self.parse_param_def_with_param_type_and_skip_comma(tb, binding_scope)?);
        }
        Ok(param_defs)
    }
}

