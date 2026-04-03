use crate::prelude::*;
use std::collections::HashSet;

impl Runtime {
    pub fn parse_def_prop_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        self.push_parsing_time_name_scope();
        let stmt = self.parse_def_prop_stmt_body(tb);
        self.pop_parsing_time_name_scope();

        let stmt_ok = stmt?;
        self.validate_name_and_insert_into_top_parsing_time_name_scope(
            &stmt_ok.name,
            tb.line_file.clone(),
        )
        .map_err(|e| {
            RuntimeError::new_parse_error_wrapping_inner_with_outer_position_optional_outer_summary(
                e,
                tb.line_file.clone(),
                Some(
                    RuntimeError::message_text_for_duplicate_used_name_without_line_file(
                        &stmt_ok.name,
                    ),
                ),
            )
        })?;

        Ok(Stmt::DefPropStmt(stmt_ok))
    }

    fn parse_def_prop_stmt_body(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<DefPropStmt, RuntimeError> {
        tb.skip_token(PROP)?;
        let name = tb.advance()?;
        self.validate_name_and_insert_into_top_parsing_time_name_scope(&name, tb.line_file.clone())
            .map_err(|e| {
                RuntimeError::new_parse_error_wrapping_inner_with_outer_position_optional_outer_summary(
                    e,
                    tb.line_file.clone(),
                    Some(RuntimeError::message_text_for_duplicate_used_name_without_line_file(&name)),
                )
            })?;
        tb.skip_token(LEFT_BRACE)?;
        let mut param_defs: Vec<ParamDefWithParamType> = vec![];
        while tb.current()? != RIGHT_BRACE {
            param_defs.push(self.parse_param_def_with_param_type_and_skip_comma(tb)?);
        }
        tb.skip_token(RIGHT_BRACE)?;
        let all_param_names = ParamDefWithParamType::collect_param_names(&param_defs);
        self.validate_names_and_insert_into_top_parsing_time_name_scope(
            &all_param_names,
            tb.line_file.clone(),
        )
        .map_err(|e| {
            RuntimeError::new_parse_error_wrapping_inner_with_outer_position_optional_outer_summary(
                e,
                tb.line_file.clone(),
                None,
            )
        })?;

        if tb.current_token_is_equal_to(COLON) {
            tb.skip_token(COLON)?;
        } else {
            if !tb.exceed_end_of_head() {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "expect `:` or end of line after `)` in prop statement".to_string(),
                        tb.line_file.clone(),
                        None,
                    ),
                );
            } else {
                return Ok(DefPropStmt::new(
                    name,
                    param_defs,
                    vec![],
                    tb.line_file.clone(),
                ));
            }
        }

        let facts = self.parse_facts_in_body(tb)?;
        Ok(DefPropStmt::new(
            name,
            param_defs,
            facts,
            tb.line_file.clone(),
        ))
    }

    pub fn parse_def_abstract_prop_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        self.push_parsing_time_name_scope();
        let stmt = self.parse_def_abstract_prop_stmt_body(tb);
        self.pop_parsing_time_name_scope();

        let stmt_ok = stmt?;
        self.validate_name_and_insert_into_top_parsing_time_name_scope(
            &stmt_ok.name,
            tb.line_file.clone(),
        )
        .map_err(|e| {
            RuntimeError::new_parse_error_wrapping_inner_with_outer_position_optional_outer_summary(
                e,
                tb.line_file.clone(),
                Some(
                    RuntimeError::message_text_for_duplicate_used_name_without_line_file(
                        &stmt_ok.name,
                    ),
                ),
            )
        })?;
        Ok(Stmt::DefAbstractPropStmt(stmt_ok))
    }

    fn parse_def_abstract_prop_stmt_body(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<DefAbstractPropStmt, RuntimeError> {
        tb.skip_token(ABSTRACT_PROP)?;
        let name = tb.advance()?;
        self.validate_name_and_insert_into_top_parsing_time_name_scope(&name, tb.line_file.clone())
            .map_err(|e| {
                RuntimeError::new_parse_error_wrapping_inner_with_outer_position_optional_outer_summary(
                    e,
                    tb.line_file.clone(),
                    Some(RuntimeError::message_text_for_duplicate_used_name_without_line_file(&name)),
                )
            })?;
        tb.skip_token(LEFT_BRACE)?;
        let mut params = vec![];
        while tb.current()? != RIGHT_BRACE {
            params.push(tb.advance()?);
            if !tb.current_token_is_equal_to(RIGHT_BRACE) {
                tb.skip_token(COMMA)?;
            }
        }
        tb.skip_token(RIGHT_BRACE)?;

        self.validate_names_and_insert_into_top_parsing_time_name_scope(
            &params,
            tb.line_file.clone(),
        )
        .map_err(|e| {
            RuntimeError::new_parse_error_wrapping_inner_with_outer_position_optional_outer_summary(
                e,
                tb.line_file.clone(),
                None,
            )
        })?;

        Ok(DefAbstractPropStmt::new(name, params, tb.line_file.clone()))
    }

    pub fn parse_def_let_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(LET)?;
        let mut param_def: Vec<ParamDefWithParamType> = vec![];
        loop {
            match tb.current() {
                Ok(t) if t == COLON => break,
                Err(_) => break,
                Ok(_) => {}
            }
            param_def.push(self.parse_param_def_with_param_type_and_skip_comma(tb)?);
        }
        let facts = if tb.current_token_is_equal_to(COLON) {
            tb.skip_token(COLON)?;

            if !tb.exceed_end_of_head() {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "expect end of line after `:` in let statement".to_string(),
                        tb.line_file.clone(),
                        None,
                    ),
                );
            } else {
                self.parse_facts_in_body(tb)?
            }
        } else {
            vec![]
        };
        let all_param_names = ParamDefWithParamType::collect_param_names(&param_def);
        self.validate_names_and_insert_into_top_parsing_time_name_scope(
            &all_param_names,
            tb.line_file.clone(),
        )
        .map_err(|e| {
            RuntimeError::new_parse_error_wrapping_inner_with_outer_position_optional_outer_summary(
                e,
                tb.line_file.clone(),
                None,
            )
        })?;
        Ok(Stmt::DefLetStmt(DefLetStmt::new(
            param_def,
            facts,
            tb.line_file.clone(),
        )))
    }

    // return HaveObjInNonemptySetOrParamTypeStmt or HaveObjEqualStmt
    pub fn parse_have_obj_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(HAVE)?;
        let mut param_defs: Vec<ParamDefWithParamType> = vec![];
        loop {
            param_defs.push(self.parse_param_def_with_param_type_and_skip_comma(tb)?);
            match tb.current() {
                Ok(t) if t == EQUAL => break,
                Err(_) => break,
                Ok(_) => {}
            }
        }
        if param_defs.is_empty() {
            return Err(
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "have expects at least one param type pair".to_string(),
                    tb.line_file.clone(),
                    None,
                ),
            );
        }
        let have_param_names = ParamDefWithParamType::collect_param_names(&param_defs);
        self.validate_names_and_insert_into_top_parsing_time_name_scope(
            &have_param_names,
            tb.line_file.clone(),
        )
        .map_err(|e| {
            RuntimeError::new_parse_error_wrapping_inner_with_outer_position_optional_outer_summary(
                e,
                tb.line_file.clone(),
                None,
            )
        })?;

        if tb.current().map(|t| t != EQUAL).unwrap_or(true) {
            Ok(Stmt::HaveObjInNonemptySetStmt(
                HaveObjInNonemptySetOrParamTypeStmt::new(param_defs, tb.line_file.clone()),
            ))
        } else {
            tb.skip_token(EQUAL)?;
            let mut objs_equal_to = vec![self.parse_obj(tb)?];
            while matches!(tb.current(), Ok(t) if t == COMMA) {
                tb.skip_token(COMMA)?;
                objs_equal_to.push(self.parse_obj(tb)?);
            }
            Ok(Stmt::HaveObjEqualStmt(HaveObjEqualStmt::new(
                param_defs,
                objs_equal_to,
                tb.line_file.clone(),
            )))
        }
    }

    pub fn parse_have_fn_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(HAVE)?;
        tb.skip_token(FN_FOR_FN_WITH_PARAMS)?;
        let name = tb.advance()?;

        self.validate_name_and_insert_into_top_parsing_time_name_scope(&name, tb.line_file.clone())
            .map_err(|e| {
                RuntimeError::new_parse_error_wrapping_inner_with_outer_position_optional_outer_summary(
                    e,
                    tb.line_file.clone(),
                    Some(RuntimeError::message_text_for_duplicate_used_name_without_line_file(&name)),
                )
            })?;

        let fs = self.parse_fn_set_with_dom_without_fn_prefix(tb)?;
        tb.skip_token(EQUAL)?;
        if tb.current_token_is_equal_to(COLON) {
            tb.skip_token(COLON)?;
            let case_block_count = tb.body.len();
            let mut cases: Vec<AndChainAtomicFact> = Vec::with_capacity(case_block_count);
            let mut equal_tos: Vec<crate::obj::Obj> = Vec::with_capacity(case_block_count);
            for block in tb.body.iter_mut() {
                block.skip_token(CASE)?;
                cases.push(self.parse_and_chain_atomic_fact(block)?);
                block.skip_token(COLON)?;
                equal_tos.push(self.parse_obj(block)?);
            }
            Ok(Stmt::HaveFnEqualCaseByCaseStmt(
                HaveFnEqualCaseByCaseStmt::new(name, fs, cases, equal_tos, tb.line_file.clone()),
            ))
        } else {
            let equal_to = self.parse_obj(tb)?;
            Ok(Stmt::HaveFnEqualStmt(HaveFnEqualStmt::new(
                name,
                fs,
                equal_to,
                tb.line_file.clone(),
            )))
        }
    }

    pub fn parse_have_exist(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(HAVE)?;
        tb.skip_token(BY)?;

        let true_fact = self.parse_exist_fact(tb)?;

        tb.skip_token(COLON)?;

        let mut equal_tos = vec![];
        while !tb.exceed_end_of_head() {
            equal_tos.push(tb.advance()?);
            if tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
            }
        }

        self.validate_names_and_insert_into_top_parsing_time_name_scope(
            &equal_tos,
            tb.line_file.clone(),
        )
        .map_err(|e| {
            RuntimeError::new_parse_error_wrapping_inner_with_outer_position_optional_outer_summary(
                e,
                tb.line_file.clone(),
                None,
            )
        })?;

        Ok(Stmt::HaveExistObjStmt(HaveExistObjStmt::new(
            equal_tos,
            true_fact,
            tb.line_file.clone(),
        )))
    }

    fn parse_braced_params_and_optional_dom_facts(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<(Vec<ParamDefWithParamType>, Vec<OrAndChainAtomicFact>), RuntimeError> {
        tb.skip_token(LEFT_BRACE)?;
        let mut params_def_with_type: Vec<ParamDefWithParamType> = vec![];
        while tb.current()? != COLON && tb.current()? != RIGHT_BRACE {
            params_def_with_type.push(self.parse_param_def_with_param_type_and_skip_comma(tb)?);
        }
        let param_names = ParamDefWithParamType::collect_param_names(&params_def_with_type);
        self.validate_names_and_insert_into_top_parsing_time_name_scope(
            &param_names,
            tb.line_file.clone(),
        )
        .map_err(|e| {
            RuntimeError::new_parse_error_wrapping_inner_with_outer_position_optional_outer_summary(
                e,
                tb.line_file.clone(),
                None,
            )
        })?;
        let dom_facts = if tb.current_token_is_equal_to(COLON) {
            tb.skip_token(COLON)?;
            let mut facts = vec![];
            while tb.current()? != RIGHT_BRACE {
                facts.push(self.parse_or_and_chain_atomic_fact(tb)?);
                if tb.current_token_is_equal_to(COMMA) {
                    tb.skip_token(COMMA)?;
                }
            }
            facts
        } else {
            vec![]
        };
        tb.skip_token(RIGHT_BRACE)?;
        Ok((params_def_with_type, dom_facts))
    }

    fn parse_braced_struct_field_params_and_optional_dom_facts(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<(Vec<ParamDefWithStructFieldType>, Vec<OrAndChainAtomicFact>), RuntimeError> {
        tb.skip_token(LEFT_BRACE)?;
        let mut param_defs: Vec<ParamDefWithStructFieldType> = vec![];
        while tb.current()? != COLON && tb.current()? != RIGHT_BRACE {
            param_defs.push(self.parse_param_def_with_struct_field_type_and_skip_comma(tb)?);
        }
        let param_names = ParamDefWithStructFieldType::collect_param_names(&param_defs);
        self.validate_names_and_insert_into_top_parsing_time_name_scope(
            &param_names,
            tb.line_file.clone(),
        )
        .map_err(|e| {
            RuntimeError::new_parse_error_wrapping_inner_with_outer_position_optional_outer_summary(
                e,
                tb.line_file.clone(),
                None,
            )
        })?;
        let dom_facts = if tb.current_token_is_equal_to(COLON) {
            tb.skip_token(COLON)?;
            let mut facts = vec![];
            while tb.current()? != RIGHT_BRACE {
                facts.push(self.parse_or_and_chain_atomic_fact(tb)?);
                if tb.current_token_is_equal_to(COMMA) {
                    tb.skip_token(COMMA)?;
                }
            }
            facts
        } else {
            vec![]
        };
        tb.skip_token(RIGHT_BRACE)?;
        Ok((param_defs, dom_facts))
    }

    pub fn parse_def_family_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(FAMILY)?;
        let name = tb.advance()?;
        self.validate_name_and_insert_into_top_parsing_time_name_scope(&name, tb.line_file.clone())
            .map_err(|e| {
                RuntimeError::new_parse_error_wrapping_inner_with_outer_position_optional_outer_summary(
                    e,
                    tb.line_file.clone(),
                    Some(RuntimeError::message_text_for_duplicate_used_name_without_line_file(&name)),
                )
            })?;

        self.push_parsing_time_name_scope();
        let stmt = self.parse_def_family_stmt_body(name, tb);
        self.pop_parsing_time_name_scope();
        stmt
    }

    fn parse_def_family_stmt_body(
        &mut self,
        name: String,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        let (params_def_with_type, dom_facts) =
            self.parse_braced_params_and_optional_dom_facts(tb)?;
        if !tb.current_token_is_equal_to(EQUAL) {
            return Err(
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "family definition expects `=` after `}`".to_string(),
                    tb.line_file.clone(),
                    None,
                ),
            );
        }
        tb.skip_token(EQUAL)?;
        let equal_to = self.parse_obj(tb)?;
        Ok(Stmt::DefFamilyStmt(DefFamilyStmt::new(
            name,
            params_def_with_type,
            dom_facts,
            equal_to,
            tb.line_file.clone(),
        )))
    }

    pub fn parse_def_param_type_struct_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        tb.skip_token(STRUCT)?;
        let name = tb.advance()?;
        self.validate_name_and_insert_into_top_parsing_time_name_scope(&name, tb.line_file.clone())
            .map_err(|e| {
                RuntimeError::new_parse_error_wrapping_inner_with_outer_position_optional_outer_summary(
                    e,
                    tb.line_file.clone(),
                    Some(RuntimeError::message_text_for_duplicate_used_name_without_line_file(&name)),
                )
            })?;

        self.push_parsing_time_name_scope();
        let stmt = self.parse_def_param_type_struct_stmt_body(name, tb);
        self.pop_parsing_time_name_scope();
        stmt
    }

    fn parse_def_param_type_struct_stmt_body(
        &mut self,
        name: String,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        let (param_defs, dom_facts) =
            self.parse_braced_struct_field_params_and_optional_dom_facts(tb)?;
        if tb.current_token_is_equal_to(EQUAL) {
            return Err(RuntimeError::new_parse_error_with_msg_position_previous_error(
                "use `family` for set-style definitions (`... {} = ...`); `struct` requires field definitions after `:`"
                    .to_string(),
                tb.line_file.clone(),
                None,
            ));
        }
        tb.skip_token(COLON)?;

        if tb.body.is_empty() {
            return Err(
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "struct with fields expects body".to_string(),
                    tb.line_file.clone(),
                    None,
                ),
            );
        }

        let mut fields: Vec<(String, StructFieldType)> = vec![];
        let mut facts: Vec<OrAndChainAtomicFact> = vec![];

        let body_len = tb.body.len();
        let last_index = body_len - 1;
        let last_is_equiv = {
            let last = tb.body.get(last_index).ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "Expected body".to_string(),
                    tb.line_file.clone(),
                    None,
                )
            })?;
            last.current_token_is_equal_to(EQUIVALENT_SIGN)
        };

        let field_end = if last_is_equiv { last_index } else { body_len };

        for i in 0..field_end {
            let block = tb.body.get_mut(i).ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "Expected field block".to_string(),
                    tb.line_file.clone(),
                    None,
                )
            })?;
            let field_name = block.advance()?;
            let cond = self.parse_struct_field_type(block)?;
            fields.push((field_name, cond));
        }

        if last_is_equiv {
            let last = tb.body.get_mut(last_index).ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "Expected <=>: block".to_string(),
                    tb.line_file.clone(),
                    None,
                )
            })?;
            last.skip_token_and_colon_and_exceed_end_of_head(EQUIVALENT_SIGN)?;
            for block in last.body.iter_mut() {
                facts.push(self.parse_or_and_chain_atomic_fact(block)?);
            }
        }

        let mut seen = HashSet::new();
        for (field_name, _) in fields.iter() {
            if !seen.insert(field_name.clone()) {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        format!("struct `{}`: duplicate field `{}`", name, field_name),
                        tb.line_file.clone(),
                        None,
                    ),
                );
            }
        }

        Ok(Stmt::DefParamTypeStructStmt(DefParamTypeStructStmt::new(
            name,
            param_defs,
            dom_facts,
            fields,
            facts,
            tb.line_file.clone(),
        )))
    }

    pub fn parse_def_algorithm_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(ALGO)?;
        let name = tb.advance()?;
        self.push_parsing_time_name_scope();
        let stmt = self.parse_def_algorithm_stmt_body(name, tb);
        self.pop_parsing_time_name_scope();
        stmt
    }

    fn parse_def_algorithm_stmt_body(
        &mut self,
        name: String,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        tb.skip_token(LEFT_BRACE)?;
        let mut params: Vec<String> = vec![];
        while tb.current()? != RIGHT_BRACE {
            params.push(tb.advance()?);
            if tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
            }
        }
        tb.skip_token(RIGHT_BRACE)?;
        tb.skip_token(COLON)?;
        let mut algo_cases: Vec<AlgoCase> = vec![];
        let mut default_return: Option<AlgoReturn> = None;
        match tb.body.split_last_mut() {
            None => {}
            Some((last_block, leading_blocks)) => {
                for block in leading_blocks.iter_mut() {
                    algo_cases.push(self.parse_algo_case(block)?);
                }
                if last_block.current_token_empty_if_exceed_end_of_head() == CASE {
                    algo_cases.push(self.parse_algo_case(last_block)?);
                } else {
                    default_return = Some(self.parse_algo_return(last_block)?);
                }
            }
        }
        Ok(Stmt::DefAlgoStmt(DefAlgoStmt::new(
            name,
            params,
            algo_cases,
            default_return,
            tb.line_file.clone(),
        )))
    }

    /// head 里是 if and_spec_fact :，body 有且只有一个块，即 return obj。
    fn parse_algo_case(&mut self, block: &mut TokenBlock) -> Result<AlgoCase, RuntimeError> {
        block.skip_token(CASE)?;
        let condition = self.parse_atomic_fact(block, true)?;
        block.skip_token(COLON)?;

        let return_stmt = self.parse_algo_return(block)?;
        Ok(AlgoCase::new(
            condition,
            return_stmt,
            block.line_file.clone(),
        ))
    }

    /// head 里是 return，后跟 obj。
    fn parse_algo_return(&mut self, block: &mut TokenBlock) -> Result<AlgoReturn, RuntimeError> {
        let value = self.parse_obj(block)?;
        Ok(AlgoReturn::new(value, block.line_file.clone()))
    }
}
