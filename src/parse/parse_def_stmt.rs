use crate::prelude::*;

impl Runtime {
    pub fn parse_def_template_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(TEMPLATE)?;
        let template_name = tb.advance()?;
        is_valid_litex_name(&template_name).map_err(|msg| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone()),
            ))
        })?;

        let stmt_result = self.run_in_local_parsing_time_name_scope(|this| {
            tb.skip_token(LESS)?;
            let close_index = tb
                .header
                .iter()
                .enumerate()
                .skip(tb.parse_index)
                .rev()
                .find(|(_, token)| token.as_str() == GREATER)
                .map(|(index, _)| index)
                .ok_or_else(|| {
                    RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "template header expects `>`".to_string(),
                            tb.line_file.clone(),
                        ),
                    ))
                })?;
            let mut header_block = TokenBlock::new(
                tb.header[tb.parse_index..close_index].to_vec(),
                Vec::new(),
                tb.line_file.clone(),
            );
            let mut groups: Vec<ParamGroupWithParamType> = Vec::new();
            loop {
                if header_block.current_token_is_equal_to(COLON)
                    || header_block.exceed_end_of_head()
                {
                    break;
                }
                groups.push(this.parse_param_def_with_param_type_and_skip_comma(
                    &mut header_block,
                    ParamObjType::DefHeader,
                )?);
            }
            let template_arg_def = ParamDefWithType::new(groups);
            let template_arg_names = template_arg_def.collect_param_names();

            let mut template_arg_dom = Vec::new();
            if header_block.current_token_is_equal_to(COLON) {
                header_block.skip_token(COLON)?;
                loop {
                    template_arg_dom.push(this.parse_or_and_chain_atomic_fact(&mut header_block)?);
                    if header_block.current_token_is_equal_to(COMMA) {
                        header_block.skip_token(COMMA)?;
                    } else {
                        break;
                    }
                }
            }
            if !header_block.exceed_end_of_head() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "unexpected token in template header".to_string(),
                        header_block.line_file.clone(),
                    ),
                )));
            }
            tb.parse_index = close_index + 1;
            tb.skip_token(COLON)?;
            if !tb.exceed_end_of_head() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "unexpected token after template header".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            if tb.body.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "template definition expects exactly one body statement".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }

            let template_def_stmt = this.parse_template_body_stmt(&mut tb.body[0])?;
            match template_def_stmt.defined_name() {
                Some(name) if name == template_name => {}
                Some(name) => {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            format!(
                                "template body defines `{}`, but template name is `{}`",
                                name, template_name
                            ),
                            tb.body[0].line_file.clone(),
                        ),
                    )));
                }
                None => {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "template body must define exactly one object or function".to_string(),
                            tb.body[0].line_file.clone(),
                        ),
                    )));
                }
            }

            this.parsing_free_param_collection
                .end_scope(ParamObjType::DefHeader, &template_arg_names);

            Ok(DefTemplateStmt::new(
                template_name.clone(),
                template_arg_def,
                template_arg_dom,
                template_def_stmt,
                tb.line_file.clone(),
            ))
        });

        let stmt = stmt_result?;
        self.insert_parsed_name_into_top_parsing_time_name_scope(
            &stmt.template_name,
            tb.line_file.clone(),
        )?;
        Ok(stmt.into())
    }

    pub fn parse_def_struct_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(STRUCT)?;
        let name = tb.advance()?;
        is_valid_litex_name(&name).map_err(|msg| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone()),
            ))
        })?;

        let stmt_result = self.run_in_local_parsing_time_name_scope(|this| {
            let param_def_with_dom = if tb.current_token_is_equal_to(LEFT_BRACE) {
                let param_def = this.parse_def_braced_param_groups_with_param_type(tb)?;
                Some((param_def, Vec::new()))
            } else {
                None
            };
            let struct_param_names = param_def_with_dom
                .as_ref()
                .map(|(param_def, _)| param_def.collect_param_names())
                .unwrap_or_else(Vec::new);

            let parse_result = (|| -> Result<DefStructStmt, RuntimeError> {
                tb.skip_token(COLON)?;
                if tb.body.is_empty() {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "struct definition expects at least two fields".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }

                let mut fields: Vec<(String, Obj)> = Vec::new();
                let mut equivalent_facts: Vec<Fact> = Vec::new();
                let mut seen_equivalent = false;

                for block in tb.body.iter_mut() {
                    if block.current()? == EQUIVALENT_SIGN {
                        if seen_equivalent {
                            return Err(RuntimeError::from(ParseRuntimeError(
                                RuntimeErrorStruct::new_with_msg_and_line_file(
                                    "struct definition can only have one `<=>:` block".to_string(),
                                    block.line_file.clone(),
                                ),
                            )));
                        }
                        seen_equivalent = true;
                        equivalent_facts = this.parse_struct_equivalent_facts(block, &fields)?;
                    } else {
                        if seen_equivalent {
                            return Err(RuntimeError::from(ParseRuntimeError(
                                RuntimeErrorStruct::new_with_msg_and_line_file(
                                    "struct fields must appear before `<=>:`".to_string(),
                                    block.line_file.clone(),
                                ),
                            )));
                        }
                        let field = this.parse_struct_field(block)?;
                        if fields.iter().any(|(name, _)| name == &field.0) {
                            return Err(RuntimeError::from(ParseRuntimeError(
                                RuntimeErrorStruct::new_with_msg_and_line_file(
                                    format!("duplicate struct field `{}`", field.0),
                                    block.line_file.clone(),
                                ),
                            )));
                        }
                        fields.push(field);
                    }
                }

                if fields.len() < 2 {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "struct definition expects at least two fields".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }

                Ok(DefStructStmt::new(
                    name.clone(),
                    param_def_with_dom,
                    fields,
                    equivalent_facts,
                    tb.line_file.clone(),
                ))
            })();

            if !struct_param_names.is_empty() {
                this.parsing_free_param_collection
                    .end_scope(ParamObjType::DefHeader, &struct_param_names);
            }
            parse_result
        });

        let stmt = stmt_result?;
        self.insert_parsed_name_into_top_parsing_time_name_scope(&stmt.name, tb.line_file.clone())?;
        Ok(stmt.into())
    }

    fn parse_struct_field(
        &mut self,
        block: &mut TokenBlock,
    ) -> Result<(String, Obj), RuntimeError> {
        if !block.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "struct field must fit on one line".to_string(),
                    block.line_file.clone(),
                ),
            )));
        }

        let field_name = block.advance()?;
        is_valid_litex_name(&field_name).map_err(|msg| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(msg, block.line_file.clone()),
            ))
        })?;

        let field_type = self.parse_obj(block)?;
        if !block.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "unexpected token after struct field type".to_string(),
                    block.line_file.clone(),
                ),
            )));
        }
        Ok((field_name, field_type))
    }

    fn parse_struct_equivalent_facts(
        &mut self,
        block: &mut TokenBlock,
        fields: &Vec<(String, Obj)>,
    ) -> Result<Vec<Fact>, RuntimeError> {
        block.skip_token(EQUIVALENT_SIGN)?;
        block.skip_token(COLON)?;
        if !block.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "`<=>:` in struct definition must not have inline facts".to_string(),
                    block.line_file.clone(),
                ),
            )));
        }
        let field_names = fields
            .iter()
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>();
        self.parsing_free_param_collection.begin_scope(
            ParamObjType::DefStructField,
            &field_names,
            block.line_file.clone(),
        )?;
        let facts_result = self.parse_facts_in_body(block);
        self.parsing_free_param_collection
            .end_scope(ParamObjType::DefStructField, &field_names);
        facts_result
    }

    pub fn parse_def_prop_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        let stmt = self.run_in_local_parsing_time_name_scope(|this| {
            tb.skip_token(PROP)?;
            let name = this.parse_name_and_insert_into_top_parsing_time_name_scope(tb)?;
            let param_defs = this.parse_def_braced_param_groups_with_param_type(tb)?;
            let def_param_names = param_defs.collect_param_names();

            if tb.current_token_is_equal_to(COLON) {
                tb.skip_token(COLON)?;
            } else {
                if !tb.exceed_end_of_head() {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "expect `:` or end of line after `)` in prop statement".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                } else {
                    this.parsing_free_param_collection
                        .end_scope(ParamObjType::DefHeader, &def_param_names);
                    return Ok(DefPropStmt::new(
                        name,
                        param_defs,
                        vec![],
                        tb.line_file.clone(),
                    ));
                }
            }

            let facts_result = this.parse_facts_in_body(tb);
            this.parsing_free_param_collection
                .end_scope(ParamObjType::DefHeader, &def_param_names);
            let facts = facts_result?;
            Ok(DefPropStmt::new(
                name,
                param_defs,
                facts,
                tb.line_file.clone(),
            ))
        });

        let stmt_ok = stmt?;
        self.insert_parsed_name_into_top_parsing_time_name_scope(
            &stmt_ok.name,
            tb.line_file.clone(),
        )?;

        Ok(stmt_ok.into())
    }

    pub fn parse_def_abstract_prop_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        let stmt: Result<DefAbstractPropStmt, RuntimeError> = self
            .run_in_local_parsing_time_name_scope(|this| {
                tb.skip_token(ABSTRACT_PROP)?;
                let name = this.parse_name_and_insert_into_top_parsing_time_name_scope(tb)?;
                tb.skip_token(LEFT_BRACE)?;
                let mut params = vec![];
                while tb.current()? != RIGHT_BRACE {
                    params.push(tb.advance()?);
                    if !tb.current_token_is_equal_to(RIGHT_BRACE) {
                        tb.skip_token(COMMA)?;
                    }
                }
                tb.skip_token(RIGHT_BRACE)?;

                this.register_collected_param_names_for_def_parse(&params, tb.line_file.clone())?;

                Ok(DefAbstractPropStmt::new(name, params, tb.line_file.clone()))
            });

        let stmt_ok = stmt?;
        self.insert_parsed_name_into_top_parsing_time_name_scope(
            &stmt_ok.name,
            tb.line_file.clone(),
        )?;
        Ok(stmt_ok.into())
    }

    pub fn parse_def_let_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(LET)?;
        let mut param_def: Vec<ParamGroupWithParamType> = vec![];
        loop {
            match tb.current() {
                Ok(t) if t == COLON => break,
                Err(_) => break,
                Ok(_) => {}
            }
            param_def.push(
                self.parse_param_def_with_param_type_and_skip_comma(tb, ParamObjType::Identifier)?,
            );
        }
        let param_def = ParamDefWithType::new(param_def);
        let all_param_names = param_def.collect_param_names();
        self.register_collected_param_names_for_def_parse(&all_param_names, tb.line_file.clone())?;

        let facts = if tb.current_token_is_equal_to(COLON) {
            tb.skip_token(COLON)?;

            let facts_result: Result<Vec<Fact>, RuntimeError> = if tb.exceed_end_of_head() {
                self.parse_facts_in_body(tb)
            } else {
                let mut facts = Vec::new();
                let parse_result = (|| {
                    loop {
                        facts.push(self.parse_fact(tb)?);
                        if tb.exceed_end_of_head() {
                            break;
                        }
                        tb.skip_token(COMMA)?;
                        if tb.exceed_end_of_head() {
                            return Err(RuntimeError::from(ParseRuntimeError(
                                RuntimeErrorStruct::new_with_msg_and_line_file(
                                    "expected fact after comma in inline let statement".to_string(),
                                    tb.line_file.clone(),
                                ),
                            )));
                        }
                    }
                    if !tb.body.is_empty() {
                        return Err(RuntimeError::from(ParseRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_line_file(
                                "inline let statement cannot also have an indented body"
                                    .to_string(),
                                tb.line_file.clone(),
                            ),
                        )));
                    }
                    Ok(())
                })();
                parse_result.map(|_| facts)
            };
            if facts_result.is_err() && !all_param_names.is_empty() {
                self.parsing_free_param_collection
                    .end_scope(ParamObjType::Identifier, &all_param_names);
            }
            let facts = facts_result?;
            self.parsing_free_param_collection
                .end_scope(ParamObjType::Identifier, &all_param_names);
            facts
        } else {
            if !all_param_names.is_empty() {
                self.parsing_free_param_collection
                    .end_scope(ParamObjType::Identifier, &all_param_names);
            }
            vec![]
        };
        Ok(DefLetStmt::new(param_def, facts, tb.line_file.clone()).into())
    }

    // return HaveObjInNonemptySetOrParamTypeStmt or HaveObjEqualStmt
    pub fn parse_have_obj_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(HAVE)?;
        let mut param_defs: Vec<ParamGroupWithParamType> = vec![];
        loop {
            param_defs.push(
                self.parse_param_def_with_param_type_and_skip_comma(tb, ParamObjType::Identifier)?,
            );
            match tb.current() {
                Ok(t) if t == EQUAL => break,
                Err(_) => break,
                Ok(_) => {}
            }
        }
        if param_defs.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "have expects at least one param type pair".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        let param_defs = ParamDefWithType::new(param_defs);
        let have_param_names = param_defs.collect_param_names();
        self.register_collected_param_names_for_def_parse(&have_param_names, tb.line_file.clone())?;

        if tb.current().map(|t| t != EQUAL).unwrap_or(true) {
            if !have_param_names.is_empty() {
                self.parsing_free_param_collection
                    .end_scope(ParamObjType::Identifier, &have_param_names);
            }
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
            self.parsing_free_param_collection
                .end_scope(ParamObjType::Identifier, &have_param_names);
            let objs_equal_to = objs_result?;
            Ok(HaveObjEqualStmt::new(param_defs, objs_equal_to, tb.line_file.clone()).into())
        }
    }

    pub fn parse_have_fn_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(HAVE)?;
        tb.skip_token(FN_LOWER_CASE)?;
        let as_algo = if tb.current_token_is_equal_to(AS) && tb.token_at_add_index(1) == ALGO {
            tb.skip_token(AS)?;
            tb.skip_token(ALGO)?;
            true
        } else {
            false
        };
        if tb.current_token_is_equal_to(BY) {
            Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "`have fn by induc from ...` has been replaced by `have fn f(...) R by induc ... from ...:`"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            )))
        } else {
            let name = self.parse_name_and_insert_into_top_parsing_time_name_scope(tb)?;
            if tb.current_token_is_equal_to(AS) {
                if as_algo {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "`have fn as algo` does not support `as set` function definitions"
                                .to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                tb.skip_token(AS)?;
                tb.skip_token(SET)?;
                tb.skip_token(COLON)?;
                let lf = tb.line_file.clone();
                if tb.body.len() != 1 {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "`have fn <name> as set:` expects exactly one `forall` fact"
                                .to_string(),
                            lf,
                        ),
                    )));
                }
                let fact = self.parse_fact(&mut tb.body[0])?;
                let forall = match fact {
                    Fact::ForallFact(ff) => ff,
                    _ => {
                        return Err(RuntimeError::from(ParseRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_line_file(
                                "`have fn <name> as set:` expects a `forall` fact".to_string(),
                                lf,
                            ),
                        )));
                    }
                };
                return Ok(HaveFnByForallExistUniqueStmt::new(name, forall, lf).into());
            }
            if tb.current_token_is_equal_to(BY) {
                if as_algo {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "`have fn as algo` expects an executable function signature and body"
                                .to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                tb.skip_token(BY)?;
                let lf = tb.line_file.clone();
                let fact = self.parse_fact(tb)?;
                let forall = match fact {
                    Fact::ForallFact(ff) => ff,
                    _ => {
                        return Err(RuntimeError::from(ParseRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_line_file(
                                "have fn <name> by ... expects a `forall` fact".to_string(),
                                lf,
                            ),
                        )));
                    }
                };
                if !tb.exceed_end_of_head() {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "unexpected token after `have fn` `by` `forall` fact".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                return Ok(HaveFnByForallExistUniqueStmt::new(name, forall, lf).into());
            }

            let fs = self.parse_fn_set_clause(tb)?;
            let fn_param_names = fs.collect_all_param_names_including_nested_ret_fn_sets();
            let top_level_fn_param_names =
                ParamGroupWithSet::collect_param_names(&fs.params_def_with_set);

            if tb.current_token_is_equal_to(EQUAL) {
                tb.skip_token(EQUAL)?;

                let lf = tb.line_file.clone();
                let equal_to = self.with_optional_free_param_scope(
                    ParamObjType::FnSet,
                    &fn_param_names,
                    lf,
                    |this| this.parse_obj(tb),
                )?;
                let equal_to_anonymous_fn = AnonymousFn::new(
                    fs.params_def_with_set.clone(),
                    fs.dom_facts.clone(),
                    fs.ret_set.clone(),
                    equal_to,
                )?;
                Ok(
                    HaveFnEqualStmt::new(
                        name,
                        equal_to_anonymous_fn,
                        as_algo,
                        tb.line_file.clone(),
                    )
                    .into(),
                )
            } else if tb.current_token_is_equal_to(COLON) {
                tb.skip_token(COLON)?;
                self.parse_have_fn_case_by_case_stmt_after_colon(
                    tb,
                    name,
                    fs,
                    &fn_param_names,
                    as_algo,
                )
            } else if tb.current_token_is_equal_to(BY) {
                if tb.token_at_add_index(1) == CASES {
                    self.parse_have_fn_by_cases_stmt_after_signature(
                        tb,
                        name,
                        fs,
                        &fn_param_names,
                        as_algo,
                    )
                } else if tb.token_at_add_index(1) == INDUC {
                    self.parse_have_fn_by_induc_stmt_after_signature(
                        tb,
                        name,
                        fs,
                        top_level_fn_param_names,
                        as_algo,
                    )
                } else if tb.token_at_add_index(1) == "decreasing" {
                    Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "`by decreasing <measure> from <lower>` has been replaced by `by induc <measure> from <lower>`"
                                .to_string(),
                            tb.line_file.clone(),
                        ),
                    )))
                } else {
                    Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "expected `by cases` or `by induc <measure> from <lower>` after `have fn` signature"
                                .to_string(),
                            tb.line_file.clone(),
                        ),
                    )))
                }
            } else {
                Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "expected `=`, `:`, `by cases`, or `by induc <measure> from <lower>` after `have fn` signature"
                            .to_string(),
                        tb.line_file.clone(),
                    ),
                )))
            }
        }
    }

    fn parse_have_fn_case_by_case_stmt_after_colon(
        &mut self,
        tb: &mut TokenBlock,
        name: String,
        fn_set_clause: FnSetClause,
        fn_param_names: &[String],
        as_algo: bool,
    ) -> Result<Stmt, RuntimeError> {
        let (cases, equal_tos) =
            self.parse_have_fn_case_by_case_blocks(&mut tb.body, fn_param_names)?;
        Ok(HaveFnEqualCaseByCaseStmt::new(
            name,
            fn_set_clause,
            cases,
            equal_tos,
            as_algo,
            tb.line_file.clone(),
        )
        .into())
    }

    fn parse_have_fn_by_cases_stmt_after_signature(
        &mut self,
        tb: &mut TokenBlock,
        name: String,
        fn_set_clause: FnSetClause,
        fn_param_names: &[String],
        as_algo: bool,
    ) -> Result<Stmt, RuntimeError> {
        tb.skip_token(BY)?;
        tb.skip_token(CASES)?;
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "unexpected token after `have fn ... by cases:`".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        self.parse_have_fn_case_by_case_stmt_after_colon(
            tb,
            name,
            fn_set_clause,
            fn_param_names,
            as_algo,
        )
    }

    fn parse_have_fn_case_by_case_blocks(
        &mut self,
        blocks: &mut [TokenBlock],
        fn_param_names: &[String],
    ) -> Result<(Vec<AndChainAtomicFact>, Vec<Obj>), RuntimeError> {
        let mut cases: Vec<AndChainAtomicFact> = Vec::with_capacity(blocks.len());
        let mut equal_tos: Vec<Obj> = Vec::with_capacity(blocks.len());
        for block in blocks.iter_mut() {
            block.skip_token(CASE)?;
            let case_lf = block.line_file.clone();
            cases.push(self.with_optional_free_param_scope(
                ParamObjType::FnSet,
                fn_param_names,
                case_lf,
                |this| this.parse_and_chain_atomic_fact(block),
            )?);
            block.skip_token(COLON)?;
            let rhs_lf = block.line_file.clone();
            equal_tos.push(self.with_optional_free_param_scope(
                ParamObjType::FnSet,
                fn_param_names,
                rhs_lf,
                |this| this.parse_obj(block),
            )?);
        }
        Ok((cases, equal_tos))
    }

    fn parse_have_fn_by_induc_stmt_after_signature(
        &mut self,
        tb: &mut TokenBlock,
        name: String,
        fn_set_clause: FnSetClause,
        fn_param_names: Vec<String>,
        as_algo: bool,
    ) -> Result<Stmt, RuntimeError> {
        self.parse_have_fn_by_induc_block(tb, name, fn_set_clause, &fn_param_names, as_algo)
    }

    fn parse_have_fn_by_induc_block(
        &mut self,
        block: &mut TokenBlock,
        name: String,
        fn_set_clause: FnSetClause,
        fn_param_names: &[String],
        as_algo: bool,
    ) -> Result<Stmt, RuntimeError> {
        block.skip_token(BY)?;
        block.skip_token(INDUC)?;

        let measure_lf = block.line_file.clone();
        let measure = self.with_optional_free_param_scope(
            ParamObjType::FnSet,
            fn_param_names,
            measure_lf,
            |this| this.parse_obj(block),
        )?;

        block.skip_token(FROM)?;
        let lower_lf = block.line_file.clone();
        let lower_bound = self.with_optional_free_param_scope(
            ParamObjType::FnSet,
            fn_param_names,
            lower_lf,
            |this| this.parse_obj(block),
        )?;
        block.skip_token(COLON)?;
        if !block.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "unexpected token after `by induc <measure> from <lower>:`".to_string(),
                    block.line_file.clone(),
                ),
            )));
        }
        if block.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "`by induc <measure> from <lower>` expects at least one `case` block"
                        .to_string(),
                    block.line_file.clone(),
                ),
            )));
        }

        let cases = self.parse_have_fn_by_induc_cases(&mut block.body, fn_param_names)?;
        Ok(HaveFnByInducStmt::new(
            name,
            fn_set_clause,
            measure,
            lower_bound,
            cases,
            as_algo,
            block.line_file.clone(),
        )
        .into())
    }

    fn parse_have_fn_by_induc_cases(
        &mut self,
        blocks: &mut [TokenBlock],
        fn_param_names: &[String],
    ) -> Result<Vec<HaveFnByInducCase>, RuntimeError> {
        let mut cases = Vec::with_capacity(blocks.len());
        for block in blocks.iter_mut() {
            cases.push(self.parse_have_fn_by_induc_case(block, fn_param_names)?);
        }
        Ok(cases)
    }

    fn parse_have_fn_by_induc_case(
        &mut self,
        block: &mut TokenBlock,
        fn_param_names: &[String],
    ) -> Result<HaveFnByInducCase, RuntimeError> {
        block.skip_token(CASE)?;
        let case_lf = block.line_file.clone();
        let case_fact = self.with_optional_free_param_scope(
            ParamObjType::FnSet,
            fn_param_names,
            case_lf,
            |this| this.parse_and_chain_atomic_fact_allow_leading_not(block),
        )?;
        block.skip_token(COLON)?;

        if !block.exceed_end_of_head() {
            let rhs_lf = block.line_file.clone();
            let equal_to = self.with_optional_free_param_scope(
                ParamObjType::FnSet,
                fn_param_names,
                rhs_lf,
                |this| this.parse_obj(block),
            )?;
            if !block.exceed_end_of_head() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "unexpected token after case right-hand side".to_string(),
                        block.line_file.clone(),
                    ),
                )));
            }
            if !block.body.is_empty() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "a case with an inline right-hand side cannot also have nested cases"
                            .to_string(),
                        block.line_file.clone(),
                    ),
                )));
            }
            return Ok(HaveFnByInducCase::new(
                case_fact,
                HaveFnByInducCaseBody::EqualTo(equal_to),
            ));
        }

        if block.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "case must end with a right-hand side or nested case blocks".to_string(),
                    block.line_file.clone(),
                ),
            )));
        }

        let nested = self.parse_have_fn_by_induc_cases(&mut block.body, fn_param_names)?;
        Ok(HaveFnByInducCase::new(
            case_fact,
            HaveFnByInducCaseBody::NestedCases(nested),
        ))
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

        self.register_collected_param_names_for_def_parse(&equal_tos, tb.line_file.clone())?;

        Ok(HaveByExistStmt::new(equal_tos, true_fact, tb.line_file.clone()).into())
    }

    pub fn parse_have_preimage(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(HAVE)?;
        tb.skip_token(BY)?;
        tb.skip_token(PREIMAGE)?;

        let mut preimage_names = Vec::new();
        loop {
            if tb.current_token_is_equal_to(FROM) {
                if preimage_names.is_empty() {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "have by preimage expects at least one preimage name".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                break;
            }
            let name = tb.advance()?;
            is_valid_litex_name(&name).map_err(|msg| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone()),
                ))
            })?;
            preimage_names.push(name);
            if tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
            } else if tb.current_token_is_equal_to(FROM) {
                break;
            } else {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "have by preimage expects `,` or `from` after a preimage name".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
        }

        tb.skip_token(FROM)?;
        let source_fact = self.parse_atomic_fact(tb, true)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "unexpected token after have by preimage source fact".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        let range_membership = match source_fact {
            AtomicFact::InFact(in_fact) => in_fact,
            _ => {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "have by preimage expects `from z $in fn_range(f)`".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
        };

        self.register_collected_param_names_for_def_parse(&preimage_names, tb.line_file.clone())?;

        Ok(HaveByPreimageStmt::new(preimage_names, range_membership, tb.line_file.clone()).into())
    }

    pub fn parse_def_algorithm_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(ALGO)?;
        let name = tb.advance()?;
        self.run_in_local_parsing_time_name_scope(move |this| {
            tb.skip_token(LEFT_BRACE)?;
            let mut params: Vec<String> = vec![];
            while tb.current()? != RIGHT_BRACE {
                params.push(tb.advance()?);
                if tb.current_token_is_equal_to(COMMA) {
                    tb.skip_token(COMMA)?;
                }
            }
            tb.skip_token(RIGHT_BRACE)?;
            this.register_collected_param_names_for_def_parse(&params, tb.line_file.clone())?;
            tb.skip_token(COLON)?;
            this.parsing_free_param_collection.begin_scope(
                ParamObjType::DefAlgo,
                &params,
                tb.line_file.clone(),
            )?;
            let params_for_end = params.clone();
            let algo_result = (|| -> Result<DefAlgoStmt, RuntimeError> {
                let mut algo_cases: Vec<AlgoCase> = vec![];
                let mut default_return: Option<AlgoReturn> = None;
                match tb.body.split_last_mut() {
                    None => {}
                    Some((last_block, leading_blocks)) => {
                        for block in leading_blocks.iter_mut() {
                            algo_cases.push(this.parse_algo_case(block)?);
                        }
                        if last_block.current_token_empty_if_exceed_end_of_head() == CASE {
                            algo_cases.push(this.parse_algo_case(last_block)?);
                        } else {
                            default_return = Some(this.parse_algo_return(last_block)?);
                        }
                    }
                }
                Ok(DefAlgoStmt::new(
                    name,
                    params,
                    algo_cases,
                    default_return,
                    tb.line_file.clone(),
                ))
            })();
            this.parsing_free_param_collection
                .end_scope(ParamObjType::DefAlgo, &params_for_end);
            Ok(algo_result?.into())
        })
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

impl Runtime {
    pub fn register_collected_param_names_for_def_parse(
        &mut self,
        names: &Vec<String>,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        self.validate_names_and_insert_into_top_parsing_time_name_scope(names, line_file.clone())
            .map_err(|e| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    String::new(),
                    line_file,
                    Some(e),
                    vec![],
                )))
            })
    }

    /// `prop name` / similar: consumes `{` … `}` of typed param groups and registers names.
    fn parse_def_braced_param_groups_with_param_type(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<ParamDefWithType, RuntimeError> {
        tb.skip_token(LEFT_BRACE)?;
        let mut groups = Vec::new();
        while tb.current()? != RIGHT_BRACE {
            groups.push(
                self.parse_param_def_with_param_type_and_skip_comma(tb, ParamObjType::DefHeader)?,
            );
        }
        tb.skip_token(RIGHT_BRACE)?;
        let param_defs = ParamDefWithType::new(groups);
        let names = param_defs.collect_param_names();
        self.register_collected_param_names_for_def_parse(&names, tb.line_file.clone())?;
        Ok(param_defs)
    }

    pub fn insert_parsed_name_into_top_parsing_time_name_scope(
        &mut self,
        name: &str,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        self.validate_name_and_insert_into_top_parsing_time_name_scope(name, line_file.clone())
            .map_err(|e| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    String::new(),
                    line_file,
                    Some(e),
                    vec![],
                )))
            })
    }

    pub fn parse_name_and_insert_into_top_parsing_time_name_scope(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<String, RuntimeError> {
        let name = tb.advance()?;
        self.insert_parsed_name_into_top_parsing_time_name_scope(&name, tb.line_file.clone())?;
        Ok(name)
    }

    fn parse_template_body_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<TemplateDefEnum, RuntimeError> {
        let stmt = self.parse_stmt(tb)?;
        match stmt {
            Stmt::HaveObjInNonemptySetStmt(stmt) => {
                Ok(TemplateDefEnum::HaveObjInNonemptySetStmt(stmt))
            }
            Stmt::HaveObjEqualStmt(stmt) => Ok(TemplateDefEnum::HaveObjEqualStmt(stmt)),
            Stmt::HaveByExistStmt(stmt) => Ok(TemplateDefEnum::HaveByExistStmt(stmt)),
            Stmt::HaveFnEqualStmt(stmt) => Ok(TemplateDefEnum::HaveFnEqualStmt(stmt)),
            Stmt::HaveFnEqualCaseByCaseStmt(stmt) => {
                Ok(TemplateDefEnum::HaveFnEqualCaseByCaseStmt(stmt))
            }
            Stmt::HaveFnByInducStmt(stmt) => Ok(TemplateDefEnum::HaveFnByInducStmt(stmt)),
            Stmt::HaveFnByForallExistUniqueStmt(stmt) => {
                Ok(TemplateDefEnum::HaveFnByForallExistUniqueStmt(stmt))
            }
            _ => Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "template body only supports `have` definition statements".to_string(),
                    tb.line_file.clone(),
                ),
            ))),
        }
    }
}
