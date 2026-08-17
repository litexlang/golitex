use crate::prelude::*;

impl Runtime {
    pub fn parse_def_setting_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(SETTING)?;
        let name = tb.advance()?;
        self.validate_name(&name, tb.line_file.clone())?;
        if !tb.current_token_is_equal_to(LEFT_BRACE) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "setting header expects `setting Name(...)`".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        self.run_in_local_parsing_time_name_scope(|this| {
            let (param_def, mut dom_facts) = this.parse_def_parameter_bundles_between(
                tb,
                LEFT_BRACE,
                RIGHT_BRACE,
                ParamObjType::Forall,
                "setting",
            )?;

            if param_def.is_empty() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "setting expects at least one parameter".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }

            if tb.current_token_is_equal_to(COLON) {
                tb.skip_token(COLON)?;
                if !tb.exceed_end_of_head() {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "setting header expects `:` to end the header".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                dom_facts.extend(this.parse_facts_in_body(tb)?);
            } else {
                if !tb.exceed_end_of_head() {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "setting header expects `:` or end of line after `)`".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
            }

            Ok(DefSettingStmt::new(name, param_def, dom_facts, tb.line_file.clone()).into())
        })
    }

    pub fn parse_def_template_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(TEMPLATE)?;
        if !tb.current_token_is_equal_to(LESS) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "template definition expects `template<...>:`; define the template name in the single body `have` or `trust have` statement".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

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
                    template_arg_dom.push(this.parse_quantifier_free_fact(&mut header_block)?);
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
            let template_name = match template_def_stmt.defined_name() {
                Some(name) => name,
                None => {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "template body must define exactly one object or function".to_string(),
                            tb.body[0].line_file.clone(),
                        ),
                    )));
                }
            };

            this.end_parsing_scope(ParamObjType::DefHeader, &template_arg_names);

            Ok(DefTemplateStmt::new(
                template_name,
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
            let (param_def_with_dom, setting_facts) = if tb.current_token_is_equal_to(LESS) {
                let (param_def, setting_facts) = this.parse_def_parameter_bundles_between(
                    tb,
                    LESS,
                    GREATER,
                    ParamObjType::DefHeader,
                    "struct",
                )?;
                (Some((param_def, Vec::new())), setting_facts)
            } else if tb.current_token_is_equal_to(LEFT_BRACE) {
                let (param_def, setting_facts) = this.parse_def_parameter_bundles_between(
                    tb,
                    LEFT_BRACE,
                    RIGHT_BRACE,
                    ParamObjType::DefHeader,
                    "struct",
                )?;
                (Some((param_def, Vec::new())), setting_facts)
            } else {
                (None, Vec::new())
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
                            "struct definition expects at least one field".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }

                let mut parsed_fields: Vec<(String, Obj)> = Vec::new();
                let mut field_bindings: Vec<SymbolBinding> = Vec::new();
                let mut equivalent_facts = setting_facts;
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
                        let field_names = parsed_fields
                            .iter()
                            .map(|(field_name, _)| field_name.clone())
                            .collect::<Vec<_>>();
                        field_bindings = this.allocate_local_symbol_bindings(&field_names)?;
                        for ((_, field_type), field_binding) in
                            parsed_fields.iter().zip(field_bindings.iter())
                        {
                            if let Obj::StructObj(struct_obj) = field_type {
                                this.register_default_struct_view(
                                    std::slice::from_ref(field_binding),
                                    struct_obj,
                                );
                            }
                        }
                        equivalent_facts
                            .extend(this.parse_struct_equivalent_facts(block, &field_bindings)?);
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
                        if parsed_fields.iter().any(|(name, _)| name == &field.0) {
                            return Err(RuntimeError::from(ParseRuntimeError(
                                RuntimeErrorStruct::new_with_msg_and_line_file(
                                    format!("duplicate struct field `{}`", field.0),
                                    block.line_file.clone(),
                                ),
                            )));
                        }
                        parsed_fields.push(field);
                    }
                }

                if parsed_fields.is_empty() {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "struct definition expects at least one field".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                if field_bindings.is_empty() {
                    let field_names = parsed_fields
                        .iter()
                        .map(|(field_name, _)| field_name.clone())
                        .collect::<Vec<_>>();
                    field_bindings = this.allocate_local_symbol_bindings(&field_names)?;
                }

                let fields = parsed_fields
                    .into_iter()
                    .zip(field_bindings)
                    .map(|((field_name, field_type), binding)| {
                        debug_assert_eq!(field_name, binding.name());
                        StructFieldDef::new(binding, field_type)
                    })
                    .collect();

                Ok(DefStructStmt::new(
                    name.clone(),
                    param_def_with_dom,
                    fields,
                    equivalent_facts,
                    tb.line_file.clone(),
                ))
            })();

            if !struct_param_names.is_empty() {
                this.end_parsing_scope(ParamObjType::DefHeader, &struct_param_names);
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
        field_bindings: &[SymbolBinding],
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
        let field_names = field_bindings
            .iter()
            .map(|binding| binding.name().to_string())
            .collect::<Vec<_>>();
        self.current_parse_context_mut().free_params.begin_scope(
            ParamObjType::DefStructField,
            field_bindings,
            block.line_file.clone(),
        )?;
        self.current_parse_context_mut()
            .push_scope_frame(field_bindings.to_vec());
        let facts_result = self.parse_facts_in_body(block);
        self.end_parsing_scope(ParamObjType::DefStructField, &field_names);
        facts_result
    }

    pub fn parse_def_prop_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        let stmt = self.run_in_local_parsing_time_name_scope(|this| {
            tb.skip_token(PROP)?;
            let name = this.parse_name_and_insert_into_top_parsing_time_name_scope(tb)?;
            let (param_defs, mut setting_facts) = this.parse_def_prop_parameter_bundles(tb)?;
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
                    this.end_parsing_scope(ParamObjType::DefHeader, &def_param_names);
                    return Ok(DefPropStmt::new(
                        name,
                        param_defs,
                        setting_facts,
                        tb.line_file.clone(),
                    ));
                }
            }

            let facts_result = this.parse_facts_in_body(tb);
            this.end_parsing_scope(ParamObjType::DefHeader, &def_param_names);
            setting_facts.extend(facts_result?);
            Ok(DefPropStmt::new(
                name,
                param_defs,
                setting_facts,
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

    pub fn parse_trust_have_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(HAVE)?;
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
                Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "`trust have ...:` facts must be written in an indented body".to_string(),
                        tb.line_file.clone(),
                    ),
                )))
            };
            if facts_result.is_err() && !all_param_names.is_empty() {
                self.end_parsing_scope(ParamObjType::Identifier, &all_param_names);
            }
            let facts = facts_result?;
            self.end_parsing_scope(ParamObjType::Identifier, &all_param_names);
            facts
        } else {
            if !all_param_names.is_empty() {
                self.end_parsing_scope(ParamObjType::Identifier, &all_param_names);
            }
            vec![]
        };
        self.register_local_existing_identifier_bindings_for_parse(
            &param_def.collect_param_bindings(),
            tb.line_file.clone(),
        )?;
        Ok(TrustHaveStmt::new(param_def, facts, tb.line_file.clone()).into())
    }

    pub fn parse_let_obj_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(LET)?;
        let name = tb.advance()?;
        is_valid_litex_name(&name).map_err(|msg| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone()),
            ))
        })?;
        tb.skip_token(EQUAL)?;
        let value = self.parse_obj(tb)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "unexpected token after let value expression".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        let symbol_binding = self.allocate_declared_symbol_binding(name.clone())?;
        self.register_local_existing_identifier_bindings_for_parse(
            &[symbol_binding.clone()],
            tb.line_file.clone(),
        )?;
        Ok(LetObjStmt::new(symbol_binding, value, tb.line_file.clone()).into())
    }

    // return HaveObjInNonemptySetOrParamTypeStmt, HaveObjEqualStmt, or HaveObjByExistFactsStmt
    pub fn parse_have_obj_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(HAVE)?;
        let has_fact_body = self.have_obj_stmt_has_fact_body(tb)?;
        let binding_kind = if has_fact_body {
            ParamObjType::Exist
        } else {
            ParamObjType::Identifier
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
        let param_defs = ParamDefWithType::new(param_defs);
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
                self.end_parsing_scope(ParamObjType::Exist, &have_param_names);
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
            self.end_parsing_scope(ParamObjType::Identifier, &have_param_names);
        }
        register_result?;

        if tb.current().map(|t| t != EQUAL).unwrap_or(true) {
            if !have_param_names.is_empty() {
                self.end_parsing_scope(ParamObjType::Identifier, &have_param_names);
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
            self.end_parsing_scope(ParamObjType::Identifier, &have_param_names);
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
                ParamObjType::Identifier,
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
        binding_kind: ParamObjType,
    ) -> Result<Vec<ParamGroupWithParamType>, RuntimeError> {
        let mut param_defs: Vec<ParamGroupWithParamType> = vec![];
        loop {
            match tb.current() {
                Ok(t) if t == EQUAL || t == COLON => break,
                Err(_) => break,
                Ok(_) => {}
            }
            param_defs.push(self.parse_param_def_with_param_type_and_skip_comma(tb, binding_kind)?);
        }
        Ok(param_defs)
    }

    pub fn parse_have_tuple_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(HAVE)?;
        tb.skip_token(TUPLE)?;
        let name = parse_have_tuple_or_cart_name(tb)?;
        let symbol_binding = self.allocate_declared_symbol_binding(name.clone())?;
        skip_have_indexed_definition_keyword(tb, "have tuple")?;
        let index_name = parse_have_tuple_or_cart_name(tb)?;
        tb.skip_token(LESS_EQUAL)?;
        let dimension = self.parse_obj(tb)?;
        tb.skip_token(COMMA)?;

        let index_names = vec![index_name.clone()];
        let ((lhs, value), index_bindings) = self.parse_in_local_free_param_scope_with_bindings(
            ParamObjType::TupleIndex,
            &index_names,
            tb.line_file.clone(),
            |this| {
                let lhs = this.parse_obj(tb)?;
                tb.skip_token(EQUAL)?;
                let value = this.parse_obj(tb)?;
                if !tb.exceed_end_of_head() {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "unexpected token after have tuple value expression".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                Ok((lhs, value))
            },
        )?;
        validate_have_tuple_lhs(&lhs, &name, &index_name, tb.line_file.clone())?;

        self.register_local_existing_identifier_bindings_for_parse(
            std::slice::from_ref(&symbol_binding),
            tb.line_file.clone(),
        )?;
        Ok(HaveTupleStmt::new(
            symbol_binding,
            index_bindings[0].clone(),
            dimension,
            value,
            tb.line_file.clone(),
        )
        .into())
    }

    pub fn parse_have_cart_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(HAVE)?;
        tb.skip_token(CART)?;
        let name = parse_have_tuple_or_cart_name(tb)?;
        let symbol_binding = self.allocate_declared_symbol_binding(name.clone())?;
        skip_have_indexed_definition_keyword(tb, "have cart")?;
        let index_name = parse_have_tuple_or_cart_name(tb)?;
        tb.skip_token(LESS_EQUAL)?;
        let dimension = self.parse_obj(tb)?;
        tb.skip_token(COMMA)?;

        let index_names = vec![index_name.clone()];
        let ((lhs, value), index_bindings) = self.parse_in_local_free_param_scope_with_bindings(
            ParamObjType::CartIndex,
            &index_names,
            tb.line_file.clone(),
            |this| {
                let lhs = this.parse_obj(tb)?;
                tb.skip_token(EQUAL)?;
                let value = this.parse_obj(tb)?;
                if !tb.exceed_end_of_head() {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "unexpected token after have cart value expression".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                Ok((lhs, value))
            },
        )?;
        validate_have_cart_lhs(&lhs, &name, &index_name, tb.line_file.clone())?;

        self.register_local_existing_identifier_bindings_for_parse(
            std::slice::from_ref(&symbol_binding),
            tb.line_file.clone(),
        )?;
        Ok(HaveCartStmt::new(
            symbol_binding,
            index_bindings[0].clone(),
            dimension,
            value,
            tb.line_file.clone(),
        )
        .into())
    }

    pub fn parse_have_seq_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(HAVE)?;
        tb.skip_token(SEQ)?;
        let name = parse_have_tuple_or_cart_name(tb)?;
        let symbol_binding = self.allocate_declared_symbol_binding(name.clone())?;
        let seq_set = match self.parse_obj(tb)? {
            Obj::SeqSet(seq_set) => seq_set,
            _ => {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "have seq expects typed header `seq(S)`".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
        };
        skip_have_indexed_definition_keyword(tb, "have seq")?;
        let index_name = parse_have_tuple_or_cart_name(tb)?;
        tb.skip_token(COMMA)?;

        let index_names = vec![index_name.clone()];
        let ((lhs, value), index_bindings) = self.parse_in_local_free_param_scope_with_bindings(
            ParamObjType::FnSet,
            &index_names,
            tb.line_file.clone(),
            |this| {
                let lhs = this.parse_obj(tb)?;
                tb.skip_token(EQUAL)?;
                let value = this.parse_obj(tb)?;
                if !tb.exceed_end_of_head() {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "unexpected token after have seq value expression".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                Ok((lhs, value))
            },
        )?;
        validate_have_seq_lhs(&lhs, &name, &index_name, tb.line_file.clone())?;

        self.register_local_existing_identifier_bindings_for_parse(
            std::slice::from_ref(&symbol_binding),
            tb.line_file.clone(),
        )?;
        Ok(HaveSeqStmt::new(
            symbol_binding,
            seq_set,
            index_bindings[0].clone(),
            value,
            tb.line_file.clone(),
        )
        .into())
    }

    pub fn parse_have_finite_seq_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        tb.skip_token(HAVE)?;
        tb.skip_token(FINITE_SEQ)?;
        let name = parse_have_tuple_or_cart_name(tb)?;
        let symbol_binding = self.allocate_declared_symbol_binding(name.clone())?;
        let finite_seq_set = match self.parse_obj(tb)? {
            Obj::FiniteSeqSet(finite_seq_set) => finite_seq_set,
            _ => {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "have finite_seq expects typed header `finite_seq(S, n)`".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
        };
        skip_have_indexed_definition_keyword(tb, "have finite_seq")?;
        let index_name = parse_have_tuple_or_cart_name(tb)?;
        tb.skip_token(LESS_EQUAL)?;
        let bound = self.parse_obj(tb)?;
        tb.skip_token(COMMA)?;

        let index_names = vec![index_name.clone()];
        let ((lhs, value), index_bindings) = self.parse_in_local_free_param_scope_with_bindings(
            ParamObjType::FnSet,
            &index_names,
            tb.line_file.clone(),
            |this| {
                let lhs = this.parse_obj(tb)?;
                tb.skip_token(EQUAL)?;
                let value = this.parse_obj(tb)?;
                if !tb.exceed_end_of_head() {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "unexpected token after have finite_seq value expression".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                Ok((lhs, value))
            },
        )?;
        validate_have_seq_lhs(&lhs, &name, &index_name, tb.line_file.clone())?;

        self.register_local_existing_identifier_bindings_for_parse(
            std::slice::from_ref(&symbol_binding),
            tb.line_file.clone(),
        )?;
        Ok(HaveFiniteSeqStmt::new(
            symbol_binding,
            finite_seq_set,
            index_bindings[0].clone(),
            bound,
            value,
            tb.line_file.clone(),
        )
        .into())
    }

    pub fn parse_have_matrix_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(HAVE)?;
        tb.skip_token(MATRIX)?;
        let name = parse_have_tuple_or_cart_name(tb)?;
        let symbol_binding = self.allocate_declared_symbol_binding(name.clone())?;
        let matrix_set = match self.parse_obj(tb)? {
            Obj::MatrixSet(matrix_set) => matrix_set,
            _ => {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "have matrix expects typed header `matrix(S, rows, cols)`".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
        };
        skip_have_indexed_definition_keyword(tb, "have matrix")?;
        let row_index_name = parse_have_tuple_or_cart_name(tb)?;
        tb.skip_token(LESS_EQUAL)?;
        let row_bound = self.parse_obj(tb)?;
        tb.skip_token(COMMA)?;
        let col_index_name = parse_have_tuple_or_cart_name(tb)?;
        tb.skip_token(LESS_EQUAL)?;
        let col_bound = self.parse_obj(tb)?;
        tb.skip_token(COMMA)?;

        let index_names = vec![row_index_name.clone(), col_index_name.clone()];
        let ((lhs, value), index_bindings) = self.parse_in_local_free_param_scope_with_bindings(
            ParamObjType::FnSet,
            &index_names,
            tb.line_file.clone(),
            |this| {
                let lhs = this.parse_obj(tb)?;
                tb.skip_token(EQUAL)?;
                let value = this.parse_obj(tb)?;
                if !tb.exceed_end_of_head() {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "unexpected token after have matrix value expression".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                Ok((lhs, value))
            },
        )?;
        validate_have_matrix_lhs(
            &lhs,
            &name,
            &row_index_name,
            &col_index_name,
            tb.line_file.clone(),
        )?;

        self.register_local_existing_identifier_bindings_for_parse(
            std::slice::from_ref(&symbol_binding),
            tb.line_file.clone(),
        )?;
        Ok(HaveMatrixStmt::new(
            symbol_binding,
            matrix_set,
            index_bindings[0].clone(),
            row_bound,
            index_bindings[1].clone(),
            col_bound,
            value,
            tb.line_file.clone(),
        )
        .into())
    }

    pub fn parse_have_fn_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(HAVE)?;
        tb.skip_token(FN_LOWER_CASE)?;
        let name = self.parse_name_and_insert_into_top_parsing_time_name_scope(tb)?;
        let symbol_binding = self.allocate_declared_symbol_binding(name.clone())?;
        if tb.current_token_is_equal_to(BY) {
            tb.skip_token(BY)?;
            if tb.current_token_is_equal_to(EXIST) && tb.token_at_add_index(1) == "!" {
                tb.skip_token(EXIST)?;
                tb.skip_token("!")?;
                tb.skip_token(COLON)?;
                if !tb.exceed_end_of_head() {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "unexpected token after `have fn <name> by exist!:`".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                return self.parse_have_fn_by_exist_unique_body(tb, symbol_binding);
            }
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "expected `by exist!:` after `have fn <name>` for unique-existence function definitions"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        let fs = self.parse_fn_set_clause(tb)?;
        let fn_param_bindings = fs.collect_all_param_bindings_including_nested_ret_fn_sets();
        let top_level_fn_param_bindings = fs.params_def_with_set.collect_param_bindings();

        if tb.current_token_is_equal_to(EQUAL) {
            tb.skip_token(EQUAL)?;

            let lf = tb.line_file.clone();
            let equal_to = self.parse_in_existing_free_param_scope(
                ParamObjType::FnSet,
                &fn_param_bindings,
                lf,
                |this| this.parse_obj(tb),
            )?;
            let equal_to_anonymous_fn = AnonymousFn::new(
                fs.params_def_with_set.clone(),
                fs.dom_facts.clone(),
                fs.ret_set.clone(),
                equal_to,
            )?;
            let stmt = HaveFnEqualStmt::new(
                symbol_binding.clone(),
                equal_to_anonymous_fn,
                tb.line_file.clone(),
            );
            self.register_local_existing_identifier_bindings_for_parse(
                std::slice::from_ref(&symbol_binding),
                tb.line_file.clone(),
            )?;
            Ok(stmt.into())
        } else if tb.current_token_is_equal_to(COLON) {
            tb.skip_token(COLON)?;
            self.parse_have_fn_case_by_case_stmt_after_colon(
                tb,
                symbol_binding,
                fs,
                &fn_param_bindings,
            )
        } else if tb.current_token_is_equal_to(BY) {
            if tb.token_at_add_index(1) == CASES {
                self.parse_have_fn_by_cases_stmt_after_signature(
                    tb,
                    symbol_binding,
                    fs,
                    &fn_param_bindings,
                )
            } else if tb.token_at_add_index(1) == INDUC {
                self.parse_have_fn_by_induc_stmt_after_signature(
                    tb,
                    name,
                    symbol_binding,
                    fs,
                    top_level_fn_param_bindings,
                )
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

    fn parse_have_fn_by_exist_unique_body(
        &mut self,
        tb: &mut TokenBlock,
        symbol_binding: SymbolBinding,
    ) -> Result<Stmt, RuntimeError> {
        let lf = tb.line_file.clone();
        if tb.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "`have fn <name> by exist!:` expects a `? forall ...` goal block".to_string(),
                    lf,
                ),
            )));
        }

        if !tb.body[0].current_token_is_equal_to(QUESTION_GOAL) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "`have fn <name> by exist!:` expects a `? forall ...` goal block".to_string(),
                    tb.body[0].line_file.clone(),
                ),
            )));
        }

        let (forall, inline_proof_start) = {
            let goal_block = tb.body.get_mut(0).ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "`have fn <name> by exist!:` expects a `? forall ...` goal block"
                            .to_string(),
                        lf.clone(),
                    ),
                ))
            })?;
            self.parse_goal_forall_fact_block_with_inline_proof(
                goal_block,
                "`have fn <name> by exist!:`",
            )?
        };
        let bindings = forall.params_def_with_type.collect_param_bindings();
        let prove_process: Vec<Stmt> = self.parse_stmts_with_existing_free_param_bindings(
            ParamObjType::Forall,
            &bindings,
            lf.clone(),
            |this| {
                let mut proof = Vec::new();
                if inline_proof_start > 0 {
                    if let Some(goal_block) = tb.body.get_mut(0) {
                        for block in goal_block.body.iter_mut().skip(inline_proof_start) {
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
        let stmt = HaveFnByForallExistUniqueStmt::new(
            symbol_binding.clone(),
            forall,
            prove_process,
            lf.clone(),
        );
        self.register_local_existing_identifier_bindings_for_parse(
            std::slice::from_ref(&symbol_binding),
            lf,
        )?;
        Ok(stmt.into())
    }

    fn parse_have_fn_case_by_case_stmt_after_colon(
        &mut self,
        tb: &mut TokenBlock,
        symbol_binding: SymbolBinding,
        fn_set_clause: FnSetClause,
        fn_param_bindings: &[SymbolBinding],
    ) -> Result<Stmt, RuntimeError> {
        let (cases, equal_tos) =
            self.parse_have_fn_case_by_case_blocks(&mut tb.body, fn_param_bindings)?;
        let stmt = HaveFnEqualCaseByCaseStmt::new(
            symbol_binding.clone(),
            fn_set_clause,
            cases,
            equal_tos,
            tb.line_file.clone(),
        );
        self.register_local_existing_identifier_bindings_for_parse(
            std::slice::from_ref(&symbol_binding),
            tb.line_file.clone(),
        )?;
        Ok(stmt.into())
    }

    fn parse_have_fn_by_cases_stmt_after_signature(
        &mut self,
        tb: &mut TokenBlock,
        symbol_binding: SymbolBinding,
        fn_set_clause: FnSetClause,
        fn_param_bindings: &[SymbolBinding],
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
            symbol_binding,
            fn_set_clause,
            fn_param_bindings,
        )
    }

    fn parse_have_fn_case_by_case_blocks(
        &mut self,
        blocks: &mut [TokenBlock],
        fn_param_bindings: &[SymbolBinding],
    ) -> Result<(Vec<AndChainAtomicFact>, Vec<Obj>), RuntimeError> {
        let mut cases: Vec<AndChainAtomicFact> = Vec::with_capacity(blocks.len());
        let mut equal_tos: Vec<Obj> = Vec::with_capacity(blocks.len());
        for block in blocks.iter_mut() {
            block.skip_token(CASE)?;
            let case_lf = block.line_file.clone();
            cases.push(self.parse_in_existing_free_param_scope(
                ParamObjType::FnSet,
                fn_param_bindings,
                case_lf,
                |this| this.parse_and_chain_atomic_fact_allow_leading_not(block),
            )?);
            block.skip_token(COLON)?;
            let rhs_lf = block.line_file.clone();
            equal_tos.push(self.parse_in_existing_free_param_scope(
                ParamObjType::FnSet,
                fn_param_bindings,
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
        symbol_binding: SymbolBinding,
        fn_set_clause: FnSetClause,
        fn_param_bindings: Vec<SymbolBinding>,
    ) -> Result<Stmt, RuntimeError> {
        self.parse_have_fn_by_induc_block(
            tb,
            name,
            symbol_binding,
            fn_set_clause,
            &fn_param_bindings,
        )
    }

    fn parse_have_fn_by_induc_block(
        &mut self,
        block: &mut TokenBlock,
        name: String,
        symbol_binding: SymbolBinding,
        fn_set_clause: FnSetClause,
        fn_param_bindings: &[SymbolBinding],
    ) -> Result<Stmt, RuntimeError> {
        block.skip_token(BY)?;
        block.skip_token(INDUC)?;

        let measure_lf = block.line_file.clone();
        let measure = self.parse_in_existing_free_param_scope(
            ParamObjType::FnSet,
            fn_param_bindings,
            measure_lf,
            |this| this.parse_obj(block),
        )?;

        block.skip_token(FROM)?;
        let lower_lf = block.line_file.clone();
        let lower_bound = self.parse_in_existing_free_param_scope(
            ParamObjType::FnSet,
            fn_param_bindings,
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

        let function_names = vec![name.clone()];
        self.current_parse_context_mut().free_params.begin_scope(
            ParamObjType::Identifier,
            std::slice::from_ref(&symbol_binding),
            block.line_file.clone(),
        )?;
        self.current_parse_context_mut()
            .push_scope_frame(vec![symbol_binding.clone()]);
        let cases_result = self.parse_have_fn_by_induc_cases(&mut block.body, fn_param_bindings);
        self.end_parsing_scope(ParamObjType::Identifier, &function_names);
        let cases = cases_result?;
        let stmt = HaveFnByInducStmt::new(
            symbol_binding.clone(),
            fn_set_clause,
            measure,
            lower_bound,
            cases,
            block.line_file.clone(),
        );
        self.register_local_existing_identifier_bindings_for_parse(
            std::slice::from_ref(&symbol_binding),
            block.line_file.clone(),
        )?;
        Ok(stmt.into())
    }

    fn parse_have_fn_by_induc_cases(
        &mut self,
        blocks: &mut [TokenBlock],
        fn_param_bindings: &[SymbolBinding],
    ) -> Result<Vec<HaveFnByInducCase>, RuntimeError> {
        let mut cases = Vec::with_capacity(blocks.len());
        for block in blocks.iter_mut() {
            cases.push(self.parse_have_fn_by_induc_case(block, fn_param_bindings)?);
        }
        Ok(cases)
    }

    fn parse_have_fn_by_induc_case(
        &mut self,
        block: &mut TokenBlock,
        fn_param_bindings: &[SymbolBinding],
    ) -> Result<HaveFnByInducCase, RuntimeError> {
        block.skip_token(CASE)?;
        let case_lf = block.line_file.clone();
        let case_fact = self.parse_in_existing_free_param_scope(
            ParamObjType::FnSet,
            fn_param_bindings,
            case_lf,
            |this| this.parse_and_chain_atomic_fact_allow_leading_not(block),
        )?;
        block.skip_token(COLON)?;

        if !block.exceed_end_of_head() {
            let rhs_lf = block.line_file.clone();
            let equal_to = self.parse_in_existing_free_param_scope(
                ParamObjType::FnSet,
                fn_param_bindings,
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

        let nested = self.parse_have_fn_by_induc_cases(&mut block.body, fn_param_bindings)?;
        Ok(HaveFnByInducCase::new(
            case_fact,
            HaveFnByInducCaseBody::NestedCases(nested),
        ))
    }

    pub fn parse_obtain_obj(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(OBTAIN)?;

        let mut equal_tos = vec![];
        loop {
            if tb.current_token_is_equal_to(FROM) {
                if equal_tos.is_empty() {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "`obtain` expects at least one name before `from`".to_string(),
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
            equal_tos.push(name);
            if tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
            } else if !tb.current_token_is_equal_to(FROM) {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "`obtain` expects `,` or `from` after each name".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
        }

        tb.skip_token(FROM)?;
        let source_line_file = tb.line_file.clone();
        let obtain_source_error = |msg: String| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(msg, source_line_file.clone()),
            ))
        };
        let mut source_atomic_fact = None;
        let mut source_thm_call = None;
        let true_fact = if tb.current_token_is_equal_to(EXIST) {
            Some(self.parse_exist_fact(tb)?)
        } else if tb.current_token_is_equal_to(THM) {
            tb.skip_token(THM)?;
            let (thm_name, args) = self.parse_theorem_call(tb)?;
            let preview = self.preview_obtain_obj_from_thm(&thm_name, &args, &source_line_file)?;
            source_thm_call = Some((thm_name, args));
            preview
        } else {
            let source_atomic = self.parse_atomic_fact(tb, true)?;
            let AtomicFact::NormalAtomicFact(source_prop) = source_atomic else {
                return Err(obtain_source_error(
                    "`obtain` expects a positive `exist`/`exist!` fact or a positive prop fact after `from`"
                        .to_string(),
                ));
            };
            let predicate_name = source_prop.predicate.to_string();
            let Some(definition) = self.get_active_prop_definition_by_name(&predicate_name) else {
                let message = if self
                    .get_abstract_prop_definition_by_name(&predicate_name)
                    .is_some()
                {
                    format!(
                        "`obtain ... from {}` requires a concrete `prop` definition; `abstract_prop` has no existential body",
                        source_prop
                    )
                } else {
                    format!(
                        "`obtain ... from {}` could not find a concrete prop definition",
                        source_prop
                    )
                };
                return Err(obtain_source_error(message));
            };
            if definition.iff_facts.len() != 1 {
                return Err(obtain_source_error(format!(
                    "`obtain ... from {}` requires `{}` to have exactly one definition clause, which must be `exist` or `exist!`",
                    source_prop, predicate_name
                )));
            }
            let Fact::ExistFact(definition_exist_fact) = &definition.iff_facts[0] else {
                return Err(obtain_source_error(format!(
                    "`obtain ... from {}` requires the sole definition clause of `{}` to be `exist` or `exist!`",
                    source_prop, predicate_name
                )));
            };
            if definition_exist_fact.is_not_exist() {
                return Err(obtain_source_error(format!(
                    "`obtain ... from {}` cannot eliminate a `not exist` definition clause",
                    source_prop
                )));
            }
            let expected_args = definition.params_def_with_type.number_of_params();
            if source_prop.body.len() != expected_args {
                return Err(obtain_source_error(format!(
                    "`obtain ... from {}` expected {} prop argument(s), got {}",
                    source_prop,
                    expected_args,
                    source_prop.body.len()
                )));
            }
            let param_to_arg_map = self
                .params_to_arg_map(&definition.params_def_with_type, &source_prop.body)
                .map_err(|cause| {
                    RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                        None,
                        format!(
                            "failed to instantiate existential definition of `{}`",
                            predicate_name
                        ),
                        source_line_file.clone(),
                        Some(cause),
                        vec![],
                    )))
                })?;
            let instantiated_exist_fact = self
                .inst_exist_fact(
                    definition_exist_fact,
                    &param_to_arg_map,
                    ParamObjType::DefHeader,
                    Some(&source_line_file),
                )
                .map_err(|cause| {
                    RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                        None,
                        format!(
                            "failed to instantiate existential definition of `{}`",
                            predicate_name
                        ),
                        source_line_file.clone(),
                        Some(cause),
                        vec![],
                    )))
                })?;
            source_atomic_fact = Some(source_prop);
            Some(instantiated_exist_fact)
        };
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "unexpected token after `obtain` source fact".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        self.register_collected_param_names_for_def_parse(&equal_tos, tb.line_file.clone())?;
        let equal_to_bindings = self.allocate_local_symbol_bindings(&equal_tos)?;

        if let Some(true_fact) = true_fact.as_ref() {
            let exist_param_defs = true_fact.params_def_with_type();
            if exist_param_defs.number_of_params() == equal_to_bindings.len() {
                let equal_to_objs = equal_to_bindings
                    .iter()
                    .map(|binding| {
                        param_binding_element_obj_for_store(binding, ParamObjType::Identifier)
                    })
                    .collect::<Vec<_>>();
                let param_to_arg_map =
                    exist_param_defs.param_defs_and_args_to_param_to_arg_map(&equal_to_objs);
                let mut default_struct_views = Vec::new();
                let mut equal_to_index = 0;

                for param_group in exist_param_defs.groups.iter() {
                    for _ in param_group.params.iter() {
                        if let ParamType::Obj(Obj::StructObj(_)) = &param_group.param_type {
                            let instantiated_type = self.inst_param_type(
                                &param_group.param_type,
                                &param_to_arg_map,
                                ParamObjType::Exist,
                            )?;
                            if let ParamType::Obj(Obj::StructObj(struct_obj)) = instantiated_type {
                                default_struct_views
                                    .push((equal_to_bindings[equal_to_index].clone(), struct_obj));
                            }
                        }
                        equal_to_index += 1;
                    }
                }

                for (binding, struct_obj) in default_struct_views {
                    self.register_default_struct_view(std::slice::from_ref(&binding), &struct_obj);
                }
            }
        }

        self.register_local_existing_identifier_bindings_for_parse(
            &equal_to_bindings,
            tb.line_file.clone(),
        )?;

        let stmt = match (source_thm_call, source_atomic_fact, true_fact) {
            (Some((thm_name, args)), None, _) => {
                ObtainObjFromThm::new(equal_to_bindings, thm_name, args, tb.line_file.clone())
                    .into()
            }
            (None, Some(fact), _) => {
                ObtainObjFromAtomicFact::new(equal_to_bindings, fact, tb.line_file.clone()).into()
            }
            (None, None, Some(fact)) => {
                ObtainObjFromExistFact::new(equal_to_bindings, fact, tb.line_file.clone()).into()
            }
            _ => unreachable!("obtain parser must retain exactly one source form"),
        };
        Ok(stmt)
    }

    /// Preview a locally resolvable theorem only to register dependent struct
    /// views for the names introduced by `obtain`. Execution resolves and
    /// validates the theorem again; no theorem definition or existential fact
    /// is cached in the statement.
    fn preview_obtain_obj_from_thm(
        &self,
        thm_name: &AtomicName,
        args: &[Obj],
        line_file: &LineFile,
    ) -> Result<Option<ExistFactEnum>, RuntimeError> {
        let Some(thm) = self.get_thm_definition_by_name(&thm_name.to_string()) else {
            // Reserved builtin theorem interfaces are execution-owned. An
            // unresolved user/imported theorem likewise receives its normal
            // authoritative diagnostic during execution.
            return Ok(None);
        };
        if thm.forall_fact.then_facts.len() != 1 {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "obtain from thm `{}` requires exactly one direct theorem conclusion, got {}",
                        thm_name,
                        thm.forall_fact.then_facts.len()
                    ),
                    line_file.clone(),
                ),
            )));
        }
        let ExistOrAndChainAtomicFact::ExistFact(exist_fact) = &thm.forall_fact.then_facts[0]
        else {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "obtain from thm `{}` requires its sole direct conclusion to be `exist` or `exist!`",
                        thm_name
                    ),
                    line_file.clone(),
                ),
            )));
        };
        if exist_fact.is_not_exist() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "obtain from thm `{}` cannot eliminate a `not exist` conclusion",
                        thm_name
                    ),
                    line_file.clone(),
                ),
            )));
        }
        let Ok(param_to_arg_map) =
            self.params_to_arg_map(&thm.forall_fact.params_def_with_type, args)
        else {
            // Preview data is optional. The executor owns theorem arity and
            // argument diagnostics through the ordinary `by thm` path.
            return Ok(None);
        };
        Ok(self
            .inst_exist_fact(
                exist_fact,
                &param_to_arg_map,
                ParamObjType::TheoremInstantiation,
                Some(line_file),
            )
            .ok())
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
                        "have by preimage expects `from z $in fn_range(f)` or `from z $in replacement(P, A)`".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
        };

        self.register_collected_param_names_for_def_parse(&preimage_names, tb.line_file.clone())?;
        let preimage_bindings = self.allocate_local_symbol_bindings(&preimage_names)?;
        self.register_local_existing_identifier_bindings_for_parse(
            &preimage_bindings,
            tb.line_file.clone(),
        )?;

        Ok(
            HaveByPreimageStmt::new(preimage_bindings, range_membership, tb.line_file.clone())
                .into(),
        )
    }

    /// Parses `have algo for f(a, b):` as an executable implementation of `f`.
    pub fn parse_have_algo_for_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(HAVE)?;
        tb.skip_token(ALGO)?;
        tb.skip_token(FOR)?;
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
            let param_bindings =
                this.begin_parsing_scope(ParamObjType::DefAlgo, &params, tb.line_file.clone())?;
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
                    param_bindings,
                    algo_cases,
                    default_return,
                    tb.line_file.clone(),
                ))
            })();
            this.end_parsing_scope(ParamObjType::DefAlgo, &params_for_end);
            Ok(algo_result?.into())
        })
    }

    /// Parses one `case <condition>: <return>` branch in a function implementation.
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

    /// Parses the return object for an algorithm branch or default return.
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

    /// Definition headers accept ordinary typed parameters mixed with setting
    /// bundles. Each bundle contributes fresh parameters and instantiated
    /// conditions in header order; the caller chooses where those conditions
    /// belong in the target definition.
    fn parse_def_parameter_bundles_between(
        &mut self,
        tb: &mut TokenBlock,
        left_token: &str,
        right_token: &str,
        target_kind: ParamObjType,
        definition_kind: &str,
    ) -> Result<(ParamDefWithType, Vec<Fact>), RuntimeError> {
        tb.skip_token(left_token)?;
        let mut groups = Vec::new();
        let mut setting_facts = Vec::new();
        while !tb.current_token_is_equal_to(right_token) {
            if tb.current_token_is_equal_to(LEFT_BRACKET) {
                let bundle = self.parse_fresh_setting_parameter_bundle(tb, target_kind)?;
                groups.extend(bundle.param_def.groups);
                setting_facts.extend(bundle.dom_facts);
                if tb.current_token_is_equal_to(COMMA) {
                    tb.skip_token(COMMA)?;
                } else if !tb.current_token_is_equal_to(right_token) {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            format!(
                                "expected `,` or `{}` after {} setting parameter bundle",
                                right_token, definition_kind
                            ),
                            tb.line_file.clone(),
                        ),
                    )));
                }
            } else {
                groups.push(self.parse_param_def_with_param_type_and_skip_comma(tb, target_kind)?);
            }
        }
        tb.skip_token(right_token)?;
        let param_defs = ParamDefWithType::new(groups);
        let names = param_defs.collect_param_names();
        self.register_collected_param_names_for_def_parse(&names, tb.line_file.clone())?;
        Ok((param_defs, setting_facts))
    }

    /// Concrete `prop` headers elaborate setting conditions into the
    /// proposition body before any explicitly written facts.
    fn parse_def_prop_parameter_bundles(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<(ParamDefWithType, Vec<Fact>), RuntimeError> {
        self.parse_def_parameter_bundles_between(
            tb,
            LEFT_BRACE,
            RIGHT_BRACE,
            ParamObjType::DefHeader,
            "prop",
        )
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
            Stmt::DefObjStmt(DefObjStmt::HaveObjInNonemptySetStmt(stmt)) => {
                Ok(TemplateDefEnum::HaveObjInNonemptySetStmt(stmt))
            }
            Stmt::DefObjStmt(DefObjStmt::HaveObjEqualStmt(stmt)) => {
                Ok(TemplateDefEnum::HaveObjEqualStmt(stmt))
            }
            Stmt::DefObjStmt(DefObjStmt::HaveObjByExistFactsStmt(stmt)) => {
                Ok(TemplateDefEnum::HaveObjByExistFactsStmt(stmt))
            }
            Stmt::UnsafeStmt(UnsafeStmt::TrustHaveStmt(stmt)) => {
                Ok(TemplateDefEnum::TrustHaveStmt(stmt))
            }
            Stmt::DefObjStmt(DefObjStmt::ObtainObjFromExistFact(stmt)) => {
                Ok(TemplateDefEnum::ObtainObjFromExistFact(stmt))
            }
            Stmt::DefObjStmt(DefObjStmt::ObtainObjFromAtomicFact(stmt)) => {
                Ok(TemplateDefEnum::ObtainObjFromAtomicFact(stmt))
            }
            Stmt::DefObjStmt(DefObjStmt::ObtainObjFromThm(stmt)) => {
                Ok(TemplateDefEnum::ObtainObjFromThm(stmt))
            }
            Stmt::DefObjStmt(DefObjStmt::HaveFnEqualStmt(stmt)) => {
                Ok(TemplateDefEnum::HaveFnEqualStmt(stmt))
            }
            Stmt::DefObjStmt(DefObjStmt::HaveFnEqualCaseByCaseStmt(stmt)) => {
                Ok(TemplateDefEnum::HaveFnEqualCaseByCaseStmt(stmt))
            }
            Stmt::DefObjStmt(DefObjStmt::HaveFnByInducStmt(stmt)) => {
                Ok(TemplateDefEnum::HaveFnByInducStmt(stmt))
            }
            Stmt::DefObjStmt(DefObjStmt::HaveFnByForallExistUniqueStmt(stmt)) => {
                Ok(TemplateDefEnum::HaveFnByForallExistUniqueStmt(stmt))
            }
            Stmt::DefObjStmt(DefObjStmt::HaveTupleStmt(stmt)) => {
                Ok(TemplateDefEnum::HaveTupleStmt(stmt))
            }
            Stmt::DefObjStmt(DefObjStmt::HaveCartStmt(stmt)) => {
                Ok(TemplateDefEnum::HaveCartStmt(stmt))
            }
            Stmt::DefObjStmt(DefObjStmt::HaveSeqStmt(stmt)) => {
                Ok(TemplateDefEnum::HaveSeqStmt(stmt))
            }
            Stmt::DefObjStmt(DefObjStmt::HaveFiniteSeqStmt(stmt)) => {
                Ok(TemplateDefEnum::HaveFiniteSeqStmt(stmt))
            }
            Stmt::DefObjStmt(DefObjStmt::HaveMatrixStmt(stmt)) => {
                Ok(TemplateDefEnum::HaveMatrixStmt(stmt))
            }
            _ => Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "template body only supports `have` and `trust have` definition statements"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            ))),
        }
    }
}

fn parse_have_tuple_or_cart_name(tb: &mut TokenBlock) -> Result<String, RuntimeError> {
    let name = tb.advance()?;
    is_valid_litex_name(&name).map_err(|msg| {
        RuntimeError::from(ParseRuntimeError(
            RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone()),
        ))
    })?;
    Ok(name)
}

fn skip_have_indexed_definition_keyword(
    tb: &mut TokenBlock,
    stmt_name: &str,
) -> Result<(), RuntimeError> {
    if tb.current_token_is_equal_to(FOR) {
        return tb.skip_token(FOR);
    }
    Err(RuntimeError::from(ParseRuntimeError(
        RuntimeErrorStruct::new_with_msg_and_line_file(
            format!("{} expects `for` before the index binder", stmt_name),
            tb.line_file.clone(),
        ),
    )))
}

fn validate_have_tuple_lhs(
    lhs: &Obj,
    name: &str,
    index_name: &str,
    line_file: LineFile,
) -> Result<(), RuntimeError> {
    let Obj::ObjAtIndex(indexed) = lhs else {
        return Err(have_tuple_or_cart_parse_error(
            "have tuple expects left side `name[index]`",
            line_file,
        ));
    };
    if !is_identifier_named(indexed.obj.as_ref(), name) {
        return Err(have_tuple_or_cart_parse_error(
            "have tuple left side must index the tuple being defined",
            line_file,
        ));
    }
    if !is_tuple_index_named(indexed.index.as_ref(), index_name) {
        return Err(have_tuple_or_cart_parse_error(
            "have tuple left side must use the bound index",
            line_file,
        ));
    }
    Ok(())
}

fn validate_have_cart_lhs(
    lhs: &Obj,
    name: &str,
    index_name: &str,
    line_file: LineFile,
) -> Result<(), RuntimeError> {
    let Obj::Proj(proj) = lhs else {
        return Err(have_tuple_or_cart_parse_error(
            "have cart expects left side `proj(name, index)`",
            line_file,
        ));
    };
    if !is_identifier_named(proj.set.as_ref(), name) {
        return Err(have_tuple_or_cart_parse_error(
            "have cart left side must project the cart being defined",
            line_file,
        ));
    }
    if !is_cart_index_named(proj.dim.as_ref(), index_name) {
        return Err(have_tuple_or_cart_parse_error(
            "have cart left side must use the bound index",
            line_file,
        ));
    }
    Ok(())
}

fn validate_have_seq_lhs(
    lhs: &Obj,
    name: &str,
    index_name: &str,
    line_file: LineFile,
) -> Result<(), RuntimeError> {
    let Obj::FnObj(fn_obj) = lhs else {
        return Err(have_tuple_or_cart_parse_error(
            "have seq expects left side `name(index)`",
            line_file,
        ));
    };
    if !is_fn_head_identifier_named(fn_obj.head.as_ref(), name) {
        return Err(have_tuple_or_cart_parse_error(
            "have seq left side must apply the sequence being defined",
            line_file,
        ));
    }
    if fn_obj.body.len() != 1 || fn_obj.body[0].len() != 1 {
        return Err(have_tuple_or_cart_parse_error(
            "have seq left side must use exactly one index",
            line_file,
        ));
    }
    if !is_fn_set_index_named(fn_obj.body[0][0].as_ref(), index_name) {
        return Err(have_tuple_or_cart_parse_error(
            "have seq left side must use the bound index",
            line_file,
        ));
    }
    Ok(())
}

fn validate_have_matrix_lhs(
    lhs: &Obj,
    name: &str,
    row_index_name: &str,
    col_index_name: &str,
    line_file: LineFile,
) -> Result<(), RuntimeError> {
    let Obj::FnObj(fn_obj) = lhs else {
        return Err(have_tuple_or_cart_parse_error(
            "have matrix expects left side `name(row, col)`",
            line_file,
        ));
    };
    if !is_fn_head_identifier_named(fn_obj.head.as_ref(), name) {
        return Err(have_tuple_or_cart_parse_error(
            "have matrix left side must apply the matrix being defined",
            line_file,
        ));
    }
    if fn_obj.body.len() != 1 || fn_obj.body[0].len() != 2 {
        return Err(have_tuple_or_cart_parse_error(
            "have matrix left side must use exactly two indices",
            line_file,
        ));
    }
    if !is_fn_set_index_named(fn_obj.body[0][0].as_ref(), row_index_name)
        || !is_fn_set_index_named(fn_obj.body[0][1].as_ref(), col_index_name)
    {
        return Err(have_tuple_or_cart_parse_error(
            "have matrix left side must use the bound row and column indices",
            line_file,
        ));
    }
    Ok(())
}

fn is_fn_head_identifier_named(head: &FnObjHead, name: &str) -> bool {
    matches!(head, FnObjHead::Identifier(identifier) if identifier.name == name)
        || matches!(head, FnObjHead::IdentifierWithMod(identifier) if identifier.name == name)
}

fn is_identifier_named(obj: &Obj, name: &str) -> bool {
    matches!(obj, Obj::Atom(AtomObj::Identifier(identifier)) if identifier.name == name)
        || matches!(obj, Obj::Atom(AtomObj::IdentifierWithMod(identifier)) if identifier.name == name)
}

fn is_tuple_index_named(obj: &Obj, name: &str) -> bool {
    matches!(obj, Obj::Atom(AtomObj::TupleIndex(index)) if index.name() == name)
}

fn is_cart_index_named(obj: &Obj, name: &str) -> bool {
    matches!(obj, Obj::Atom(AtomObj::CartIndex(index)) if index.name() == name)
}

fn is_fn_set_index_named(obj: &Obj, name: &str) -> bool {
    matches!(obj, Obj::Atom(AtomObj::FnSet(index)) if index.name() == name)
}

fn have_tuple_or_cart_parse_error(msg: &str, line_file: LineFile) -> RuntimeError {
    RuntimeError::from(ParseRuntimeError(
        RuntimeErrorStruct::new_with_msg_and_line_file(msg.to_string(), line_file),
    ))
}
