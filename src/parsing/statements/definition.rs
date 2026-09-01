//! Definition statements for settings, templates, structs, and propositions.

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
                BindingScope::LocalBinder,
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
            let mut groups: Vec<TypedParameterGroup> = Vec::new();
            loop {
                if header_block.current_token_is_equal_to(COLON)
                    || header_block.exceed_end_of_head()
                {
                    break;
                }
                groups.push(this.parse_param_def_with_param_type_and_skip_comma(
                    &mut header_block,
                    BindingScope::LocalBinder,
                )?);
            }
            let template_arg_def = TypedParameterList::new(groups);
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

            this.end_parsing_scope(&template_arg_names);

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
                    BindingScope::LocalBinder,
                    "struct",
                )?;
                (Some((param_def, Vec::new())), setting_facts)
            } else if tb.current_token_is_equal_to(LEFT_BRACE) {
                let (param_def, setting_facts) = this.parse_def_parameter_bundles_between(
                    tb,
                    LEFT_BRACE,
                    RIGHT_BRACE,
                    BindingScope::LocalBinder,
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
                this.end_parsing_scope(&struct_param_names);
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
            BindingScope::StructureField,
            field_bindings,
            block.line_file.clone(),
        )?;
        self.current_parse_context_mut()
            .push_scope_frame(field_bindings.to_vec());
        let facts_result = self.parse_facts_in_body(block);
        self.end_parsing_scope(&field_names);
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
                    this.end_parsing_scope(&def_param_names);
                    return Ok(DefPropStmt::new(
                        name,
                        param_defs,
                        setting_facts,
                        tb.line_file.clone(),
                    ));
                }
            }

            let facts_result = this.parse_facts_in_body(tb);
            this.end_parsing_scope(&def_param_names);
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
        let mut param_def: Vec<TypedParameterGroup> = vec![];
        loop {
            match tb.current() {
                Ok(t) if t == COLON => break,
                Err(_) => break,
                Ok(_) => {}
            }
            param_def.push(self.parse_param_def_with_param_type_and_skip_comma(
                tb,
                BindingScope::DefinitionBinding,
            )?);
        }
        let param_def = TypedParameterList::new(param_def);
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
                self.end_parsing_scope(&all_param_names);
            }
            let facts = facts_result?;
            self.end_parsing_scope(&all_param_names);
            facts
        } else {
            if !all_param_names.is_empty() {
                self.end_parsing_scope(&all_param_names);
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

        let symbol_binding = self.allocate_definition_symbol_binding(name.clone())?;
        self.register_local_existing_identifier_bindings_for_parse(
            &[symbol_binding.clone()],
            tb.line_file.clone(),
        )?;
        Ok(LetObjStmt::new(symbol_binding, value, tb.line_file.clone()).into())
    }

    // return HaveObjInNonemptySetOrParamTypeStmt, HaveObjEqualStmt, or HaveObjByExistFactsStmt
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
        target_scope: BindingScope,
        definition_kind: &str,
    ) -> Result<(TypedParameterList, Vec<Fact>), RuntimeError> {
        tb.skip_token(left_token)?;
        let mut groups = Vec::new();
        let mut setting_facts = Vec::new();
        while !tb.current_token_is_equal_to(right_token) {
            if tb.current_token_is_equal_to(LEFT_BRACKET) {
                let bundle = self.parse_fresh_setting_parameter_bundle(tb, target_scope)?;
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
                groups.push(self.parse_param_def_with_param_type_and_skip_comma(tb, target_scope)?);
            }
        }
        tb.skip_token(right_token)?;
        let param_defs = TypedParameterList::new(groups);
        let names = param_defs.collect_param_names();
        self.register_collected_param_names_for_def_parse(&names, tb.line_file.clone())?;
        Ok((param_defs, setting_facts))
    }

    /// Concrete `prop` headers elaborate setting conditions into the
    /// proposition body before any explicitly written facts.
    fn parse_def_prop_parameter_bundles(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<(TypedParameterList, Vec<Fact>), RuntimeError> {
        self.parse_def_parameter_bundles_between(
            tb,
            LEFT_BRACE,
            RIGHT_BRACE,
            BindingScope::LocalBinder,
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
        let stmt = self.parse_statement(tb)?;
        match stmt {
            Stmt::Definition(DefinitionStmt::HaveObjInNonemptySetStmt(stmt)) => {
                Ok(TemplateDefEnum::HaveObjInNonemptySetStmt(stmt))
            }
            Stmt::Definition(DefinitionStmt::HaveObjEqualStmt(stmt)) => {
                Ok(TemplateDefEnum::HaveObjEqualStmt(stmt))
            }
            Stmt::Definition(DefinitionStmt::HaveObjByExistFactsStmt(stmt)) => {
                Ok(TemplateDefEnum::HaveObjByExistFactsStmt(stmt))
            }
            Stmt::UnsafeStmt(UnsafeStmt::TrustHaveStmt(stmt)) => {
                Ok(TemplateDefEnum::TrustHaveStmt(stmt))
            }
            Stmt::Definition(DefinitionStmt::ObtainObjFromExistFact(stmt)) => {
                Ok(TemplateDefEnum::ObtainObjFromExistFact(stmt))
            }
            Stmt::Definition(DefinitionStmt::ObtainObjFromAtomicFact(stmt)) => {
                Ok(TemplateDefEnum::ObtainObjFromAtomicFact(stmt))
            }
            Stmt::Definition(DefinitionStmt::ObtainObjFromThm(stmt)) => {
                Ok(TemplateDefEnum::ObtainObjFromThm(stmt))
            }
            Stmt::Definition(DefinitionStmt::HaveFnEqualStmt(stmt)) => {
                Ok(TemplateDefEnum::HaveFnEqualStmt(stmt))
            }
            Stmt::Definition(DefinitionStmt::HaveFnEqualCaseByCaseStmt(stmt)) => {
                Ok(TemplateDefEnum::HaveFnEqualCaseByCaseStmt(stmt))
            }
            Stmt::Definition(DefinitionStmt::HaveFnByInducStmt(stmt)) => {
                Ok(TemplateDefEnum::HaveFnByInducStmt(stmt))
            }
            Stmt::Definition(DefinitionStmt::HaveFnByForallExistUniqueStmt(stmt)) => {
                Ok(TemplateDefEnum::HaveFnByForallExistUniqueStmt(stmt))
            }
            Stmt::Definition(DefinitionStmt::HaveTupleStmt(stmt)) => {
                Ok(TemplateDefEnum::HaveTupleStmt(stmt))
            }
            Stmt::Definition(DefinitionStmt::HaveCartStmt(stmt)) => {
                Ok(TemplateDefEnum::HaveCartStmt(stmt))
            }
            Stmt::Definition(DefinitionStmt::HaveSeqStmt(stmt)) => {
                Ok(TemplateDefEnum::HaveSeqStmt(stmt))
            }
            Stmt::Definition(DefinitionStmt::HaveFiniteSeqStmt(stmt)) => {
                Ok(TemplateDefEnum::HaveFiniteSeqStmt(stmt))
            }
            Stmt::Definition(DefinitionStmt::HaveMatrixStmt(stmt)) => {
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
