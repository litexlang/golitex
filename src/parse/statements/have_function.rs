//! Function definitions introduced with `have fn`.

use crate::prelude::*;

impl Runtime {
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

        // A nested proof block is parsed before any of its statements execute.
        // Record a direct, non-dependent struct return carrier now so a later
        // statement in that same block can parse `local_fn(args).field` from
        // the declaration alone. Dependent carriers keep using the executed
        // function signature, whose parameter substitution is exact.
        if let Obj::StructObj(struct_obj) = &fs.ret_set {
            let return_fn_param_names = fs.ret_set.collect_param_obj_names(ParamObjType::FnSet);
            let return_depends_on_fn_param = fn_param_bindings
                .iter()
                .any(|binding| return_fn_param_names.contains(binding.name()));
            if !return_depends_on_fn_param {
                self.register_default_struct_view(
                    std::slice::from_ref(&symbol_binding),
                    struct_obj,
                );
            }
        }

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
                            proof.push(this.parse_statement(block)?);
                        }
                    }
                }
                for block in tb.body.iter_mut().skip(1) {
                    proof.push(this.parse_statement(block)?);
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
}
