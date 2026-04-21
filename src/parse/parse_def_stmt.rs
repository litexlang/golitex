use crate::prelude::*;
use crate::verify::number_is_in_z;
use std::collections::HashSet;

impl Runtime {
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
                    return Err(
                        RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "expect `:` or end of line after `)` in prop statement".to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            ))));
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
            param_def.push(self.parse_param_def_with_param_type_and_skip_comma(tb)?);
        }
        let param_def = ParamDefWithType::new(param_def);
        let all_param_names = param_def.collect_param_names();
        self.register_collected_param_names_for_def_parse(&all_param_names, tb.line_file.clone())?;

        let facts = if tb.current_token_is_equal_to(COLON) {
            tb.skip_token(COLON)?;

            if !tb.exceed_end_of_head() {
                return Err(
                    RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "expect end of line after `:` in let statement".to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            ))));
            }
            self.parsing_free_param_collection.begin_scope(
                ParamObjType::Identifier,
                &all_param_names,
                tb.line_file.clone(),
            )?;
            let facts_result = self.parse_facts_in_body(tb);
            self.parsing_free_param_collection
                .end_scope(ParamObjType::Identifier, &all_param_names);
            let facts = facts_result?;
            if !all_param_names.is_empty() {
                self.parsing_free_param_collection.begin_scope(
                    ParamObjType::Identifier,
                    &all_param_names,
                    tb.line_file.clone(),
                )?;
            }
            facts
        } else {
            if !all_param_names.is_empty() {
                self.parsing_free_param_collection.begin_scope(
                    ParamObjType::Identifier,
                    &all_param_names,
                    tb.line_file.clone(),
                )?;
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
            param_defs.push(self.parse_param_def_with_param_type_and_skip_comma(tb)?);
            match tb.current() {
                Ok(t) if t == EQUAL => break,
                Err(_) => break,
                Ok(_) => {}
            }
        }
        if param_defs.is_empty() {
            return Err(
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "have expects at least one param type pair".to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            ))));
        }
        let param_defs = ParamDefWithType::new(param_defs);
        let have_param_names = param_defs.collect_param_names();
        self.register_collected_param_names_for_def_parse(&have_param_names, tb.line_file.clone())?;

        if tb.current().map(|t| t != EQUAL).unwrap_or(true) {
            self.parsing_free_param_collection.begin_scope(
                ParamObjType::Identifier,
                &have_param_names,
                tb.line_file.clone(),
            )?;
            Ok(HaveObjInNonemptySetOrParamTypeStmt::new(param_defs, tb.line_file.clone()).into())
        } else {
            tb.skip_token(EQUAL)?;
            self.parsing_free_param_collection.begin_scope(
                ParamObjType::Identifier,
                &have_param_names,
                tb.line_file.clone(),
            )?;
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
            if !have_param_names.is_empty() {
                self.parsing_free_param_collection.begin_scope(
                    ParamObjType::Identifier,
                    &have_param_names,
                    tb.line_file.clone(),
                )?;
            }
            Ok(HaveObjEqualStmt::new(param_defs, objs_equal_to, tb.line_file.clone()).into())
        }
    }

    pub fn parse_have_fn_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(HAVE)?;
        tb.skip_token(FN_LOWER_CASE)?;
        if tb.current_token_is_equal_to(BY) {
            tb.skip_token(BY)?;
            self.parse_have_fn_by_induc_stmt(tb)
        } else {
            let name = self.parse_name_and_insert_into_top_parsing_time_name_scope(tb)?;

            let fs = self.parse_fn_set_clause(tb)?;
            let fn_param_names = ParamGroupWithSet::collect_param_names(&fs.params_def_with_set);

            if tb.current_token_is_equal_to(COLON) {
                tb.skip_token(COLON)?;
                let case_block_count = tb.body.len();
                let mut cases: Vec<AndChainAtomicFact> = Vec::with_capacity(case_block_count);
                let mut equal_tos: Vec<Obj> = Vec::with_capacity(case_block_count);
                for block in tb.body.iter_mut() {
                    block.skip_token(CASE)?;
                    let case_lf = block.line_file.clone();
                    cases.push(self.with_optional_free_param_scope(
                        ParamObjType::FnSet,
                        &fn_param_names,
                        case_lf,
                        |this| this.parse_and_chain_atomic_fact(block),
                    )?);
                    block.skip_token(COLON)?;
                    let rhs_lf = block.line_file.clone();
                    equal_tos.push(self.with_optional_free_param_scope(
                        ParamObjType::FnSet,
                        &fn_param_names,
                        rhs_lf,
                        |this| this.parse_obj(block),
                    )?);
                }
                Ok(
                    HaveFnEqualCaseByCaseStmt::new(
                        name,
                        fs,
                        cases,
                        equal_tos,
                        tb.line_file.clone(),
                    )
                    .into(),
                )
            } else {
                tb.skip_token(EQUAL)?;

                let lf = tb.line_file.clone();
                let equal_to = self.with_optional_free_param_scope(
                    ParamObjType::FnSet,
                    &fn_param_names,
                    lf,
                    |this| this.parse_obj(tb),
                )?;
                Ok(HaveFnEqualStmt::new(name, fs, equal_to, tb.line_file.clone()).into())
            }
        }
    }

    /// `have fn by` 已消费；解析 `induc from <Obj>: <name> ( <param> Z: <param> >= <induc_from> ) <ret_set> : case ...`。
    /// 前若干条特例为 `case <k>: obj`，其中 `<k>` 为 **0 起下标占位符**，须与该行顺序一致（第 1 条为 0，第 2 条为 1，…）；
    /// 最后一条须为 `case >= n:`，其中 **n 为特例个数**（数字字面量）；且要么行末 `: obj`，要么 `:` 后换行跟子块 `case when: obj`。
    fn parse_have_fn_by_induc_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(INDUC)?;
        tb.skip_token(FROM)?;
        let induc_from = self.parse_obj(tb)?;
        tb.skip_token(COLON)?;
        let name = self.parse_name_and_insert_into_top_parsing_time_name_scope(tb)?;

        tb.skip_token(LEFT_BRACE)?;
        let param = tb.advance()?;
        if !tb.current_token_is_equal_to(Z) {
            return Err(
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "have fn by induc from: expected `Z` after parameter name".to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            ))));
        }
        tb.skip_token(Z)?;
        tb.skip_token(COLON)?;

        self.run_in_local_parsing_time_name_scope(|this| {
            this.parse_have_fn_by_induc_stmt_after_param_scope(tb, name, param, induc_from)
        })
    }

    fn parse_have_fn_by_induc_stmt_after_param_scope(
        &mut self,
        tb: &mut TokenBlock,
        name: String,
        param: String,
        induc_from: Obj,
    ) -> Result<Stmt, RuntimeError> {
        self.validate_user_fn_param_names_for_parse(&[param.clone()], tb.line_file.clone())?;
        let dom_and_chain = self.parse_and_chain_atomic_fact(tb)?;
        Self::verify_have_fn_by_induc_dom_matches_induc_from(
            &dom_and_chain,
            &param,
            &induc_from,
            tb.line_file.clone(),
        )?;
        tb.skip_token(RIGHT_BRACE)?;
        let ret_set = self.parse_obj(tb)?;

        if !tb.current_token_is_equal_to(COLON) {
            return Err(
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "have fn by induc from: expected `:` before case blocks".to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            ))));
        }
        tb.skip_token(COLON)?;

        let num_blocks = tb.body.len();
        if num_blocks <= 1 {
            return Err(
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "have fn by induc from: expected at least two case blocks".to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            ))));
        }

        let num_special = num_blocks - 1;
        let mut special_cases_equal_tos: Vec<Obj> = Vec::with_capacity(num_special);

        let induc_from_is_number_obj = matches!(induc_from, Obj::Number(_));
        if induc_from_is_number_obj {
            if let Obj::Number(n) = &induc_from {
                if !number_is_in_z(n) {
                    return Err(
                        RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                format!(
                                "have fn by induc from: when `from` is a number literal, it must be an integer, got {}",
                                induc_from.to_string()
                            ),
                tb.line_file.clone(),
                None,
                vec![],
            ))));
                }
            }
        }

        for i in 0..num_special {
            let block = &mut tb.body[i];
            block.skip_token(CASE)?;

            block.skip_token(&param)?;

            block.skip_token(EQUAL)?;

            let slot_label = self.parse_obj(block)?;
            Self::verify_have_fn_by_induc_special_case_slot_label(
                &slot_label,
                i,
                block.line_file.clone(),
            )?;

            if induc_from_is_number_obj {
                let induc_from_add_i: Obj = Add::new(
                    induc_from.clone(),
                    Into::<Obj>::into(Number::new(i.to_string())),
                )
                .into();

                if !induc_from_add_i
                    .two_objs_can_be_calculated_and_equal_by_calculation(&slot_label)
                {
                    return Err(
                        RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                format!(
                                "have fn by induc from: when `from` is a number literal, special case must be `case {} = {}:` (`from` + {}), got {}",
                                param, induc_from_add_i.to_string(), i, slot_label.to_string()
                            ),
                block.line_file.clone(),
                None,
                vec![],
            ))));
                }
            } else {
                let induc_from_add_i: Obj = Add::new(
                    induc_from.clone(),
                    Into::<Obj>::into(Number::new(i.to_string())),
                )
                .into();

                if induc_from_add_i.to_string() != slot_label.to_string() {
                    return Err(
                        RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                format!(
                                "have fn by induc from: when `from` is not a number literal, special case must be `case {} = {}:`, got {}",
                                param, induc_from_add_i.to_string(), slot_label.to_string()
                            ),
                block.line_file.clone(),
                None,
                vec![],
            ))));
                }
            }

            block.skip_token(COLON)?;
            if !block.exceed_end_of_head() {
                special_cases_equal_tos.push(self.parse_obj(block)?);
            } else {
                return Err(
                    RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "have fn by induc from: special case must be `case <index>: <obj>` on one line"
                            .to_string(),
                block.line_file.clone(),
                None,
                vec![],
            ))));
            }
        }

        let induc_names_last = [param.clone()];
        let last_case_line = tb.body[num_blocks - 1].line_file.clone();
        let last_case = self.parse_in_local_free_param_scope(
            ParamObjType::Induc,
            &induc_names_last,
            last_case_line,
            |this| {
                let last_block = &mut tb.body[num_blocks - 1];
                last_block.skip_token(CASE)?;
                last_block.skip_token(&param)?;
                last_block.skip_token(GREATER_EQUAL)?;
                let last_bound = this.parse_obj(last_block)?;

                if induc_from_is_number_obj {
                    let induc_from_add_n: Obj = Add::new(
                        induc_from.clone(),
                        Into::<Obj>::into(Number::new(num_special.to_string())),
                    )
                    .into();
                    if !induc_from_add_n
                        .two_objs_can_be_calculated_and_equal_by_calculation(&last_bound)
                    {
                        return Err(
                            RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                format!(
                            "have fn by induc from: when `from` is a number literal, last case must be `case >= {}:` (`from` + {}), got {}",
                            induc_from_add_n.to_string(), num_special, last_bound.to_string()
                        ),
                last_block.line_file.clone(),
                None,
                vec![],
            ))));
                    }
                } else {
                    let induc_from_add_n: Obj = Add::new(
                        induc_from.clone(),
                        Into::<Obj>::into(Number::new(num_special.to_string())),
                    )
                    .into();
                    if induc_from_add_n.to_string() != last_bound.to_string() {
                        return Err(
                            RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                format!(
                            "have fn by induc from: when `from` is not a number literal, last case must be `case >= {}:`, got {}",
                            induc_from_add_n.to_string(), last_bound.to_string()
                        ),
                last_block.line_file.clone(),
                None,
                vec![],
            ))));
                    }
                }

                last_block.skip_token(COLON)?;

                if !last_block.exceed_end_of_head() {
                    let last_obj = this.parse_obj(last_block)?;
                    if !last_block.exceed_end_of_head() {
                        return Err(
                            RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "have fn by induc from: unexpected tokens after `obj` in last case"
                            .to_string(),
                last_block.line_file.clone(),
                None,
                vec![],
            ))));
                    }
                    if !last_block.body.is_empty() {
                        return Err(
                        RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "have fn by induc from: if last case has `:` and an object on the same line, it must not have a nested body"
                                .to_string(),
                last_block.line_file.clone(),
                None,
                vec![],
            ))));
                    }
                    Ok(HaveFnByInducLastCase::EqualTo(last_obj))
                } else if !last_block.body.is_empty() {
                    let mut nested: Vec<HaveFnByInducNestedCase> =
                        Vec::with_capacity(last_block.body.len());
                    for sub in last_block.body.iter_mut() {
                        sub.skip_token(CASE)?;
                        let w = this.parse_and_chain_atomic_fact(sub)?;
                        sub.skip_token(COLON)?;
                        if sub.exceed_end_of_head() {
                            return Err(
                        RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "have fn by induc from: nested case must be `case <when>: <obj>`"
                                .to_string(),
                sub.line_file.clone(),
                                None,
                                vec![],
            ))));
                        }
                        let o = this.parse_obj(sub)?;
                        if !sub.body.is_empty() {
                            return Err(
                        RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "have fn by induc from: nested case must not have further indentation"
                                .to_string(),
                sub.line_file.clone(),
                                None,
                                vec![],
            ))));
                        }
                        nested.push(HaveFnByInducNestedCase {
                            case_fact: w,
                            equal_to: o,
                        });
                    }
                    Ok(HaveFnByInducLastCase::NestedCases(nested))
                } else {
                    Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new(
                            None,
                            "have fn by induc from: last case must end with `: <obj>` or `:` with nested `case` blocks"
                                .to_string(),
                            last_block.line_file.clone(),
                            None,
                            vec![],
                        ),
                    )))
                }
            },
        )?;

        Ok(HaveFnByInducStmt::new(
            name,
            param,
            ret_set,
            induc_from,
            special_cases_equal_tos,
            last_case,
            tb.line_file.clone(),
        )
        .into())
    }

    fn verify_have_fn_by_induc_dom_matches_induc_from(
        when: &AndChainAtomicFact,
        param_name: &str,
        induc_from: &Obj,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        let ge = match when {
            AndChainAtomicFact::AtomicFact(AtomicFact::GreaterEqualFact(ge)) => ge,
            _ => {
                return Err(
                    RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "have fn by induc from: dom fact must be a single `>=` fact".to_string(),
                line_file,
                None,
                vec![],
            ))));
            }
        };
        match &ge.left {
            Obj::Identifier(id) if id.name == param_name => {}
            _ => {
                return Err(
                    RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "have fn by induc from: `>=` left must be the parameter name".to_string(),
                line_file,
                None,
                vec![],
            ))));
            }
        }
        if ge.right.to_string() != induc_from.to_string() {
            return Err(
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "have fn by induc from: `>=` right must match the object after `from`"
                        .to_string(),
                line_file,
                None,
                vec![],
            ))));
        }
        Ok(())
    }

    /// 特例行 `case <k>:`：`<k>` 须为自然数字面量，且等于该行在特例中的 **0-based 顺序**（第 1 条为 0，第 2 条为 1，…）。
    fn verify_have_fn_by_induc_special_case_slot_label(
        slot: &Obj,
        expected_index: usize,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        match slot {
            Obj::Number(n) => {
                if n.normalized_value == expected_index.to_string() {
                    Ok(())
                } else {
                    Err(
                        RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                format!(
                                "have fn by induc from: special case label must be `{}` (0-based index for this row), got {}",
                                expected_index, n.normalized_value
                            ),
                line_file,
                None,
                vec![],
            ))))
                }
            }
            _ => Err(
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "have fn by induc from: special case must be `case <natural>: <obj>` where <natural> is the 0-based index (0, 1, …)"
                        .to_string(),
                line_file,
                None,
                vec![],
            )))),
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

        self.register_collected_param_names_for_def_parse(&equal_tos, tb.line_file.clone())?;

        Ok(HaveByExistStmt::new(equal_tos, true_fact, tb.line_file.clone()).into())
    }

    /// Parses `{ params [: dom_facts] }` for `family`. Leaves a **Def** free-param scope open for the
    /// caller to parse `= obj` and then call `end_scope`.
    fn parse_braced_params_and_optional_dom_facts(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<(ParamDefWithType, Vec<OrAndChainAtomicFact>), RuntimeError> {
        tb.skip_token(LEFT_BRACE)?;
        let params_def_with_type =
            self.parse_def_param_type_groups_until_colon_or_right_brace(tb)?;
        let scope_names = params_def_with_type.collect_param_names();
        self.parsing_free_param_collection.begin_scope(
            ParamObjType::DefHeader,
            &scope_names,
            tb.line_file.clone(),
        )?;
        let dom_facts = if tb.current_token_is_equal_to(COLON) {
            tb.skip_token(COLON)?;
            let mut facts = vec![];
            let dom_result = loop {
                if tb.current()? == RIGHT_BRACE {
                    break Ok(facts);
                }
                match self.parse_or_and_chain_atomic_fact(tb) {
                    Ok(f) => facts.push(f),
                    Err(e) => {
                        self.parsing_free_param_collection
                            .end_scope(ParamObjType::DefHeader, &scope_names);
                        break Err(e);
                    }
                }
                if tb.current_token_is_equal_to(COMMA) {
                    tb.skip_token(COMMA)?;
                }
            };
            dom_result?
        } else {
            vec![]
        };
        if let Err(e) = tb.skip_token(RIGHT_BRACE) {
            self.parsing_free_param_collection
                .end_scope(ParamObjType::DefHeader, &scope_names);
            return Err(e);
        }
        Ok((params_def_with_type, dom_facts))
    }

    /// Like [`Self::parse_braced_params_and_optional_dom_facts`]: leaves **Def** scope open for the
    /// rest of `struct` (fields and `<=>` facts).
    fn parse_braced_struct_field_params_and_optional_dom_facts(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<(ParamDefWithType, Vec<OrAndChainAtomicFact>), RuntimeError> {
        tb.skip_token(LEFT_BRACE)?;
        let param_defs =
            self.parse_def_struct_header_param_groups_until_colon_or_right_brace(tb)?;
        let scope_names = param_defs.collect_param_names();
        self.parsing_free_param_collection.begin_scope(
            ParamObjType::DefHeader,
            &scope_names,
            tb.line_file.clone(),
        )?;
        let dom_facts = if tb.current_token_is_equal_to(COLON) {
            tb.skip_token(COLON)?;
            let mut facts = vec![];
            let dom_result = loop {
                if tb.current()? == RIGHT_BRACE {
                    break Ok(facts);
                }
                match self.parse_or_and_chain_atomic_fact(tb) {
                    Ok(f) => facts.push(f),
                    Err(e) => {
                        self.parsing_free_param_collection
                            .end_scope(ParamObjType::DefHeader, &scope_names);
                        break Err(e);
                    }
                }
                if tb.current_token_is_equal_to(COMMA) {
                    tb.skip_token(COMMA)?;
                }
            };
            dom_result?
        } else {
            vec![]
        };
        if let Err(e) = tb.skip_token(RIGHT_BRACE) {
            self.parsing_free_param_collection
                .end_scope(ParamObjType::DefHeader, &scope_names);
            return Err(e);
        }
        Ok((param_defs, dom_facts))
    }

    pub fn parse_def_family_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(FAMILY)?;
        let name = self.parse_name_and_insert_into_top_parsing_time_name_scope(tb)?;

        self.run_in_local_parsing_time_name_scope(move |this| {
            let (params_def_with_type, dom_facts) =
                this.parse_braced_params_and_optional_dom_facts(tb)?;
            let family_def_scope_names = params_def_with_type.collect_param_names();
            let stmt_result = (|| -> Result<Stmt, RuntimeError> {
                if !tb.current_token_is_equal_to(EQUAL) {
                    return Err(
                        RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "family definition expects `=` after `}`".to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            ))));
                }
                tb.skip_token(EQUAL)?;
                let equal_to = this.parse_obj(tb)?;
                Ok(DefFamilyStmt::new(
                    name,
                    params_def_with_type,
                    dom_facts,
                    equal_to,
                    tb.line_file.clone(),
                )
                .into())
            })();
            this.parsing_free_param_collection
                .end_scope(ParamObjType::DefHeader, &family_def_scope_names);
            stmt_result
        })
    }

    pub fn parse_def_struct_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(STRUCT)?;
        let name = self.parse_name_and_insert_into_top_parsing_time_name_scope(tb)?;

        self.run_in_local_parsing_time_name_scope(move |this| {
            let (param_defs, dom_facts) =
                this.parse_braced_struct_field_params_and_optional_dom_facts(tb)?;
            let struct_def_scope_names = param_defs.collect_param_names();
            let stmt_result = (|| -> Result<Stmt, RuntimeError> {
                if tb.current_token_is_equal_to(EQUAL) {
                    return Err(RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "use `family` for set-style definitions (`... {} = ...`); `struct` requires field definitions after `:`"
                        .to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            ))));
                }
                tb.skip_token(COLON)?;

                if tb.body.is_empty() {
                    return Err(
                        RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "struct with fields expects body".to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            ))));
                }

                let mut fields: Vec<(String, ParamType)> = vec![];
                let mut facts: Vec<OrAndChainAtomicFact> = vec![];

                let body_len = tb.body.len();
                let last_index = body_len - 1;
                let last_is_equiv = {
                    let last = tb.body.get(last_index).ok_or_else(|| {
                        RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "Expected body".to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            )))
                    })?;
                    last.current_token_is_equal_to(EQUIVALENT_SIGN)
                };

                let field_end = if last_is_equiv { last_index } else { body_len };

                for i in 0..field_end {
                    let block = tb.body.get_mut(i).ok_or_else(|| {
                        RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "Expected field block".to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            )))
                    })?;
                    let field_name = block.advance()?;
                    let pt = this.parse_param_type(block)?;
                    this.reject_nested_struct_param_type(&pt, block.line_file.clone())?;
                    fields.push((field_name, pt));
                }

                let mut seen = HashSet::new();
                for (field_name, _) in fields.iter() {
                    if !seen.insert(field_name.clone()) {
                        return Err(
                            RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                format!("struct `{}`: duplicate field `{}`", name, field_name),
                tb.line_file.clone(),
                None,
                vec![],
            ))));
                    }
                }

                if fields.len() <= 1 {
                    return Err(
                        RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "struct with fields expects at least two fields".to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            ))));
                }

                if last_is_equiv {
                    let last = tb.body.get_mut(last_index).ok_or_else(|| {
                        RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "Expected <=>: block".to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            )))
                    })?;
                    last.skip_token_and_colon_and_exceed_end_of_head(EQUIVALENT_SIGN)?;
                    let field_names: Vec<String> =
                        fields.iter().map(|(n, _)| n.clone()).collect();
                    this.parsing_free_param_collection.begin_scope(
                        ParamObjType::StructSelf,
                        &field_names,
                        tb.line_file.clone(),
                    )?;
                    for block in last.body.iter_mut() {
                        facts.push(this.parse_or_and_chain_atomic_fact(block)?);
                    }
                    this.parsing_free_param_collection
                        .end_scope(ParamObjType::StructSelf, &field_names);
                }

                Ok(DefStructStmt::new(
                    name,
                    param_defs,
                    dom_facts,
                    fields,
                    facts,
                    tb.line_file.clone(),
                )
                .into())
            })();
            this.parsing_free_param_collection
                .end_scope(ParamObjType::DefHeader, &struct_def_scope_names);
            stmt_result
        })
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
                self.parse_param_def_with_param_type_and_skip_comma_impl(tb, true)?,
            );
        }
        tb.skip_token(RIGHT_BRACE)?;
        let param_defs = ParamDefWithType::new(groups);
        let names = param_defs.collect_param_names();
        self.register_collected_param_names_for_def_parse(&names, tb.line_file.clone())?;
        Ok(param_defs)
    }

    /// After `{` is consumed: param-type groups until `:` or `}` (family / struct header); registers names.
    fn parse_def_param_type_groups_until_colon_or_right_brace(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<ParamDefWithType, RuntimeError> {
        let mut groups = vec![];
        while tb.current()? != COLON && tb.current()? != RIGHT_BRACE {
            groups.push(self.parse_param_def_with_param_type_and_skip_comma(tb)?);
        }
        let params_def_with_type = ParamDefWithType::new(groups);
        let param_names = params_def_with_type.collect_param_names();
        self.register_collected_param_names_for_def_parse(&param_names, tb.line_file.clone())?;
        Ok(params_def_with_type)
    }

    /// After `{` is consumed: struct header param groups until `:` or `}`; no nested `struct` type; registers names.
    fn parse_def_struct_header_param_groups_until_colon_or_right_brace(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<ParamDefWithType, RuntimeError> {
        let mut groups = vec![];
        while tb.current()? != COLON && tb.current()? != RIGHT_BRACE {
            let def = self.parse_param_def_with_param_type_and_skip_comma(tb)?;
            self.reject_nested_struct_param_type(&def.param_type, tb.line_file.clone())?;
            groups.push(def);
        }
        let param_defs = ParamDefWithType::new(groups);
        let param_names = param_defs.collect_param_names();
        self.register_collected_param_names_for_def_parse(&param_names, tb.line_file.clone())?;
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
}
