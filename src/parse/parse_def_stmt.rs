use crate::prelude::*;
use crate::stmt::definition_stmt::induc_obj_plus_offset;
use std::collections::HashSet;

impl Runtime {
    pub fn parse_def_prop_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        self.push_parsing_time_name_scope();
        let stmt = self.parse_def_prop_stmt_body(tb);
        self.pop_parsing_time_name_scope();

        let stmt_ok = stmt?;
        self.insert_parsed_name_into_top_parsing_time_name_scope(
            &stmt_ok.name,
            tb.line_file.clone(),
        )?;

        Ok(Stmt::DefPropStmt(stmt_ok))
    }

    fn parse_def_prop_stmt_body(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<DefPropStmt, RuntimeError> {
        tb.skip_token(PROP)?;
        let name = self.parse_name_and_insert_into_top_parsing_time_name_scope(tb)?;
        let param_defs = self.parse_def_braced_param_groups_with_param_type(tb)?;

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
        self.insert_parsed_name_into_top_parsing_time_name_scope(
            &stmt_ok.name,
            tb.line_file.clone(),
        )?;
        Ok(Stmt::DefAbstractPropStmt(stmt_ok))
    }

    fn parse_def_abstract_prop_stmt_body(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<DefAbstractPropStmt, RuntimeError> {
        tb.skip_token(ABSTRACT_PROP)?;
        let name = self.parse_name_and_insert_into_top_parsing_time_name_scope(tb)?;
        tb.skip_token(LEFT_BRACE)?;
        let mut params = vec![];
        while tb.current()? != RIGHT_BRACE {
            params.push(tb.advance()?);
            if !tb.current_token_is_equal_to(RIGHT_BRACE) {
                tb.skip_token(COMMA)?;
            }
        }
        tb.skip_token(RIGHT_BRACE)?;

        self.register_collected_param_names_for_def_parse(&params, tb.line_file.clone())?;

        Ok(DefAbstractPropStmt::new(name, params, tb.line_file.clone()))
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
        let all_param_names = ParamGroupWithParamType::collect_param_names(&param_def);
        self.register_collected_param_names_for_def_parse(&all_param_names, tb.line_file.clone())?;
        Ok(Stmt::DefLetStmt(DefLetStmt::new(
            param_def,
            facts,
            tb.line_file.clone(),
        )))
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
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "have expects at least one param type pair".to_string(),
                    tb.line_file.clone(),
                    None,
                ),
            );
        }
        let have_param_names = ParamGroupWithParamType::collect_param_names(&param_defs);
        self.register_collected_param_names_for_def_parse(&have_param_names, tb.line_file.clone())?;

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
        tb.skip_token(FN)?;
        if tb.current_token_is_equal_to(BY) {
            tb.skip_token(BY)?;
            self.parse_have_fn_by_induc_stmt(tb)
        } else {
            let name = self.parse_name_and_insert_into_top_parsing_time_name_scope(tb)?;

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
                    HaveFnEqualCaseByCaseStmt::new(
                        name,
                        fs,
                        cases,
                        equal_tos,
                        tb.line_file.clone(),
                    ),
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
    }

    /// `have fn by` 已消费；解析 `induc from <Obj>: <name> { ... } ret = : case ...`。
    /// 前若干条须为 `param = from`, `param = from + 1`, …；最后一条须为 `param >= induc_from + n`（n 为特殊 case 个数）；
    /// 且要么行末 `: obj`，要么 `:` 后换行跟子块 `case when: obj`。
    fn parse_have_fn_by_induc_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(INDUC)?;
        tb.skip_token(FROM)?;
        let induc_from = self.parse_obj(tb)?;
        tb.skip_token(COLON)?;
        let name = self.parse_name_and_insert_into_top_parsing_time_name_scope(tb)?;
        let fs = self.parse_fn_set_with_dom_without_fn_prefix(tb)?;
        tb.skip_token(EQUAL)?;
        if !tb.current_token_is_equal_to(COLON) {
            return Err(
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "have fn by induc from ...: expected '=' ':' before case blocks".to_string(),
                    tb.line_file.clone(),
                    None,
                ),
            );
        }
        tb.skip_token(COLON)?;

        let num_blocks = tb.body.len();
        if num_blocks < 1 {
            return Err(
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "have fn by induc from: expected at least one case block".to_string(),
                    tb.line_file.clone(),
                    None,
                ),
            );
        }

        Self::verify_have_fn_by_induc_fn_set_constraints(&fs, &induc_from, tb.line_file.clone())?;
        let param_name = fs.params_def_with_set[0].params[0].clone();

        let num_special = num_blocks - 1;
        let mut special_cases_equal_tos: Vec<Obj> = Vec::with_capacity(num_special);

        for i in 0..num_special {
            let block = &mut tb.body[i];
            block.skip_token(CASE)?;
            let when = self.parse_and_chain_atomic_fact(block)?;
            block.skip_token(COLON)?;
            Self::verify_have_fn_by_induc_special_case_when(
                &when,
                &param_name,
                &induc_from,
                i,
                block.line_file.clone(),
            )?;
            if !block.exceed_end_of_head() {
                special_cases_equal_tos.push(self.parse_obj(block)?);
            } else {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "have fn by induc from: special case must be `case param = from + k: <obj>` on one line"
                            .to_string(),
                        block.line_file.clone(),
                        None,
                    ),
                );
            }
            if !block.exceed_end_of_head() {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "have fn by induc from: unexpected tokens after `obj` in special case"
                            .to_string(),
                        block.line_file.clone(),
                        None,
                    ),
                );
            }
            if !block.body.is_empty() {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "have fn by induc from: special case must not have a nested body under `case`"
                            .to_string(),
                        block.line_file.clone(),
                        None,
                    ),
                );
            }
        }

        let last_block = &mut tb.body[num_blocks - 1];
        last_block.skip_token(CASE)?;
        let last_when = self.parse_and_chain_atomic_fact(last_block)?;
        last_block.skip_token(COLON)?;
        Self::verify_have_fn_by_induc_last_greater_equal_when(
            &last_when,
            &param_name,
            &induc_from,
            num_special,
            last_block.line_file.clone(),
        )?;

        let (last_case_equal_to, last_case_cases) = if !last_block.exceed_end_of_head() {
            let last_obj = self.parse_obj(last_block)?;
            if !last_block.exceed_end_of_head() {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "have fn by induc from: unexpected tokens after `obj` in last case"
                            .to_string(),
                        last_block.line_file.clone(),
                        None,
                    ),
                );
            }
            if !last_block.body.is_empty() {
                return Err(
                        RuntimeError::new_parse_error_with_msg_position_previous_error(
                            "have fn by induc from: if last case has `:` and an object on the same line, it must not have a nested body"
                                .to_string(),
                            last_block.line_file.clone(),
                            None,
                        ),
                    );
            }
            (Some(last_obj), None)
        } else if !last_block.body.is_empty() {
            let mut nested: Vec<(AndChainAtomicFact, Obj)> =
                Vec::with_capacity(last_block.body.len());
            for sub in last_block.body.iter_mut() {
                sub.skip_token(CASE)?;
                let w = self.parse_and_chain_atomic_fact(sub)?;
                sub.skip_token(COLON)?;
                if sub.exceed_end_of_head() {
                    return Err(
                        RuntimeError::new_parse_error_with_msg_position_previous_error(
                            "have fn by induc from: nested case must be `case <when>: <obj>`"
                                .to_string(),
                            sub.line_file.clone(),
                            None,
                        ),
                    );
                }
                let o = self.parse_obj(sub)?;
                if !sub.body.is_empty() {
                    return Err(
                        RuntimeError::new_parse_error_with_msg_position_previous_error(
                            "have fn by induc from: nested case must not have further indentation"
                                .to_string(),
                            sub.line_file.clone(),
                            None,
                        ),
                    );
                }
                nested.push((w, o));
            }
            (None, Some(nested))
        } else {
            return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "have fn by induc from: last case must end with `: <obj>` or `:` with nested `case` blocks"
                            .to_string(),
                        last_block.line_file.clone(),
                        None,
                    ),
                );
        };

        Ok(Stmt::HaveFnByInducStmt(HaveFnByInducStmt::new(
            name,
            fs,
            induc_from,
            special_cases_equal_tos,
            last_case_equal_to,
            last_case_cases,
            tb.line_file.clone(),
        )))
    }

    fn verify_have_fn_by_induc_special_case_when(
        when: &AndChainAtomicFact,
        param_name: &str,
        induc_from: &Obj,
        index: usize,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        let eq = match when {
            AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)) => eq,
            AndChainAtomicFact::AndFact(af) if af.facts.len() == 1 => match &af.facts[0] {
                AtomicFact::EqualFact(eq) => eq,
                _ => {
                    return Err(
                        RuntimeError::new_parse_error_with_msg_position_previous_error(
                            "have fn by induc from: special case `when` must be `param = from + k`"
                                .to_string(),
                            line_file,
                            None,
                        ),
                    );
                }
            },
            _ => {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "have fn by induc from: special case `when` must be `param = from + k`"
                            .to_string(),
                        line_file,
                        None,
                    ),
                );
            }
        };
        match &eq.left {
            Obj::Identifier(id) if id.name == param_name => {}
            _ => {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "have fn by induc from: special case equality left must be the parameter name"
                            .to_string(),
                        line_file,
                        None,
                    ),
                );
            }
        }
        let expected = induc_obj_plus_offset(induc_from, index);
        if eq.right.to_string() != expected.to_string() {
            return Err(
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    format!(
                        "have fn by induc from: special case {} must be `param = {}` (got {})",
                        index, expected, eq.right
                    ),
                    line_file,
                    None,
                ),
            );
        }
        Ok(())
    }

    fn verify_have_fn_by_induc_last_greater_equal_when(
        when: &AndChainAtomicFact,
        param_name: &str,
        induc_from: &Obj,
        len_special: usize,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        let ge = match when {
            AndChainAtomicFact::AtomicFact(AtomicFact::GreaterEqualFact(ge)) => ge,
            AndChainAtomicFact::AndFact(af) if af.facts.len() == 1 => match &af.facts[0] {
                AtomicFact::GreaterEqualFact(ge) => ge,
                _ => {
                    return Err(
                        RuntimeError::new_parse_error_with_msg_position_previous_error(
                            "have fn by induc from: last case `when` must be `param >= induc_from + <len_of_special_cases>`"
                                .to_string(),
                            line_file,
                            None,
                        ),
                    );
                }
            },
            _ => {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "have fn by induc from: last case `when` must be `param >= induc_from + <len_of_special_cases>`"
                            .to_string(),
                        line_file,
                        None,
                    ),
                );
            }
        };
        match &ge.left {
            Obj::Identifier(id) if id.name == param_name => {}
            _ => {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "have fn by induc from: last case `>=` left must be the parameter name"
                            .to_string(),
                        line_file,
                        None,
                    ),
                );
            }
        }
        let expected = induc_obj_plus_offset(induc_from, len_special);
        if ge.right.to_string() != expected.to_string() {
            return Err(
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    format!(
                        "have fn by induc from: last case must be `{} >= {}` (got right-hand side {})",
                        param_name, expected, ge.right
                    ),
                    line_file,
                    None,
                ),
            );
        }
        Ok(())
    }

    /// `have fn by induc from`：要求 fn 只有一个参数、参数域为 `Z`、恰有一条 dom，且为 `param >= from_obj`（`from_obj` 与 `from` 子句解析结果一致）。
    fn verify_have_fn_by_induc_fn_set_constraints(
        fs: &FnSet,
        induc_from: &Obj,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        if fs.params_def_with_set.len() != 1 {
            return Err(
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "have fn by induc from: expected exactly one parameter group".to_string(),
                    line_file,
                    None,
                ),
            );
        }
        let group = &fs.params_def_with_set[0];
        if group.params.len() != 1 {
            return Err(
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "have fn by induc from: expected exactly one parameter".to_string(),
                    line_file,
                    None,
                ),
            );
        }
        if !matches!(group.set, Obj::StandardSet(StandardSet::Z)) {
            return Err(
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "have fn by induc from: parameter domain must be Z".to_string(),
                    line_file,
                    None,
                ),
            );
        }
        if fs.dom_facts.len() != 1 {
            return Err(
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "have fn by induc from: expected exactly one dom fact".to_string(),
                    line_file,
                    None,
                ),
            );
        }
        let ge = match &fs.dom_facts[0] {
            OrAndChainAtomicFact::AtomicFact(AtomicFact::GreaterEqualFact(ge)) => ge,
            _ => {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "have fn by induc from: dom fact must be a single >= fact".to_string(),
                        line_file,
                        None,
                    ),
                );
            }
        };
        let param_name = &group.params[0];
        match &ge.left {
            Obj::Identifier(id) => {
                if id.name != *param_name {
                    return Err(
                        RuntimeError::new_parse_error_with_msg_position_previous_error(
                            "have fn by induc from: >= fact left must be the parameter name"
                                .to_string(),
                            line_file,
                            None,
                        ),
                    );
                }
            }
            _ => {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "have fn by induc from: >= fact left must be the parameter name"
                            .to_string(),
                        line_file,
                        None,
                    ),
                );
            }
        }
        if ge.right.to_string() != induc_from.to_string() {
            return Err(
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "have fn by induc from: >= fact right must match the object after `from`"
                        .to_string(),
                    line_file,
                    None,
                ),
            );
        }
        Ok(())
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

        Ok(Stmt::HaveExistObjStmt(HaveExistObjStmt::new(
            equal_tos,
            true_fact,
            tb.line_file.clone(),
        )))
    }

    fn parse_braced_params_and_optional_dom_facts(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<(Vec<ParamGroupWithParamType>, Vec<OrAndChainAtomicFact>), RuntimeError> {
        tb.skip_token(LEFT_BRACE)?;
        let params_def_with_type =
            self.parse_def_param_type_groups_until_colon_or_right_brace(tb)?;
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
    ) -> Result<
        (
            Vec<ParamGroupWithStructFieldType>,
            Vec<OrAndChainAtomicFact>,
        ),
        RuntimeError,
    > {
        tb.skip_token(LEFT_BRACE)?;
        let param_defs = self.parse_def_struct_field_groups_until_colon_or_right_brace(tb)?;
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
        let name = self.parse_name_and_insert_into_top_parsing_time_name_scope(tb)?;

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

    pub fn parse_def_struct_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(STRUCT)?;
        let name = self.parse_name_and_insert_into_top_parsing_time_name_scope(tb)?;

        self.push_parsing_time_name_scope();
        let stmt = self.parse_def_struct_stmt_body(name, tb);
        self.pop_parsing_time_name_scope();
        stmt
    }

    fn parse_def_struct_stmt_body(
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

        Ok(Stmt::DefStructStmt(DefStructStmt::new(
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

impl Runtime {
    pub(crate) fn register_collected_param_names_for_def_parse(
        &mut self,
        names: &Vec<String>,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        self.validate_names_and_insert_into_top_parsing_time_name_scope(names, line_file.clone())
            .map_err(|e| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    String::new(),
                    line_file,
                    Some(e),
                )
            })
    }

    /// `prop name` / similar: consumes `{` … `}` of `ParamGroupWithParamType` entries and registers names.
    fn parse_def_braced_param_groups_with_param_type(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Vec<ParamGroupWithParamType>, RuntimeError> {
        tb.skip_token(LEFT_BRACE)?;
        let mut param_defs = Vec::new();
        while tb.current()? != RIGHT_BRACE {
            param_defs.push(self.parse_param_def_with_param_type_and_skip_comma(tb)?);
        }
        tb.skip_token(RIGHT_BRACE)?;
        let names = ParamGroupWithParamType::collect_param_names(&param_defs);
        self.register_collected_param_names_for_def_parse(&names, tb.line_file.clone())?;
        Ok(param_defs)
    }

    /// After `{` is consumed: param-type groups until `:` or `}` (family / struct header); registers names.
    fn parse_def_param_type_groups_until_colon_or_right_brace(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Vec<ParamGroupWithParamType>, RuntimeError> {
        let mut params_def_with_type = vec![];
        while tb.current()? != COLON && tb.current()? != RIGHT_BRACE {
            params_def_with_type.push(self.parse_param_def_with_param_type_and_skip_comma(tb)?);
        }
        let param_names = ParamGroupWithParamType::collect_param_names(&params_def_with_type);
        self.register_collected_param_names_for_def_parse(&param_names, tb.line_file.clone())?;
        Ok(params_def_with_type)
    }

    /// After `{` is consumed: struct-field param groups until `:` or `}`; registers names.
    fn parse_def_struct_field_groups_until_colon_or_right_brace(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Vec<ParamGroupWithStructFieldType>, RuntimeError> {
        let mut param_defs = vec![];
        while tb.current()? != COLON && tb.current()? != RIGHT_BRACE {
            param_defs.push(self.parse_param_def_with_struct_field_type_and_skip_comma(tb)?);
        }
        let param_names = ParamGroupWithStructFieldType::collect_param_names(&param_defs);
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
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    RuntimeError::message_text_for_duplicate_used_name_without_line_file(name),
                    line_file,
                    Some(e),
                )
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
