use super::TokenBlock;
use crate::common::keywords::{
    ALGO, CASE, COLON, COMMA, EQUAL, EQUIVALENT_SIGN, FN_FOR_FN_WITH_PARAMS, HAVE, LEFT_BRACE, LET,
    PROP, RIGHT_BRACE, STRUCT,
};
use crate::error::ParsingError;
use crate::error::{duplicate_used_name_error_message, RuntimeError};
use crate::execute::Runtime;
use crate::fact::{AndChainAtomicFact, OrAndChainAtomicFact};
use crate::stmt::define_algorithm_stmt::{AlgoCase, AlgoReturn, AlgoReturnOrAlgoCase, DefAlgoStmt};
use crate::stmt::definition_stmt::{
    DefLetStmt, DefPropWithMeaningStmt, DefPropWithoutMeaningStmt, DefStructWithFieldsStmt,
    DefStructWithNoFieldStmt, HaveExistObjStmt, HaveFnEqualCaseByCaseStmt, HaveFnEqualStmt,
    HaveObjEqualStmt, HaveObjInNonemptySetOrParamTypeStmt,
};
use crate::stmt::parameter_def::ParamDefWithParamType;
use crate::stmt::Stmt;

impl<'a> Runtime<'a> {
    pub fn parse_def_prop_with_meaning_stmt_or_prop_without_meaning(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, ParsingError> {
        if tb.token_at_end_of_head() != COLON {
            return self.parse_def_prop_without_meaning_stmt(tb);
        } else {
            self.parse_def_prop_with_meaning_stmt(tb)
        }
    }

    pub fn parse_def_prop_with_meaning_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, ParsingError> {
        self.push_parsing_time_name_scope();
        let stmt = self.parse_def_prop_with_meaning_stmt_body(tb);
        self.pop_parsing_time_name_scope();

        let stmt_ok = stmt?;
        self.validate_name_and_insert_into_top_parsing_time_name_scope(&stmt_ok.name, tb.line_file)
            .map_err(|e| {
                ParsingError::new(
                    duplicate_used_name_error_message(&stmt_ok.name),
                    tb.line_file,
                    Some(RuntimeError::ParseBlockError(e)),
                )
            })?;
        Ok(Stmt::DefPropWithMeaningStmt(stmt_ok))
    }

    fn parse_def_prop_with_meaning_stmt_body(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<DefPropWithMeaningStmt, ParsingError> {
        tb.skip_token(PROP)?;
        let name = tb.advance()?;
        self.validate_name_and_insert_into_top_parsing_time_name_scope(&name, tb.line_file)
            .map_err(|e| {
                ParsingError::new(
                    duplicate_used_name_error_message(&name),
                    tb.line_file,
                    Some(RuntimeError::ParseBlockError(e)),
                )
            })?;
        tb.skip_token(LEFT_BRACE)?;
        let mut param_defs: Vec<ParamDefWithParamType> = vec![];
        while tb.current()? != RIGHT_BRACE {
            param_defs.push(self.param_def_with_type(tb)?);
        }
        tb.skip_token(RIGHT_BRACE)?;
        let all_param_names = ParamDefWithParamType::collect_param_names(&param_defs);
        self.validate_names_and_insert_into_top_parsing_time_name_scope(
            &all_param_names,
            tb.line_file,
        )
        .map_err(|e| ParsingError::new(e.to_string(), tb.line_file, None))?;
        let facts = self.parse_facts_in_body(tb)?;
        Ok(DefPropWithMeaningStmt::new(
            name,
            param_defs,
            facts,
            tb.line_file,
        ))
    }

    pub fn parse_def_prop_without_meaning_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, ParsingError> {
        self.push_parsing_time_name_scope();
        let stmt = self.parse_def_prop_without_meaning_stmt_body(tb);
        self.pop_parsing_time_name_scope();

        let stmt_ok = stmt?;
        self.validate_name_and_insert_into_top_parsing_time_name_scope(&stmt_ok.name, tb.line_file)
            .map_err(|e| {
                ParsingError::new(
                    duplicate_used_name_error_message(&stmt_ok.name),
                    tb.line_file,
                    Some(RuntimeError::ParseBlockError(e)),
                )
            })?;
        Ok(Stmt::DefPropWithoutMeaningStmt(stmt_ok))
    }

    fn parse_def_prop_without_meaning_stmt_body(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<DefPropWithoutMeaningStmt, ParsingError> {
        tb.skip_token(PROP)?;
        let name = tb.advance()?;
        self.validate_name_and_insert_into_top_parsing_time_name_scope(&name, tb.line_file)
            .map_err(|e| {
                ParsingError::new(
                    duplicate_used_name_error_message(&name),
                    tb.line_file,
                    Some(RuntimeError::ParseBlockError(e)),
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

        self.validate_names_and_insert_into_top_parsing_time_name_scope(&params, tb.line_file)
            .map_err(|e| ParsingError::new(e.to_string(), tb.line_file, None))?;

        Ok(DefPropWithoutMeaningStmt::new(name, params, tb.line_file))
    }

    pub fn parse_def_let_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(LET)?;
        let mut param_def: Vec<ParamDefWithParamType> = vec![];
        loop {
            match tb.current() {
                Ok(t) if t == COLON => break,
                Err(_) => break,
                Ok(_) => {}
            }
            param_def.push(self.parse_param_def_with_param_type(tb)?);
            if matches!(tb.current(), Ok(t) if t == COMMA) {
                tb.skip_token(COMMA)?;
            }
        }
        let facts = if tb.current().map(|c| c == COLON).unwrap_or(false) {
            tb.skip_token(COLON)?;
            self.parse_facts_in_body(tb)?
        } else {
            vec![]
        };
        let all_param_names = ParamDefWithParamType::collect_param_names(&param_def);
        self.validate_names_and_insert_into_top_parsing_time_name_scope(
            &all_param_names,
            tb.line_file,
        )
        .map_err(|e| ParsingError::new(e.to_string(), tb.line_file, None))?;
        Ok(Stmt::DefLetStmt(DefLetStmt::new(
            param_def,
            facts,
            tb.line_file,
        )))
    }

    // return HaveObjInNonemptySetOrParamTypeStmt or HaveObjEqualStmt
    pub fn parse_have_obj_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(HAVE)?;
        let mut param_defs: Vec<ParamDefWithParamType> = vec![];
        loop {
            param_defs.push(self.parse_param_def_with_param_type(tb)?);
            if !matches!(tb.current(), Ok(t) if t == COMMA) {
                break;
            }
            tb.skip_token(COMMA)?;
        }
        if param_defs.is_empty() {
            return Err(ParsingError::new(
                "have expects at least one param type pair".to_string(),
                tb.line_file,
                None,
            ));
        }
        let have_param_names = ParamDefWithParamType::collect_param_names(&param_defs);
        self.validate_names_and_insert_into_top_parsing_time_name_scope(
            &have_param_names,
            tb.line_file,
        )
        .map_err(|e| ParsingError::new(e.to_string(), tb.line_file, None))?;

        if tb.current().map(|t| t != EQUAL).unwrap_or(true) {
            Ok(Stmt::HaveObjInNonemptySetStmt(
                HaveObjInNonemptySetOrParamTypeStmt::new(param_defs, tb.line_file),
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
                tb.line_file,
            )))
        }
    }

    pub fn parse_have_fn_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(HAVE)?;
        tb.skip_token(FN_FOR_FN_WITH_PARAMS)?;
        let name = tb.advance()?;

        self.validate_name_and_insert_into_top_parsing_time_name_scope(&name, tb.line_file)
            .map_err(|e| {
                ParsingError::new(
                    duplicate_used_name_error_message(&name),
                    tb.line_file,
                    Some(RuntimeError::ParseBlockError(e)),
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
                HaveFnEqualCaseByCaseStmt::new(name, fs, cases, equal_tos, tb.line_file),
            ))
        } else {
            let equal_to = self.parse_obj(tb)?;
            Ok(Stmt::HaveFnEqualStmt(HaveFnEqualStmt::new(
                name,
                fs,
                equal_to,
                tb.line_file,
            )))
        }
    }

    pub fn parse_have_exist(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(HAVE)?;

        let true_fact = self.parse_exist_fact(tb)?;

        tb.skip_token(COLON)?;

        let mut equal_tos = vec![];
        while !tb.exceed_end_of_head() {
            equal_tos.push(tb.advance()?);
            if tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
            }
        }

        self.validate_names_and_insert_into_top_parsing_time_name_scope(&equal_tos, tb.line_file)
            .map_err(|e| ParsingError::new(e.to_string(), tb.line_file, None))?;

        Ok(Stmt::HaveExistObjStmt(HaveExistObjStmt::new(
            equal_tos,
            true_fact,
            tb.line_file,
        )))
    }

    pub fn parse_def_struct_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(STRUCT)?;
        let name = tb.advance()?;
        self.validate_name_and_insert_into_top_parsing_time_name_scope(&name, tb.line_file)
            .map_err(|e| {
                ParsingError::new(
                    duplicate_used_name_error_message(&name),
                    tb.line_file,
                    Some(RuntimeError::ParseBlockError(e)),
                )
            })?;

        self.push_parsing_time_name_scope();
        let stmt = self.parse_def_struct_stmt_body(name, tb);
        self.pop_parsing_time_name_scope();
        stmt
    }

    fn parse_def_struct_stmt_body(
        &mut self,
        name: String,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, ParsingError> {
        tb.skip_token(LEFT_BRACE)?;
        let mut params_def_with_type: Vec<ParamDefWithParamType> = vec![];
        while tb.current()? != COLON && tb.current()? != RIGHT_BRACE {
            params_def_with_type.push(self.parse_param_def_with_param_type(tb)?);
            if tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
            }
        }
        let struct_param_names = ParamDefWithParamType::collect_param_names(&params_def_with_type);
        self.validate_names_and_insert_into_top_parsing_time_name_scope(
            &struct_param_names,
            tb.line_file,
        )
        .map_err(|e| ParsingError::new(e.to_string(), tb.line_file, None))?;
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
        if tb.current_token_is_equal_to(EQUAL) {
            tb.skip_token(EQUAL)?;
            let equal_to = self.parse_obj(tb)?;
            Ok(Stmt::DefStructWithNoFieldStmt(
                DefStructWithNoFieldStmt::new(
                    name,
                    params_def_with_type,
                    dom_facts,
                    equal_to,
                    tb.line_file,
                ),
            ))
        } else {
            tb.skip_token(COLON)?;

            if tb.body.is_empty() {
                return Err(ParsingError::new(
                    "struct with fields expects body".to_string(),
                    tb.line_file,
                    None,
                ));
            }

            let mut fields: Vec<(String, OrAndChainAtomicFact)> = vec![];
            let mut facts: Vec<OrAndChainAtomicFact> = vec![];

            let body_len = tb.body.len();
            let last_index = body_len - 1;
            let last_is_equiv = {
                let last = tb.body.get(last_index).ok_or_else(|| {
                    ParsingError::new("Expected body".to_string(), tb.line_file, None)
                })?;
                last.token_at_end_of_head() == EQUIVALENT_SIGN
            };

            let field_end = if last_is_equiv { last_index } else { body_len };

            for i in 0..field_end {
                let block = tb.body.get_mut(i).ok_or_else(|| {
                    ParsingError::new("Expected field block".to_string(), tb.line_file, None)
                })?;
                let field_name = block.advance()?;
                let cond = self.parse_or_and_chain_atomic_fact(block)?;
                fields.push((field_name, cond));
            }

            if last_is_equiv {
                let last = tb.body.get_mut(last_index).ok_or_else(|| {
                    ParsingError::new("Expected <=>: block".to_string(), tb.line_file, None)
                })?;
                last.skip_token_and_colon_and_exceed_end_of_head(EQUIVALENT_SIGN)?;
                for block in last.body.iter_mut() {
                    facts.push(self.parse_or_and_chain_atomic_fact(block)?);
                }
            }

            Ok(Stmt::DefStructWithFieldsStmt(DefStructWithFieldsStmt::new(
                name,
                params_def_with_type,
                fields,
                facts,
                tb.line_file,
            )))
        }
    }

    pub fn parse_def_algorithm_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(ALGO)?;
        let name = tb.advance()?;
        self.validate_name_and_insert_into_top_parsing_time_name_scope(&name, tb.line_file)
            .map_err(|e| {
                ParsingError::new(
                    duplicate_used_name_error_message(&name),
                    tb.line_file,
                    Some(RuntimeError::ParseBlockError(e)),
                )
            })?;

        self.push_parsing_time_name_scope();
        let stmt = self.parse_def_algorithm_stmt_body(name, tb);
        self.pop_parsing_time_name_scope();
        stmt
    }

    fn parse_def_algorithm_stmt_body(
        &mut self,
        name: String,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, ParsingError> {
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
        let mut return_or_algo_case: Vec<AlgoReturnOrAlgoCase> = vec![];
        for block in tb.body.iter_mut() {
            let item = if block.current()? == CASE {
                AlgoReturnOrAlgoCase::AlgoCase(self.parse_algo_case(block)?)
            } else {
                AlgoReturnOrAlgoCase::AlgoReturn(self.parse_algo_return(block)?)
            };

            return_or_algo_case.push(item);
        }
        Ok(Stmt::DefAlgoStmt(DefAlgoStmt::new(
            name,
            params,
            return_or_algo_case,
            tb.line_file,
        )))
    }

    /// head 里是 if and_spec_fact :，body 有且只有一个块，即 return obj。
    fn parse_algo_case(&mut self, block: &mut TokenBlock) -> Result<AlgoCase, ParsingError> {
        block.skip_token(CASE)?;
        let condition = self.parse_and_chain_atomic_fact(block)?;
        block.skip_token(COLON)?;
        if !block.exceed_end_of_head() {
            return Err(ParsingError::new(
                "algo if: expected end of head after condition".to_string(),
                block.line_file,
                None,
            ));
        }
        if block.body.len() != 1 {
            return Err(ParsingError::new(
                "algo if block must have exactly one body block (return stmt)".to_string(),
                block.line_file,
                None,
            ));
        }

        let block = block.body.first_mut().ok_or_else(|| {
            ParsingError::new(
                "algo if block must have exactly one body block (return stmt)".to_string(),
                block.line_file,
                None,
            )
        })?;

        let return_stmt = self.parse_algo_return(block)?;
        Ok(AlgoCase::new(condition, return_stmt, block.line_file))
    }

    /// head 里是 return，后跟 obj。
    fn parse_algo_return(&mut self, block: &mut TokenBlock) -> Result<AlgoReturn, ParsingError> {
        let value = self.parse_obj(block)?;
        Ok(AlgoReturn::new(value, block.line_file))
    }
}
