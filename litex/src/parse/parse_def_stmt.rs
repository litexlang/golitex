use crate::stmt::definition_stmt::{DefLetStmt, DefPropStmt, DefStructWithNoFieldStmt, DefStructWithFieldsStmt, HaveExistObjStmt, HaveFnEqualCaseByCaseStmt, HaveFnEqualStmt, HaveObjEqualStmt, HaveObjInNonemptySetOrParamTypeStmt, DefPropWithoutMeaningStmt};
use crate::fact::{AndChainAtomicFact, OrAndChainAtomicFact};
use crate::error::ParsingError;
use crate::stmt::define_algorithm_stmt::{AlgoIf, AlgoReturn, AlgoReturnOrAlgoIf, DefAlgoStmt};
use crate::common::keywords::{ALGO, CASE, COLON, COMMA, EQUAL, EQUIVALENT_SIGN, FN, HAVE, IF, LEFT_BRACE, LET, PROP, RETURN, RIGHT_BRACE, STRUCT};
use crate::stmt::parameter_type_and_property::ParamDefWithParamType;
use crate::execute::Executor;
use crate::stmt::Stmt;
use super::TokenBlock;

impl<'a> Executor<'a> {
    pub fn def_prop_stmt_or_prop_without_meaning(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {        
        if tb.token_at_end_of_head() != COLON {
            return self.parse_def_prop_without_meaning_stmt(tb)
        } else {
            self.parse_def_prop_stmt(tb)
        }
    }

    pub fn parse_def_prop_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        self.new_parsing_names_block();
        let stmt = self.parse_def_prop_stmt_body(tb);
        self.delete_parsing_names_block();
        stmt
    }

    fn parse_def_prop_stmt_body(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(PROP)?;
        let name = tb.advance()?;
        self.validate_name_and_put_into_parsing_names_block(&name).map_err(|e| ParsingError::new(e.to_string(), tb.line_file_index))?;
        tb.skip_token(LEFT_BRACE)?;
        let mut param_defs: Vec<ParamDefWithParamType> = vec![];
        while tb.current()? != RIGHT_BRACE {
            param_defs.push(self.param_def_with_type(tb)?);
        }
        tb.skip_token(RIGHT_BRACE)?;
        let all_param_names = ParamDefWithParamType::collect_param_names(&param_defs);
        self.validate_names_and_put_into_parsing_names_block(&all_param_names).map_err(|e| ParsingError::new(e.to_string(), tb.line_file_index))?;
        let facts = self.parse_facts_in_body(tb)?;
        match facts.len() {
            0 => Ok(Stmt::DefPropStmt(DefPropStmt::new(name, param_defs, None, Some(tb.line_file_index)))),
            _ => Ok(Stmt::DefPropStmt(DefPropStmt::new(name, param_defs, Some(facts), Some(tb.line_file_index)))),
        }
    }

    pub fn parse_def_prop_without_meaning_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        self.new_parsing_names_block();
        let stmt = self.parse_def_prop_without_meaning_stmt_body(tb);
        self.delete_parsing_names_block();
        stmt
    }

    fn parse_def_prop_without_meaning_stmt_body(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(PROP)?;
        let name = tb.advance()?;
        self.validate_name_and_put_into_parsing_names_block(&name).map_err(|e| ParsingError::new(e.to_string(), tb.line_file_index))?;
        tb.skip_token(LEFT_BRACE)?;
        let mut params = vec![];
        while tb.current()? != RIGHT_BRACE {
            params.push(tb.advance()?);
            if tb.current()? == COMMA {
                tb.skip_token(COMMA)?;
            }
        }
        tb.skip_token(RIGHT_BRACE)?;

        self.validate_names_and_put_into_parsing_names_block(&params).map_err(|e| ParsingError::new(e.to_string(), tb.line_file_index))?;

        Ok(Stmt::DefPropWithoutMeaningStmt(DefPropWithoutMeaningStmt::new(name, params, Some(tb.line_file_index))))
    }

    pub fn parse_def_let_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        self.new_parsing_names_block();
        let stmt = self.parse_def_let_stmt_body(tb);
        self.delete_parsing_names_block();
        stmt
    }

    fn parse_def_let_stmt_body(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
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
        self.validate_names_and_put_into_parsing_names_block(&all_param_names).map_err(|e| ParsingError::new(e.to_string(), tb.line_file_index))?;
        Ok(Stmt::DefLetStmt(DefLetStmt::new(
            param_def,
            facts,
            Some(tb.line_file_index),
        )))
    }

    // return HaveObjInNonemptySetOrParamTypeStmt or HaveObjEqualStmt
    pub fn have_obj_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        self.new_parsing_names_block();
        let stmt = self.have_obj_stmt_body(tb);
        self.delete_parsing_names_block();
        stmt
    }

    fn have_obj_stmt_body(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
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
            return Err(ParsingError::new("have expects at least one param type pair".to_string(), tb.line_file_index));
        }
        let have_param_names = ParamDefWithParamType::collect_param_names(&param_defs);
        self.validate_names_and_put_into_parsing_names_block(&have_param_names).map_err(|e| ParsingError::new(e.to_string(), tb.line_file_index))?;

        if tb.current().map(|t| t != EQUAL).unwrap_or(true) {
            Ok(Stmt::HaveObjInNonemptySetStmt(HaveObjInNonemptySetOrParamTypeStmt::new(param_defs, Some(tb.line_file_index))))
        } else {
            tb.skip_token(EQUAL)?;
            let mut objs_equal_to = vec![self.parse_obj(tb)?];
            while matches!(tb.current(), Ok(t) if t == COMMA) {
                tb.skip_token(COMMA)?;
                objs_equal_to.push(self.parse_obj(tb)?);
            }
            Ok(Stmt::HaveObjEqualStmt(HaveObjEqualStmt::new(param_defs, objs_equal_to, Some(tb.line_file_index))))
        }
    }

    pub fn have_fn_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(HAVE)?;
        tb.skip_token(FN)?;
        let name = tb.advance()?;
        let fs = self.fn_set_with_dom_without_fn_prefix(tb)?;
        if tb.current()? == COLON {
            tb.skip_token(COLON)?;
            let mut cases: Vec<AndChainAtomicFact> = vec![];
            let mut equal_tos: Vec<crate::obj::Obj> = vec![];
            for block in tb.body.iter_mut() {
                block.skip_token(CASE)?;
                cases.push(self.parse_and_chain_atomic_fact(block)?);
                block.skip_token(EQUAL)?;
                equal_tos.push(self.parse_obj(block)?);
            }
            Ok(Stmt::HaveFnEqualCaseByCaseStmt(HaveFnEqualCaseByCaseStmt::new(
                name, fs, cases, equal_tos, Some(tb.line_file_index),
            )))
        } else {
            tb.skip_token(EQUAL)?;
            let equal_to = self.parse_obj(tb)?;
            Ok(Stmt::HaveFnEqualStmt(HaveFnEqualStmt::new(
                name, fs, equal_to, Some(tb.line_file_index),
            )))
        }
    }

    pub fn have_exist(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(HAVE)?;

        let mut equal_tos = vec![];
        while tb.current()? == COMMA {
            tb.skip_token(COMMA)?;
            equal_tos.push(self.parse_obj(tb)?);
        }

        tb.skip_token(COLON)?;
        let true_fact = self.parse_exist_fact(tb)?;
        Ok(Stmt::HaveExistObjStmt(HaveExistObjStmt::new(equal_tos, true_fact, Some(tb.line_file_index))))
    }

    pub fn def_struct_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        self.new_parsing_names_block();
        let stmt = self.def_struct_stmt_body(tb);
        self.delete_parsing_names_block();
        stmt
    }

    fn def_struct_stmt_body(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(STRUCT)?;
        let name = tb.advance()?;
        self.validate_name_and_put_into_parsing_names_block(&name).map_err(|e| ParsingError::new(e.to_string(), tb.line_file_index))?;
        tb.skip_token(LEFT_BRACE)?;
        let mut params_def_with_type: Vec<ParamDefWithParamType> = vec![];
        while tb.current()? != COLON && tb.current()? != RIGHT_BRACE {
            params_def_with_type.push(self.parse_param_def_with_param_type(tb)?);
            if tb.current()? == COMMA {
                tb.skip_token(COMMA)?;
            }
        }
        let struct_param_names = ParamDefWithParamType::collect_param_names(&params_def_with_type);
        self.validate_names_and_put_into_parsing_names_block(&struct_param_names).map_err(|e| ParsingError::new(e.to_string(), tb.line_file_index))?;
        let dom_facts = if tb.current()? == COLON {
            tb.skip_token(COLON)?;
            let mut facts = vec![];
            while tb.current()? != RIGHT_BRACE {
                facts.push(self.parse_or_and_chain_atomic_fact(tb)?);
                if tb.current()? == COMMA {
                    tb.skip_token(COMMA)?;
                }
            }
            facts
        } else {
            vec![]
        };
        tb.skip_token(RIGHT_BRACE)?;
        if tb.current()? == EQUAL {
            tb.skip_token(EQUAL)?;
            let equal_to = self.parse_obj(tb)?;
            Ok(Stmt::DefStructWithNoFieldStmt(DefStructWithNoFieldStmt::new(
                name,
                params_def_with_type,
                dom_facts,
                equal_to,
                Some(tb.line_file_index),
            )))
        } else {
            tb.skip_token(COLON)?;

            if tb.body.is_empty() {
                return Err(ParsingError::new("struct with fields expects body".to_string(), tb.line_file_index));
            }

            let mut fields: Vec<(String, OrAndChainAtomicFact)> = vec![];
            let mut facts: Vec<OrAndChainAtomicFact> = vec![];

            let body_len = tb.body.len();
            let last_index = body_len - 1;
            let last_is_equiv = {
                let last = tb.body.get(last_index).ok_or_else(|| ParsingError::new("Expected body".to_string(), tb.line_file_index))?;
                last.token_at_end_of_head() == EQUIVALENT_SIGN
            };

            let field_end = if last_is_equiv { last_index } else { body_len };

            for i in 0..field_end {
                let block = tb.body.get_mut(i).ok_or_else(|| ParsingError::new("Expected field block".to_string(), tb.line_file_index))?;
                let field_name = block.advance()?;
                let cond = self.parse_or_and_chain_atomic_fact(block)?;
                fields.push((field_name, cond));
            }

            if last_is_equiv {
                let last = tb.body.get_mut(last_index).ok_or_else(|| ParsingError::new("Expected <=>: block".to_string(), tb.line_file_index))?;
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
                Some(tb.line_file_index),
            )))
        }
    }

    pub fn def_algorithm_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        self.new_parsing_names_block();
        let stmt = self.def_algorithm_stmt_body(tb);
        self.delete_parsing_names_block();
        stmt
    }

    fn def_algorithm_stmt_body(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(ALGO)?;
        let name = tb.advance()?;
        self.validate_name_and_put_into_parsing_names_block(&name).map_err(|e| ParsingError::new(e.to_string(), tb.line_file_index))?;
        tb.skip_token(LEFT_BRACE)?;
        let mut params: Vec<String> = vec![];
        while tb.current()? != RIGHT_BRACE {
            params.push(tb.advance()?);
            if tb.current()? == COMMA {
                tb.skip_token(COMMA)?;
            }
        }
        tb.skip_token(RIGHT_BRACE)?;
        tb.skip_token(COLON)?;
        let mut return_or_algo_if: Vec<AlgoReturnOrAlgoIf> = vec![];
        for block in tb.body.iter_mut() {
            let item = if block.current()? == IF {
                AlgoReturnOrAlgoIf::AlgoIf(self.parse_algo_if(block)?)
            } else if block.current()? == RETURN {
                AlgoReturnOrAlgoIf::AlgoReturn(self.parse_algo_return(block)?)
            } else {
                return Err(ParsingError::new("algo body block must start with if or return".to_string(), block.line_file_index));
            };

            
            return_or_algo_if.push(item);
        }
        Ok(Stmt::DefAlgoStmt(DefAlgoStmt::new(
            name,
            params,
            return_or_algo_if,
            Some(tb.line_file_index),
        )))
    }

    /// head 里是 if and_spec_fact :，body 有且只有一个块，即 return obj。
    fn parse_algo_if(&mut self, block: &mut TokenBlock) -> Result<AlgoIf, ParsingError> {
        block.skip_token(IF)?;
        let condition = self.parse_and_chain_atomic_fact(block)?;
        block.skip_token(COLON)?;
        if !block.exceed_end_of_head() {
            return Err(ParsingError::new("algo if: expected end of head after condition".to_string(), block.line_file_index));
        }
        if block.body.len() != 1 {
            return Err(ParsingError::new("algo if block must have exactly one body block (return stmt)".to_string(), block.line_file_index));
        }

        let block = block.body.first_mut().ok_or_else(|| ParsingError::new("algo if block must have exactly one body block (return stmt)".to_string(), block.line_file_index))?;
        
        let return_stmt = self.parse_algo_return(block)?;
        Ok(AlgoIf::new(
            condition,
            return_stmt,
            Some(block.line_file_index),
        ))
    }

    /// head 里是 return，后跟 obj。
    fn parse_algo_return(&mut self, block: &mut TokenBlock) -> Result<AlgoReturn, ParsingError> {
        block.skip_token(RETURN)?;
        let value = self.parse_obj(block)?;
        Ok(AlgoReturn::new(value, Some(block.line_file_index)))
    }

}