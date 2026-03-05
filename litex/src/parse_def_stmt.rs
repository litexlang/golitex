use crate::and_fact_or_specific_fact::AndFactOrSpecFact;
use crate::definition_stmt::{DefLetStmt, DefPropStmt, DefSetTemplateStmt, DefStmt, HaveExistObjStmt, HaveFnEqualCaseByCaseStmt, HaveFnEqualStmt, HaveObjEqualStmt, HaveObjInNonemptySetOrParamTypeStmt};
use crate::exist_fact::ExistFact;
use crate::errors::ParsingError;
use crate::define_algorithm_stmt::{AlgoIf, AlgoReturn, AlgoReturnOrAlgoIf, DefineAlgorithmStmt};
use crate::keywords::{ALGO, CASE, COLON, COMMA, EQUAL, FN, HAVE, IF, LEFT_BRACE, LET, PROP, RETURN, RIGHT_BRACE, SET_TEMPLATE};
use crate::parameter_type_and_property::{ParamDefWithParamType, ParamDefWithParamTypeOrProperty};
use crate::parser::Parser;
use crate::stmt::Stmt;
use crate::token_block::TokenBlock;

impl Parser {
    pub fn def_prop_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(PROP)?;
        let name = tb.advance()?;
        tb.skip_token(LEFT_BRACE)?;
        let mut param_defs: Vec<ParamDefWithParamTypeOrProperty> = vec![];
        while tb.current()? != RIGHT_BRACE {
            param_defs.push(self.param_def_with_property(tb)?);
        }
        tb.skip_token(RIGHT_BRACE)?;
        let facts = self.parse_facts_in_body(tb)?;
        match facts.len() {
            0 => Ok(Stmt::DefStmt(DefStmt::DefPropStmt(DefPropStmt::new(name, param_defs, None, Some(tb.line_file_index))))),
            _ => Ok(Stmt::DefStmt(DefStmt::DefPropStmt(DefPropStmt::new(name, param_defs, Some(facts), Some(tb.line_file_index))))),
        }
    }

    pub fn def_let_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(LET)?;
        let mut param_def: Vec<ParamDefWithParamType> = vec![];
        loop {
            match tb.current() {
                Ok(t) if t == COLON => break,
                Err(_) => break,
                Ok(_) => {}
            }
            let p = self.param_def_with_param_type(tb)?;
            let pd = match p {
                ParamDefWithParamTypeOrProperty::ParamAndItsTypePair(n, t) => ParamDefWithParamType::ParamAndItsTypePair(n, t),
                ParamDefWithParamTypeOrProperty::ParamsAndTheirTypePair(ns, t) => ParamDefWithParamType::ParamsAndTheirTypePair(ns, t),
                ParamDefWithParamTypeOrProperty::ParamsPropertyPair(..) => {
                    return Err(ParsingError::new("let does not support property params here", tb.line_file_index));
                }
            };
            param_def.push(pd);
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
        Ok(Stmt::DefStmt(DefStmt::DefLetStmt(DefLetStmt::new(
            param_def,
            facts,
            Some(tb.line_file_index),
        ))))
    }

    // return HaveObjInNonemptySetOrParamTypeStmt or HaveObjEqualStmt
    pub fn have_obj_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(HAVE)?;
        let mut param_defs: Vec<ParamDefWithParamType> = vec![];
        loop {
            let p = self.param_def_with_param_type(tb)?;
            let param_def = match p {
                ParamDefWithParamTypeOrProperty::ParamAndItsTypePair(n, t) => ParamDefWithParamType::ParamAndItsTypePair(n, t),
                ParamDefWithParamTypeOrProperty::ParamsAndTheirTypePair(ns, t) => ParamDefWithParamType::ParamsAndTheirTypePair(ns, t),
                ParamDefWithParamTypeOrProperty::ParamsPropertyPair(..) => {
                    return Err(ParsingError::new("have obj in nonempty set does not support property params", tb.line_file_index));
                }
            };
            param_defs.push(param_def);
            if !matches!(tb.current(), Ok(t) if t == COMMA) {
                break;
            }
            tb.skip_token(COMMA)?;
        }
        if param_defs.is_empty() {
            return Err(ParsingError::new("have expects at least one param type pair", tb.line_file_index));
        }

        if tb.current().map(|t| t != EQUAL).unwrap_or(true) {
            Ok(Stmt::DefStmt(DefStmt::HaveObjInNonemptySetStmt(HaveObjInNonemptySetOrParamTypeStmt::new(param_defs, Some(tb.line_file_index)))))
        } else {
            tb.skip_token(EQUAL)?;
            let mut objs_equal_to = vec![self.obj(tb)?];
            while matches!(tb.current(), Ok(t) if t == COMMA) {
                tb.skip_token(COMMA)?;
                objs_equal_to.push(self.obj(tb)?);
            }
            Ok(Stmt::DefStmt(DefStmt::HaveObjEqualStmt(HaveObjEqualStmt::new(param_defs, objs_equal_to, Some(tb.line_file_index)))))
        }
    }

    pub fn have_fn_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(HAVE)?;
        tb.skip_token(FN)?;
        let name = tb.advance()?;
        let fs = self.fn_set_with_dom_without_fn_prefix(tb)?;
        if tb.current()? == COLON {
            tb.skip_token(COLON)?;
            let mut cases: Vec<AndFactOrSpecFact> = vec![];
            let mut equal_tos: Vec<crate::obj::Obj> = vec![];
            for block in tb.body.iter_mut() {
                block.skip_token(CASE)?;
                cases.push(self.and_spec_fact(block)?);
                block.skip_token(EQUAL)?;
                equal_tos.push(self.obj(block)?);
            }
            Ok(Stmt::DefStmt(DefStmt::HaveFnEqualCaseByCaseStmt(HaveFnEqualCaseByCaseStmt::new(
                name, fs, cases, equal_tos, Some(tb.line_file_index),
            ))))
        } else {
            tb.skip_token(EQUAL)?;
            let equal_to = self.obj(tb)?;
            Ok(Stmt::DefStmt(DefStmt::HaveFnEqualStmt(HaveFnEqualStmt::new(
                name, fs, equal_to, Some(tb.line_file_index),
            ))))
        }
    }

    pub fn have_exist(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(HAVE)?;
        let ef = self.exist_fact(tb, true)?;
        let true_fact = match ef {
            ExistFact::TrueExistFact(t) => t,
            ExistFact::NotExistFact(_) => {
                return Err(ParsingError::new("have exist expects true exist fact", tb.line_file_index));
            }
        };
        Ok(Stmt::DefStmt(DefStmt::HaveExistObjStmt(HaveExistObjStmt::new(
            true_fact,
            Some(tb.line_file_index),
        ))))
    }

    pub fn def_set_template_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(SET_TEMPLATE)?;
        let name = tb.advance()?;
        tb.skip_token(LEFT_BRACE)?;
        let mut params_def_with_type: Vec<ParamDefWithParamTypeOrProperty> = vec![];
        while tb.current()? != COLON && tb.current()? != RIGHT_BRACE {
            params_def_with_type.push(self.param_def_with_param_type(tb)?);
            if tb.current()? == COMMA {
                tb.skip_token(COMMA)?;
            }
        }
        let dom_facts = if tb.current()? == COLON {
            tb.skip_token(COLON)?;
            let mut facts = vec![];
            while tb.current()? != RIGHT_BRACE {
                facts.push(self.or_and_spec_fact(tb)?);
                if tb.current()? == COMMA {
                    tb.skip_token(COMMA)?;
                }
            }
            facts
        } else {
            vec![]
        };
        tb.skip_token(RIGHT_BRACE)?;
        tb.skip_token(EQUAL)?;
        let equal_to = self.obj(tb)?;
        Ok(Stmt::DefStmt(DefStmt::DefSetTemplateStmt(DefSetTemplateStmt::new(
            name,
            params_def_with_type,
            dom_facts,
            equal_to,
            Some(tb.line_file_index),
        ))))
    }

    pub fn def_algorithm_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(ALGO)?;
        let name = tb.advance()?;
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
                return Err(ParsingError::new("algo body block must start with if or return", block.line_file_index));
            };
            return_or_algo_if.push(item);
        }
        Ok(Stmt::DefStmt(DefStmt::DefineAlgorithmStmt(DefineAlgorithmStmt::new(
            name,
            params,
            return_or_algo_if,
            Some(tb.line_file_index),
        ))))
    }

    /// head 里是 if and_spec_fact :，body 有且只有一个块，即 return obj。
    fn parse_algo_if(&self, block: &mut TokenBlock) -> Result<AlgoIf, ParsingError> {
        block.skip_token(IF)?;
        let condition = self.and_spec_fact(block)?;
        block.skip_token(COLON)?;
        if !block.exceed_end_of_head() {
            return Err(ParsingError::new("algo if: expected end of head after condition", block.line_file_index));
        }
        if block.body.len() != 1 {
            return Err(ParsingError::new("algo if block must have exactly one body block (return stmt)", block.line_file_index));
        }
        let return_stmt = self.parse_algo_return(block.body.first_mut().unwrap())?;
        Ok(AlgoIf::new(
            condition,
            return_stmt,
            Some(block.line_file_index),
        ))
    }

    /// head 里是 return，后跟 obj。
    fn parse_algo_return(&self, block: &mut TokenBlock) -> Result<AlgoReturn, ParsingError> {
        block.skip_token(RETURN)?;
        let value = self.obj(block)?;
        Ok(AlgoReturn::new(value, Some(block.line_file_index)))
    }

}