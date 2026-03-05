use crate::keywords::{COMMA, FINITE_SET, LEFT_BRACKET, NONEMPTY_SET, NOT, RIGHT_BRACKET, SET, is_key_symbol_or_keyword};
use crate::parser::Parser;
use crate::token_block::TokenBlock;
use crate::errors::ParsingError;
use crate::parameter_type_and_property::{ParamDefWithParamTypeOrProperty, ParamType, Set, NonemptySet, FiniteSet};

impl Parser {
    pub fn param_def_with_param_type(&self, tb: &mut TokenBlock) -> Result<ParamDefWithParamTypeOrProperty, ParsingError> {
        match tb.current()? {
            LEFT_BRACKET => self.param_def_with_property(tb),
            _ => self.param_def_with_type(tb),
        }
    }

    pub fn param_def_with_property(&self, tb: &mut TokenBlock) -> Result<ParamDefWithParamTypeOrProperty, ParsingError> {
        tb.skip_token(LEFT_BRACKET)?;
        let mut params: Vec<String> = vec![];
        while tb.current()? != RIGHT_BRACKET {
            params.push(tb.advance()?);
        }
        tb.skip_token(RIGHT_BRACKET)?;

        let is_true: bool = if tb.current()? == NOT {
            tb.no_check_skip()?;
            false
        } else {
            true
        };
        
        let property_name = self.atom(tb)?;

        if is_key_symbol_or_keyword(&property_name.to_string()) {
            return Err(ParsingError::new(&format!("Invalid property name: {}", property_name.to_string()), tb.line_file_index));
        }
        
        Ok(ParamDefWithParamTypeOrProperty::ParamsPropertyPair(params, is_true, property_name))
    }

    pub fn param_def_with_type(&self, tb: &mut TokenBlock) -> Result<ParamDefWithParamTypeOrProperty, ParsingError> {
        let param = tb.advance()?;
        if tb.current()? != COMMA {
            Ok(ParamDefWithParamTypeOrProperty::ParamAndItsTypePair(param, self.param_type(tb)?))
        } else {
            let mut vec_of_params = vec![param];
            while tb.current()? == COMMA {
                tb.no_check_skip()?;
                vec_of_params.push(tb.advance()?);
            }
            let param_type = self.param_type(tb)?;
            Ok(ParamDefWithParamTypeOrProperty::ParamsAndTheirTypePair(vec_of_params, param_type))
        }
    }

    pub fn param_type(&self, tb: &mut TokenBlock) -> Result<ParamType, ParsingError> {
        match tb.current()? {
            NONEMPTY_SET => self.param_type_nonempty_set(tb),
            FINITE_SET => self.param_type_finite_set(tb),
            SET => self.param_type_set(tb),
            _ => self.param_type_obj(tb),
        }
    }

    pub fn param_type_nonempty_set(&self, tb: &mut TokenBlock) -> Result<ParamType, ParsingError> {
        tb.skip_token(NONEMPTY_SET)?;
        Ok(ParamType::NonemptySet(NonemptySet::new()))
    }

    pub fn param_type_finite_set(&self, tb: &mut TokenBlock) -> Result<ParamType, ParsingError> {
        tb.skip_token(FINITE_SET)?;
        Ok(ParamType::FiniteSet(FiniteSet::new()))
    }

    pub fn param_type_set(&self, tb: &mut TokenBlock) -> Result<ParamType, ParsingError> {
        tb.skip_token(SET)?;
        Ok(ParamType::Set(Set::new()))
    }

    pub fn param_type_obj(&self, tb: &mut TokenBlock) -> Result<ParamType, ParsingError> {
        let obj = self.obj(tb)?;
        Ok(ParamType::Obj(obj))
    }
}