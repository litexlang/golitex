use crate::keywords::{COMMA, FINITE_SET, LEFT_BRACKET, NONEMPTY_SET, NOT, RIGHT_BRACKET, SET, is_key_symbol_or_keyword};
use crate::parser::Parser;
use crate::token_block::TokenBlock;
use crate::errors::ParsingError;
use crate::parameter_type_and_property::{ParamDefWithParamType, ParamType, Set, NonemptySet, FiniteSet};

impl Parser {
    pub fn param_def_with_param_type(&self, token_block: &mut TokenBlock) -> Result<ParamDefWithParamType, ParsingError> {
        match token_block.current()? {
            LEFT_BRACKET => self.param_def_with_property(token_block),
            _ => self.param_def_with_type(token_block),
        }
    }

    pub fn param_def_with_property(&self, token_block: &mut TokenBlock) -> Result<ParamDefWithParamType, ParsingError> {
        token_block.skip_token(LEFT_BRACKET)?;
        let mut params: Vec<String> = vec![];
        while token_block.current()? != RIGHT_BRACKET {
            let param = token_block.advance()?;
            params.push(param);
        }
        token_block.skip_token(RIGHT_BRACKET)?;

        let is_true: bool = if token_block.current()? == NOT {
            token_block.no_check_skip()?;
            false
        } else {
            true
        };
        
        let property_name = self.atom(token_block)?;

        if is_key_symbol_or_keyword(&property_name.to_string()) {
            return Err(ParsingError::new(&format!("Invalid property name: {}", property_name.to_string()), token_block.line_file_index));
        }
        
        Ok(ParamDefWithParamType::ParamsPropertyPair(params, is_true, property_name))
    }

    pub fn param_def_with_type(&self, token_block: &mut TokenBlock) -> Result<ParamDefWithParamType, ParsingError> {
        let param = token_block.advance()?;
        if token_block.current()? != COMMA {
            Ok(ParamDefWithParamType::ParamAndItsTypePair(param, self.param_type(token_block)?))
        } else {
            let mut vec_of_params = vec![param];
            while token_block.current()? == COMMA {
                token_block.no_check_skip()?;
                let param = token_block.advance()?;
                vec_of_params.push(param);
            }
            let param_type = self.param_type(token_block)?;
            Ok(ParamDefWithParamType::ParamsAndTheirTypePair(vec_of_params, param_type))
        }
    }

    pub fn param_type(&self, token_block: &mut TokenBlock) -> Result<ParamType, ParsingError> {
        match token_block.current()? {
            NONEMPTY_SET => self.param_type_nonempty_set(token_block),
            FINITE_SET => self.param_type_finite_set(token_block),
            SET => self.param_type_set(token_block),
            _ => self.param_type_obj(token_block),
        }
    }

    pub fn param_type_nonempty_set(&self, token_block: &mut TokenBlock) -> Result<ParamType, ParsingError> {
        token_block.skip_token(NONEMPTY_SET)?;
        Ok(ParamType::NonemptySet(NonemptySet::new()))
    }

    pub fn param_type_finite_set(&self, token_block: &mut TokenBlock) -> Result<ParamType, ParsingError> {
        token_block.skip_token(FINITE_SET)?;
        Ok(ParamType::FiniteSet(FiniteSet::new()))
    }

    pub fn param_type_set(&self, token_block: &mut TokenBlock) -> Result<ParamType, ParsingError> {
        token_block.skip_token(SET)?;
        Ok(ParamType::Set(Set::new()))
    }

    pub fn param_type_obj(&self, token_block: &mut TokenBlock) -> Result<ParamType, ParsingError> {
        let obj = self.obj(token_block)?;
        Ok(ParamType::Obj(obj))
    }
}