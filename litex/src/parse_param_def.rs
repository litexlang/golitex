use crate::keywords::{COMMA, FINITE_SET, NONEMPTY_SET, SET, STRUCT};
use crate::parser::Parser;
use crate::token_block::TokenBlock;
use crate::errors::ParsingError;
use crate::parameter_type_and_property::{ParamDefWithParamType, ParamType, Set, NonemptySet, FiniteSet, StructParamType};

impl Parser {
    pub fn param_def_with_param_type(&self, tb: &mut TokenBlock) -> Result<ParamDefWithParamType, ParsingError> {
        self.param_def_with_type(tb)
    }

    pub fn param_def_with_type(&self, tb: &mut TokenBlock) -> Result<ParamDefWithParamType, ParsingError> {
        let param = tb.advance()?;
        if tb.current()? != COMMA {
            Ok(ParamDefWithParamType::ParamAndItsTypePair(param, self.param_type(tb)?))
        } else {
            let mut vec_of_params = vec![param];
            while tb.current()? == COMMA {
                tb.skip()?;
                vec_of_params.push(tb.advance()?);
            }
            let param_type = self.param_type(tb)?;
            Ok(ParamDefWithParamType::ParamsAndTheirTypePair(vec_of_params, param_type))
        }
    }

    pub fn param_type(&self, tb: &mut TokenBlock) -> Result<ParamType, ParsingError> {
        match tb.current()? {
            NONEMPTY_SET => self.param_type_nonempty_set(tb),
            FINITE_SET => self.param_type_finite_set(tb),
            SET => self.param_type_set(tb),
            STRUCT => self.param_type_struct(tb),
            _ => self.param_type_obj(tb),
        }
    }

    pub fn param_type_struct(&self, tb: &mut TokenBlock) -> Result<ParamType, ParsingError> {
        tb.skip_token(STRUCT)?;
        let identifier = self.identifier_or_identifier_with_mod(tb)?;
        Ok(ParamType::Struct(StructParamType::new(identifier)))
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