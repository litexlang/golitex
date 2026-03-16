use crate::common::keywords::{COMMA, FINITE_SET, NONEMPTY_SET, SET};
use crate::execute::Executor;
use super::TokenBlock;
use crate::error::ParsingError;
use crate::stmt::parameter_type_and_property::{ParamDefWithParamType, ParamType, Set, NonemptySet, FiniteSet};

impl<'a> Executor<'a> {
    pub fn parse_param_def_with_param_type(&self, tb: &mut TokenBlock) -> Result<ParamDefWithParamType, ParsingError> {
        self.param_def_with_type(tb)
    }

    pub fn param_def_with_type(&self, tb: &mut TokenBlock) -> Result<ParamDefWithParamType, ParsingError> {
        let param = tb.advance()?;
        if tb.current()? != COMMA {
            Ok(ParamDefWithParamType(vec![param], self.param_type(tb)?))
        } else {
            let mut vec_of_params = vec![param];
            while tb.current()? == COMMA {
                tb.skip()?;
                vec_of_params.push(tb.advance()?);
            }
            let param_type = self.param_type(tb)?;
            Ok(ParamDefWithParamType(vec_of_params, param_type))
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
        let obj = self.parse_obj(tb)?;
        Ok(ParamType::Obj(obj))
    }
}