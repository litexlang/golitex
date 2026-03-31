use crate::prelude::*;

impl Runtime {
    pub fn parse_param_def_with_param_type_and_skip_comma(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<ParamDefWithParamType, ParsingError> {
        let param = tb.advance()?;
        let param_def_with_param_type = if tb.current()? != COMMA {
            ParamDefWithParamType(vec![param], self.parse_param_type(tb)?)
        } else {
            let mut vec_of_params = vec![param];

            while tb.current_token_is_equal_to(COMMA) {
                tb.skip()?;
                vec_of_params.push(tb.advance()?);
            }
            let param_type = self.parse_param_type(tb)?;

            ParamDefWithParamType(vec_of_params, param_type)
        };
        if tb.current_token_is_equal_to(COMMA) {
            tb.skip_token(COMMA)?;
        }
        Ok(param_def_with_param_type)
    }

    pub fn parse_param_type(&mut self, tb: &mut TokenBlock) -> Result<ParamType, ParsingError> {
        match tb.current()? {
            NONEMPTY_SET => self.param_type_nonempty_set(tb),
            FINITE_SET => self.param_type_finite_set(tb),
            SET => self.param_type_set(tb),
            STRUCT => self.param_type_instantiated_struct(tb),
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

    pub fn param_type_obj(&mut self, tb: &mut TokenBlock) -> Result<ParamType, ParsingError> {
        let obj = self.parse_obj(tb)?;
        Ok(ParamType::Obj(obj))
    }

    pub fn param_type_instantiated_struct(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<ParamType, ParsingError> {
        tb.skip_token(STRUCT)?;
        let name = self.parse_identifier_or_identifier_with_mod(tb)?;
        let params = self.parse_braced_objs(tb)?;
        Ok(ParamType::InstantiatedStruct(InstantiatedStruct {
            name,
            params,
        }))
    }
}
