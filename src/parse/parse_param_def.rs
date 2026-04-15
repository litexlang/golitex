use crate::prelude::*;

impl Runtime {
    /// Struct type parameters and field types must not use nested `struct T(...)` (no `ParamType::Struct`).
    pub fn reject_nested_struct_param_type(
        &self,
        pt: &ParamType,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        if matches!(pt, ParamType::Struct(_)) {
            return Err(
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "nested `struct` types are not allowed in struct parameter and field types"
                        .to_string(),
                line_file,
                None,
                vec![],
            ))));
        }
        Ok(())
    }

    pub fn parse_param_def_with_param_type_and_skip_comma(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<ParamGroupWithParamType, RuntimeError> {
        let param = tb.advance()?;
        let param_def_with_param_type = if tb.current()? != COMMA {
            ParamGroupWithParamType::new(vec![param], self.parse_param_type(tb)?)
        } else {
            let mut vec_of_params = vec![param];

            while tb.current_token_is_equal_to(COMMA) {
                tb.skip()?;
                vec_of_params.push(tb.advance()?);
            }
            let param_type = self.parse_param_type(tb)?;

            ParamGroupWithParamType::new(vec_of_params, param_type)
        };
        if tb.current_token_is_equal_to(COMMA) {
            tb.skip_token(COMMA)?;
        }
        Ok(param_def_with_param_type)
    }

    pub fn parse_param_type(&mut self, tb: &mut TokenBlock) -> Result<ParamType, RuntimeError> {
        match tb.current()? {
            NONEMPTY_SET => self.parse_param_type_nonempty_set(tb),
            FINITE_SET => self.parse_param_type_finite_set(tb),
            SET => self.parse_param_type_set(tb),
            FAMILY => self
                .parse_family_obj(tb)
                .map(|f| ParamType::Obj(Obj::FamilyObj(f))),
            STRUCT => self
                .parse_struct_obj(tb)
                .map(|s| ParamType::Struct(s.into())),
            _ => self.parse_param_type_obj(tb),
        }
    }

    pub fn parse_param_type_nonempty_set(
        &self,
        tb: &mut TokenBlock,
    ) -> Result<ParamType, RuntimeError> {
        tb.skip_token(NONEMPTY_SET)?;
        Ok(ParamType::NonemptySet(NonemptySet::new()))
    }

    pub fn parse_param_type_finite_set(
        &self,
        tb: &mut TokenBlock,
    ) -> Result<ParamType, RuntimeError> {
        tb.skip_token(FINITE_SET)?;
        Ok(ParamType::FiniteSet(FiniteSet::new()))
    }

    pub fn parse_param_type_set(&self, tb: &mut TokenBlock) -> Result<ParamType, RuntimeError> {
        tb.skip_token(SET)?;
        Ok(ParamType::Set(Set::new()))
    }

    pub fn parse_param_type_obj(&mut self, tb: &mut TokenBlock) -> Result<ParamType, RuntimeError> {
        let obj = self.parse_obj(tb)?;
        Ok(ParamType::Obj(obj))
    }
}
