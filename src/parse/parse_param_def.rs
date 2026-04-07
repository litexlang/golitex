use crate::prelude::*;

impl Runtime {
    pub fn parse_param_def_with_struct_field_type_and_skip_comma(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<ParamGroupWithStructFieldType, RuntimeError> {
        let param = tb.advance()?;
        let param_def = if tb.current()? != COMMA {
            ParamGroupWithStructFieldType::new(vec![param], self.parse_struct_field_type(tb)?)
        } else {
            let mut vec_of_params = vec![param];

            while tb.current_token_is_equal_to(COMMA) {
                tb.skip()?;
                vec_of_params.push(tb.advance()?);
            }
            let param_type = self.parse_struct_field_type(tb)?;

            ParamGroupWithStructFieldType::new(vec_of_params, param_type)
        };
        if tb.current_token_is_equal_to(COMMA) {
            tb.skip_token(COMMA)?;
        }
        Ok(param_def)
    }

    /// `struct` 头部与字段类型：不允许嵌套 `struct`（无 `struct Foo(...)`）。
    pub fn parse_struct_field_type(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<StructFieldType, RuntimeError> {
        match tb.current()? {
            NONEMPTY_SET => self.parse_param_type_nonempty_set(tb).map(|pt| match pt {
                ParamType::NonemptySet(n) => StructFieldType::NonemptySet(n),
                _ => unreachable!(),
            }),
            FINITE_SET => self.parse_param_type_finite_set(tb).map(|pt| match pt {
                ParamType::FiniteSet(f) => StructFieldType::FiniteSet(f),
                _ => unreachable!(),
            }),
            SET => self.parse_param_type_set(tb).map(|pt| match pt {
                ParamType::Set(s) => StructFieldType::Set(s),
                _ => unreachable!(),
            }),
            FAMILY => self.parse_param_type_family(tb).map(|pt| match pt {
                ParamType::Family(f) => StructFieldType::Family(f),
                _ => unreachable!(),
            }),
            STRUCT => Err(
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "nested `struct` types are not allowed in struct parameter and field types"
                        .to_string(),
                    tb.line_file.clone(),
                    None,
                ),
            ),
            _ => self.parse_param_type_obj(tb).map(|pt| match pt {
                ParamType::Obj(o) => StructFieldType::Obj(o),
                _ => unreachable!(),
            }),
        }
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
            FAMILY => self.parse_param_type_family(tb),
            STRUCT => self.parse_param_type_struct(tb),
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

    pub fn parse_param_type_family(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<ParamType, RuntimeError> {
        tb.skip_token(FAMILY)?;
        let name = self.parse_identifier_or_identifier_with_mod(tb)?;
        let params = self.parse_braced_objs(tb)?;
        Ok(ParamType::Family(FamilyObj { name, params }))
    }

    pub fn parse_param_type_struct(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<ParamType, RuntimeError> {
        tb.skip_token(STRUCT)?;
        let name = self.parse_identifier_or_identifier_with_mod(tb)?;
        let params = self.parse_braced_objs(tb)?;
        Ok(ParamType::Struct(StructObj { name, args: params }))
    }
}
