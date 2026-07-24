use crate::prelude::*;

impl Runtime {
    /// Each parameter group is pushed to the current frame's parse context with
    /// `free_param_kind` after its shared type is parsed, so later groups can resolve earlier
    /// parameters without allowing same-group self references.
    pub fn parse_param_def_with_param_type_and_skip_comma(
        &mut self,
        tb: &mut TokenBlock,
        free_param_kind: ParamObjType,
    ) -> Result<ParamGroupWithParamType, RuntimeError> {
        let param = tb.advance()?;
        let mut params = vec![param];
        while tb.current_token_is_equal_to(COMMA) {
            tb.skip()?;
            params.push(tb.advance()?);
        }
        let (param_type, default_struct_view) =
            self.parse_param_type_with_default_struct_view(tb)?;
        let bindings = self.begin_parsing_scope(free_param_kind, &params, tb.line_file.clone())?;
        if let Some(struct_obj) = default_struct_view {
            self.register_default_struct_view(&bindings, &struct_obj);
        }
        let param_def_with_param_type = ParamGroupWithParamType::new(bindings, param_type);
        if tb.current_token_is_equal_to(COMMA) {
            tb.skip_token(COMMA)?;
        }
        Ok(param_def_with_param_type)
    }

    pub fn parse_param_type(&mut self, tb: &mut TokenBlock) -> Result<ParamType, RuntimeError> {
        match tb.current()? {
            NONEMPTY_SET | COMPACT_NONEMPTY_SET => self.parse_param_type_nonempty_set(tb),
            FINITE_SET => self.parse_param_type_finite_set(tb),
            SET => self.parse_param_type_set(tb),
            _ => self.parse_param_type_obj(tb),
        }
    }

    pub(crate) fn parse_obj_with_default_struct_view(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<(Obj, Option<StructObj>), RuntimeError> {
        let obj = self.parse_obj(tb)?;
        let default_struct_view = match &obj {
            Obj::StructObj(struct_obj) => Some(struct_obj.clone()),
            _ => None,
        };
        Ok((obj, default_struct_view))
    }

    pub fn parse_param_type_nonempty_set(
        &self,
        tb: &mut TokenBlock,
    ) -> Result<ParamType, RuntimeError> {
        tb.skip()?;
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

    fn parse_param_type_with_default_struct_view(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<(ParamType, Option<StructObj>), RuntimeError> {
        let param_type = self.parse_param_type(tb)?;
        let default_struct_view = match &param_type {
            ParamType::Obj(Obj::StructObj(struct_obj)) => Some(struct_obj.clone()),
            _ => None,
        };
        Ok((param_type, default_struct_view))
    }
}
