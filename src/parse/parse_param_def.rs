use crate::prelude::*;

impl Runtime {
    /// Each parameter group is pushed to [`Runtime::parsing_free_param_collection`] with
    /// `free_param_kind` after its shared type is parsed, so later groups can resolve earlier
    /// parameters without allowing same-group self references.
    pub fn parse_param_def_with_param_type_and_skip_comma(
        &mut self,
        tb: &mut TokenBlock,
        free_param_kind: ParamObjType,
    ) -> Result<ParamGroupWithParamType, RuntimeError> {
        let param = tb.advance()?;
        let param_def_with_param_type = if tb.current()? != COMMA {
            let params = vec![param];
            let param_type = self.parse_param_type(tb)?;
            self.parsing_free_param_collection.begin_scope(
                free_param_kind,
                &params,
                tb.line_file.clone(),
            )?;
            ParamGroupWithParamType::new(params, param_type)
        } else {
            let mut vec_of_params = vec![param];

            while tb.current_token_is_equal_to(COMMA) {
                tb.skip()?;
                let p = tb.advance()?;
                vec_of_params.push(p);
            }
            let param_type = self.parse_param_type(tb)?;
            self.parsing_free_param_collection.begin_scope(
                free_param_kind,
                &vec_of_params,
                tb.line_file.clone(),
            )?;

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
            s if s == FAMILY_OBJ_PREFIX => self
                .parse_family_obj(tb)
                .map(|f| ParamType::Obj(Obj::FamilyObj(f))),
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
