use crate::prelude::*;

impl Runtime {
    /// Each parameter name is pushed to [`Runtime::parsing_free_param_collection`] with `free_param_kind`
    /// before its shared type is parsed, so later parameter types in the same group (or later groups)
    /// can resolve earlier parameters. Use [`ParamObjType::DefHeader`] for `prop { ... }` and `family`
    /// headers, [`ParamObjType::Forall`] for `forall`, [`ParamObjType::Exist`] for `exist`, [`ParamObjType::Identifier`] for `let` / `have`, etc.
    pub fn parse_param_def_with_param_type_and_skip_comma(
        &mut self,
        tb: &mut TokenBlock,
        free_param_kind: ParamObjType,
    ) -> Result<ParamGroupWithParamType, RuntimeError> {
        let param = tb.advance()?;
        let owned = param.clone();
        self.parsing_free_param_collection.begin_scope(
            free_param_kind,
            std::slice::from_ref(&owned),
            tb.line_file.clone(),
        )?;
        let param_def_with_param_type = if tb.current()? != COMMA {
            ParamGroupWithParamType::new(vec![param], self.parse_param_type(tb)?)
        } else {
            let mut vec_of_params = vec![param];

            while tb.current_token_is_equal_to(COMMA) {
                tb.skip()?;
                let p = tb.advance()?;
                let owned = p.clone();
                self.parsing_free_param_collection.begin_scope(
                    free_param_kind,
                    std::slice::from_ref(&owned),
                    tb.line_file.clone(),
                )?;
                vec_of_params.push(p);
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
            RESTRICTIVE => self.parse_param_type_restrictive(tb),
            s if s == FAMILY_OBJ_PREFIX => self
                .parse_family_obj(tb)
                .map(|f| ParamType::Obj(Obj::FamilyObj(f))),
            _ => self.parse_param_type_obj(tb),
        }
    }

    pub fn parse_param_type_restrictive(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<ParamType, RuntimeError> {
        tb.skip_token(RESTRICTIVE)?;
        tb.skip_token(LEFT_BRACE)?;
        // Same shape as the second argument of `$restrict_fn_in`: `fn` + fn-set.
        tb.skip_token(FN_LOWER_CASE)?;
        let fn_set = self.parse_fn_set(tb)?;
        tb.skip_token(RIGHT_BRACE)?;
        Ok(ParamType::Restrictive(fn_set))
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
