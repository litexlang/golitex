use super::keywords::{COLON, COMMA, FINITE_SET, NONEMPTY_SET, SET};
use super::object::{is_atom_name, parse_obj};
use crate::new_pipeline::ast::param::{
    FiniteSet, NonemptySet, ParamType, Set, TypedParameterGroup, TypedParameterList,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeParseError, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

impl Runtime {
    // Parse `x R` / `x, y R` groups until `:` (consumed).
    // Occupies each parameter name in the current parse scope.
    pub(super) fn parse_typed_param_list_until_colon(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<TypedParameterList> {
        let mut groups = Vec::new();
        while !tb.exceed_end_of_head() && tb.peek() != Some(COLON) {
            groups.push(self.parse_one_typed_param_group(tb)?);
            if tb.peek() == Some(COMMA) {
                tb.advance()?;
            }
        }
        tb.expect(COLON)?;
        if groups.is_empty() {
            return Err(RuntimeParseError::new(
                "expected at least one parameter",
                tb.line,
                tb.source_path.clone(),
            )
            .into());
        }
        Ok(TypedParameterList { groups })
    }

    // Parse `x R` / `x, y R` groups until `st` (not consumed).
    pub(super) fn parse_typed_param_list_until_st(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<TypedParameterList> {
        let mut groups = Vec::new();
        while !tb.exceed_end_of_head() && tb.peek() != Some(super::keywords::ST) {
            groups.push(self.parse_one_typed_param_group(tb)?);
            if tb.peek() == Some(COMMA) {
                tb.advance()?;
            }
        }
        if groups.is_empty() {
            return Err(RuntimeParseError::new(
                "expected at least one parameter",
                tb.line,
                tb.source_path.clone(),
            )
            .into());
        }
        Ok(TypedParameterList { groups })
    }

    fn parse_one_typed_param_group(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<TypedParameterGroup> {
        let mut params = Vec::new();
        let name = tb.advance()?;
        if !is_atom_name(&name) {
            return Err(RuntimeParseError::new(
                format!("invalid parameter name `{name}`"),
                tb.line,
                tb.source_path.clone(),
            )
            .into());
        }
        self.occupy_name_as_parse(tb, name.clone())?;
        params.push(name);

        while tb.peek() == Some(COMMA) {
            // More names in this group: `x, y R`. Group separators are handled
            // by the outer list loop after the shared type is parsed.
            tb.advance()?;
            let next = tb.advance()?;
            if !is_atom_name(&next) {
                return Err(RuntimeParseError::new(
                    format!("invalid parameter name `{next}`"),
                    tb.line,
                    tb.source_path.clone(),
                )
                .into());
            }
            self.occupy_name_as_parse(tb, next.clone())?;
            params.push(next);
        }

        let param_type = self.parse_param_type(tb)?;
        Ok(TypedParameterGroup { params, param_type })
    }

    fn parse_param_type(&mut self, tb: &mut TokenBlock) -> RuntimeResult<ParamType> {
        match tb.peek() {
            Some(NONEMPTY_SET) => {
                tb.advance()?;
                Ok(ParamType::NonemptySet(NonemptySet {}))
            }
            Some(FINITE_SET) => {
                tb.advance()?;
                Ok(ParamType::FiniteSet(FiniteSet {}))
            }
            Some(SET) => {
                tb.advance()?;
                Ok(ParamType::Set(Set {}))
            }
            _ => Ok(ParamType::Obj(parse_obj(tb)?)),
        }
    }

    pub(super) fn occupy_name_as_parse(
        &mut self,
        tb: &TokenBlock,
        name: String,
    ) -> RuntimeResult<()> {
        self.occupy_name(name).map_err(|err| match err {
            crate::new_pipeline::runtime::RuntimeError::Invariant(message) => {
                RuntimeParseError::new(message, tb.line, tb.source_path.clone()).into()
            }
            other => other,
        })
    }
}
