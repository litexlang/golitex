use super::keywords::{
    BY, COLON, COMMA, EQUAL, FINITE_SET, GREATER, LEFT_PAREN, LESS, NONEMPTY_SET, RIGHT_ARROW,
    RIGHT_PAREN, SET,
};
use super::object::{is_atom_name, parse_obj};
use crate::new_pipeline::ast::param::{
    FiniteSet, NonemptySet, ParamType, Set, TypedParameterGroup, TypedParameterList,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeParseError, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

impl Runtime {
    // Parse `x R` / `x, y R` groups until `:` (consumed).
    // Defines each parameter atom in the current parse scope.
    pub(super) fn parse_typed_param_list_until_colon(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<TypedParameterList> {
        let params = self.parse_typed_param_list_until_colon_or_arrow(tb)?;
        tb.expect(COLON)?;
        Ok(params)
    }

    // Parse `x R` / `x, y R` groups until `:` or `=>` (delimiter not consumed).
    // Used by inline `forall x Dom => P` and block `forall x Dom:`.
    pub(super) fn parse_typed_param_list_until_colon_or_arrow(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<TypedParameterList> {
        let mut groups = Vec::new();
        while !tb.exceed_end_of_head()
            && tb.peek() != Some(COLON)
            && tb.peek() != Some(RIGHT_ARROW)
        {
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

    // Parse `x R` / `x, y R` groups until `=` / `:` / `by` / end of header
    // (delimiter not consumed). `by` stops for `have Img set by replacement_axiom(...)`.
    pub(super) fn parse_typed_param_list_until_eq_colon_or_end(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<TypedParameterList> {
        let mut groups = Vec::new();
        while !tb.exceed_end_of_head()
            && tb.peek() != Some(EQUAL)
            && tb.peek() != Some(COLON)
            && tb.peek() != Some(BY)
        {
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

    // Parse `(x R, y S)` — defines each parameter atom.
    pub(super) fn parse_typed_param_list_in_parens(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<TypedParameterList> {
        tb.expect(LEFT_PAREN)?;
        let mut groups = Vec::new();
        while !tb.exceed_end_of_head() && tb.peek() != Some(RIGHT_PAREN) {
            groups.push(self.parse_one_typed_param_group(tb)?);
            if tb.peek() == Some(COMMA) {
                tb.advance()?;
            }
        }
        tb.expect(RIGHT_PAREN)?;
        if groups.is_empty() {
            return Err(RuntimeParseError::new(
                "expected at least one parameter inside `(...)`",
                tb.line,
                tb.source_path.clone(),
            )
            .into());
        }
        Ok(TypedParameterList { groups })
    }

    // Parse `<x R, y S>` — same groups as `(...)`, for `struct Name<...>:`.
    pub(super) fn parse_typed_param_list_in_angles(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<TypedParameterList> {
        tb.expect(LESS)?;
        let mut groups = Vec::new();
        while !tb.exceed_end_of_head() && tb.peek() != Some(GREATER) {
            groups.push(self.parse_one_typed_param_group(tb)?);
            if tb.peek() == Some(COMMA) {
                tb.advance()?;
            }
        }
        tb.expect(GREATER)?;
        if groups.is_empty() {
            return Err(RuntimeParseError::new(
                "expected at least one parameter inside `<...>`",
                tb.line,
                tb.source_path.clone(),
            )
            .into());
        }
        Ok(TypedParameterList { groups })
    }

    // Parse `(x, y)` bare names — defines each atom.
    // Returns surface strings for stmt-only param lists (e.g. abstract_prop).
    pub(super) fn parse_name_list_in_parens(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<Vec<String>> {
        tb.expect(LEFT_PAREN)?;
        let mut names = Vec::new();
        while !tb.exceed_end_of_head() && tb.peek() != Some(RIGHT_PAREN) {
            let name = tb.advance()?;
            if !is_atom_name(&name) {
                return Err(RuntimeParseError::new(
                    format!("invalid parameter name `{name}`"),
                    tb.line,
                    tb.source_path.clone(),
                )
                .into());
            }
            let bound = self.define_plain_atom_as_parse(tb, name)?;
            names.push(bound.name);
            if tb.peek() == Some(COMMA) {
                tb.advance()?;
            }
        }
        tb.expect(RIGHT_PAREN)?;
        if names.is_empty() {
            return Err(RuntimeParseError::new(
                "expected at least one name inside `(...)`",
                tb.line,
                tb.source_path.clone(),
            )
            .into());
        }
        Ok(names)
    }

    pub(super) fn parse_one_typed_param_group(
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
        params.push(self.define_plain_atom_as_parse(tb, name)?);

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
            params.push(self.define_plain_atom_as_parse(tb, next)?);
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
            _ => Ok(ParamType::Obj(parse_obj(self, tb)?)),
        }
    }

    pub(super) fn define_plain_atom_as_parse(
        &mut self,
        tb: &TokenBlock,
        name: String,
    ) -> RuntimeResult<crate::new_pipeline::ast::names::BoundName> {
        self.define_plain_atom(name).map_err(|err| match err {
            crate::new_pipeline::runtime::RuntimeError::InternalBug(message) => {
                RuntimeParseError::new(message, tb.line, tb.source_path.clone()).into()
            }
            other => other,
        })
    }

    pub(super) fn occupy_bound_name_as_parse(
        &mut self,
        tb: &TokenBlock,
        bound: &crate::new_pipeline::ast::names::BoundName,
    ) -> RuntimeResult<()> {
        self.occupy_bound_name(bound).map_err(|err| match err {
            crate::new_pipeline::runtime::RuntimeError::InternalBug(message) => {
                RuntimeParseError::new(message, tb.line, tb.source_path.clone()).into()
            }
            other => other,
        })
    }
}
