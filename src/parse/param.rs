use super::keywords::{
    COLON, COMMA, EQUAL, FINITE_SET, GREATER, LEFT_PAREN, LESS, NONEMPTY_SET, RIGHT_ARROW,
    RIGHT_PAREN, SET,
};
use super::object::{is_atom_name, parse_obj};
use crate::ast::param::{
    FiniteSet, NonemptySet, ParamType, Set, TypedParameterGroup, TypedParameterList,
};
use crate::runtime::{Runtime, RuntimeParseError, RuntimeResult};
use crate::tokenize::TokenBlock;

impl Runtime {
    // Parse `x R` / `x, y R` groups until `:` (consumed).
    // Empty list allowed for parameterless `forall:` / `not forall:`.
    pub(super) fn parse_typed_param_list_until_colon_allow_empty(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<TypedParameterList> {
        let params = self.parse_typed_param_list_until_colon_or_arrow_allow_empty(tb, true)?;
        tb.expect(COLON)?;
        Ok(params)
    }

    // `allow_empty`: parameterless `forall:` / `forall => P` (no binders).
    pub(super) fn parse_typed_param_list_until_colon_or_arrow_allow_empty(
        &mut self,
        tb: &mut TokenBlock,
        allow_empty: bool,
    ) -> RuntimeResult<TypedParameterList> {
        let mut groups = Vec::new();
        while !tb.exceed_end_of_head() && tb.peek() != Some(COLON) && tb.peek() != Some(RIGHT_ARROW)
        {
            groups.push(self.parse_one_typed_param_group(tb)?);
            if tb.peek() == Some(COMMA) {
                tb.advance()?;
            }
        }
        if groups.is_empty() && !allow_empty {
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

    // Parse `x R` / `x, y R` groups until `=` / `:` / end of header
    // (delimiter not consumed).
    pub(super) fn parse_typed_param_list_until_eq_colon_or_end(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<TypedParameterList> {
        let mut groups = Vec::new();
        while !tb.exceed_end_of_head() && tb.peek() != Some(EQUAL) && tb.peek() != Some(COLON) {
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

    // Parse `(x R, y S)` or `()` for a nullary concrete proposition.
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

    // Parse `(x, y)` or `()` for an abstract proposition — defines each atom.
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
    ) -> RuntimeResult<crate::ast::names::BoundName> {
        if crate::builtin_theorem::is_reserved_builtin_name(&name)
            || super::keywords::is_reserved_object_name(&name)
        {
            return Err(tb.parse_error(format!("`{name}` is a reserved builtin name")));
        }
        self.define_plain_atom(name).map_err(|err| match err {
            crate::runtime::RuntimeError::InternalBug(message) => {
                RuntimeParseError::new(message, tb.line, tb.source_path.clone()).into()
            }
            other => other,
        })
    }

    pub(super) fn occupy_bound_name_as_parse(
        &mut self,
        tb: &TokenBlock,
        bound: &crate::ast::names::BoundName,
    ) -> RuntimeResult<()> {
        self.occupy_bound_name(bound).map_err(|err| match err {
            crate::runtime::RuntimeError::InternalBug(message) => {
                RuntimeParseError::new(message, tb.line, tb.source_path.clone()).into()
            }
            other => other,
        })
    }

    // Reopen exactly the bindings used by the function's domain conditions;
    // parameter domains and the return carrier have already been parsed.
    pub(super) fn occupy_set_bound_parameters_as_parse(
        &mut self,
        tb: &TokenBlock,
        params: &crate::ast::param::SetBoundParameterList,
    ) -> RuntimeResult<()> {
        for group in &params.groups {
            for param in &group.params {
                self.occupy_bound_name_as_parse(tb, param)?;
            }
        }
        Ok(())
    }
}
