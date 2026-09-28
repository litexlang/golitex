//! Bare, qualified, struct-carrier, and template-backed object references.

use crate::prelude::*;

use super::expression::{
    parse_synthetically_correct_identifier_string, validate_litex_name_for_parse,
    validate_module_path_segment_for_parse,
};

impl Runtime {
    pub fn parse_identifier(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let left = parse_synthetically_correct_identifier_string(tb)?;
        Ok(Identifier::new(left).into())
    }

    fn parse_mod_qualified_atom(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let mut parts = vec![parse_synthetically_correct_identifier_string(tb)?];
        while !tb.exceed_end_of_head() && tb.current()? == MOD_SIGN {
            tb.skip_token(MOD_SIGN)?;
            parts.push(parse_synthetically_correct_identifier_string(tb)?);
        }
        let right = parts
            .pop()
            .expect("qualified name should have a local name");
        let left = self.canonical_module_name_for_parse(&parts.join(MOD_SIGN));
        let identifier = match self.resolved_qualified_identifier_symbol(&left, &right) {
            Some(symbol) => IdentifierWithMod::new_bound(left, right, symbol),
            None => IdentifierWithMod::new(left, right),
        };
        Ok(identifier.into())
    }

    /// Unqualified or `::`-qualified name / field name; returns a name-shaped [`Obj`].
    pub fn parse_identifier_or_identifier_with_mod(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Obj, RuntimeError> {
        let next_is_mod = tb.token_at_add_index(1) == MOD_SIGN;
        if next_is_mod {
            self.parse_mod_qualified_atom(tb)
        } else {
            self.parse_identifier(tb)
        }
    }

    pub fn parse_predicate(&mut self, tb: &mut TokenBlock) -> Result<AtomicName, RuntimeError> {
        self.parse_atomic_name(tb)
    }

    pub fn parse_struct_carrier_obj(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        tb.skip_token(STRUCT_VIEW_PREFIX)?;
        let struct_obj = self.parse_struct_obj_after_prefix(tb)?;

        if !tb.exceed_end_of_head() && tb.current()? == LEFT_CURLY_BRACE {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "explicit struct selection `&Struct{object}.field` has been removed; define the object or function return directly with `&Struct` and write `object.field`"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(struct_obj.into())
    }

    fn parse_struct_obj_after_prefix(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<StructObj, RuntimeError> {
        let name = self.parse_module_qualified_reference_name(tb)?;
        let params = if !tb.exceed_end_of_head() && tb.current()? == LESS {
            self.parse_angle_bracketed_objs(tb)?
        } else if !tb.exceed_end_of_head() && tb.current()? == LEFT_BRACE {
            self.parse_braced_objs(tb)?
        } else {
            vec![]
        };
        Ok(StructObj::new(name, params))
    }

    /// `ident` or `mod::ident` as a predicate/atomic name in parse position.
    pub fn parse_atomic_name(&mut self, tb: &mut TokenBlock) -> Result<AtomicName, RuntimeError> {
        let left = parse_synthetically_correct_identifier_string(tb)?;
        if !tb.exceed_end_of_head() && tb.current()? == MOD_SIGN {
            let mut parts = vec![left];
            while !tb.exceed_end_of_head() && tb.current()? == MOD_SIGN {
                tb.skip()?;
                parts.push(parse_synthetically_correct_identifier_string(tb)?);
            }
            let right = parts
                .pop()
                .expect("qualified name should have a local name");
            let module_name = self.canonical_module_name_for_parse(&parts.join(MOD_SIGN));
            Ok(AtomicName::WithMod(module_name, right))
        } else {
            Ok(self.parse_bare_atomic_name(left))
        }
    }

    pub fn parse_module_qualified_reference_name(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<AtomicName, RuntimeError> {
        let left = tb.advance()?;
        if !tb.exceed_end_of_head() && tb.current()? == MOD_SIGN {
            let mut parts = vec![left];
            while !tb.exceed_end_of_head() && tb.current()? == MOD_SIGN {
                tb.skip_token(MOD_SIGN)?;
                let part = tb.advance()?;
                parts.push(part);
            }
            let right = parts
                .pop()
                .expect("qualified name should have a local name");
            for (index, part) in parts.iter().enumerate() {
                validate_module_path_segment_for_parse(part, index == 0, tb.line_file.clone())?;
            }
            validate_litex_name_for_parse(&right, tb.line_file.clone())?;
            let module_name = self.canonical_module_name_for_parse(&parts.join(MOD_SIGN));
            Ok(AtomicName::WithMod(module_name, right))
        } else {
            validate_litex_name_for_parse(&left, tb.line_file.clone())?;
            Ok(self.parse_bare_atomic_name(left))
        }
    }

    fn current_parse_module_name(&self) -> Option<String> {
        self.current_parse_namespace().map(str::to_string)
    }

    pub(super) fn qualify_bare_identifier_if_needed(&self, id: Identifier) -> Obj {
        if is_builtin_identifier_name(&id.name) {
            let symbol =
                builtin_symbol_ref(&id.name).expect("builtin identifiers have stable symbol IDs");
            return Identifier::new_bound(id.name, symbol).into();
        }
        let symbol = self.resolved_identifier_symbol(&id.name);
        let Some(module_name) = self.current_parse_module_name() else {
            return match symbol {
                Some(symbol) => Identifier::new_bound(id.name, symbol).into(),
                None => id.into(),
            };
        };
        match symbol {
            Some(symbol) => IdentifierWithMod::new_bound(module_name, id.name, symbol).into(),
            None => IdentifierWithMod::new(module_name, id.name).into(),
        }
    }

    pub(super) fn parse_bare_atomic_name(&self, name: String) -> AtomicName {
        if is_builtin_predicate(&name) {
            return AtomicName::WithoutMod(name);
        }
        // At a use site, keep the source spelling authoritative: a module
        // qualifier is accepted only when written explicitly. Definition
        // bodies are the one canonicalization boundary: their local bare
        // names are owned by the module that stores the definition, so an
        // imported theorem can still resolve its own predicates/templates.
        if self.parsing_definition_depth > 0 {
            if let Some(module_name) = self.current_parse_module_name() {
                return AtomicName::WithMod(module_name, name);
            }
        }
        AtomicName::WithoutMod(name)
    }
}
