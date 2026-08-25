use crate::prelude::*;
use std::collections::HashMap;
use std::fmt;

/// Operational policy for introducing a symbol into a parser/runtime scope.
/// The enclosing AST, rather than the occurrence object, owns whether that
/// binder came from `forall`, `exist`, a set builder, or a function set.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindingScope {
    DefinitionBinding,
    LocalBinder,
    StructureField,
    ReuseActiveBinder,
}

/// Operation performed while rebuilding an object or fact.
///
/// These variants say how substitution is performed; they do not encode which
/// AST construct owns a binder.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SubstitutionMode {
    Exact,
    Named,
    Theorem,
    /// Replace an executed `let` symbol by its stored transparent object
    /// definition while retaining parser occurrence provenance on the
    /// surrounding syntax tree.
    TransparentDefinition,
}

impl BindingScope {
    pub fn is_definition_binding(self) -> bool {
        self == Self::DefinitionBinding
    }

    pub fn reuses_active_binding(self) -> bool {
        self == Self::ReuseActiveBinder
    }

    pub fn respects_bare_symbols(self, name: &str) -> bool {
        !name.starts_with("#binder_") && self != Self::StructureField
    }
}

pub const FREE_PARAM_DISPLAY_TAG_PREFIX: char = '~';

fn write_symbol_identity_spine(
    f: &mut fmt::Formatter<'_>,
    symbol: &SymbolRef,
    spine: &str,
) -> Result<(), fmt::Error> {
    write!(f, "{}", symbol.identity_spine(spine))
}

pub fn strip_parsing_free_param_tags_for_user_display(text: &str) -> String {
    strip_free_param_numeric_tags_in_display(text)
}

/// Removes internal binder identity prefixes from finished user-facing output.
///
/// The current representation is `#<symbol-id>#name`; legacy `~<kind>tag` prefixes are
/// also accepted while old serialized artifacts still exist.
pub fn strip_free_param_numeric_tags_in_display(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let chars = text.chars().collect::<Vec<_>>();
    let mut generated_names = HashMap::new();
    let mut index = 0;
    while index < chars.len() {
        if chars[index] == '#' {
            let digits_start = index + 1;
            let mut after_digits = digits_start;
            while after_digits < chars.len() && chars[after_digits].is_ascii_digit() {
                after_digits += 1;
            }
            if after_digits > digits_start
                && after_digits < chars.len()
                && chars[after_digits] == '#'
            {
                index = after_digits + 1;
                continue;
            }

            let internal_prefix = "#binder_".chars().collect::<Vec<_>>();
            if chars[index..].starts_with(&internal_prefix) {
                let digits_start = index + internal_prefix.len();
                let mut after_digits = digits_start;
                while after_digits < chars.len() && chars[after_digits].is_ascii_digit() {
                    after_digits += 1;
                }
                if after_digits > digits_start {
                    let internal_name = chars[index..after_digits].iter().collect::<String>();
                    let next_display_index = generated_names.len() + 1;
                    let display_name = generated_names
                        .entry(internal_name)
                        .or_insert_with(|| format!("_generated_{}", next_display_index));
                    out.push_str(display_name);
                    index = after_digits;
                    continue;
                }
            }
        }
        if chars[index] == FREE_PARAM_DISPLAY_TAG_PREFIX {
            let mut after_digits = index + 1;
            while after_digits < chars.len() && chars[after_digits].is_ascii_digit() {
                after_digits += 1;
            }
            if after_digits > index + 1 {
                index = after_digits;
                continue;
            }
        }
        out.push(chars[index]);
        index += 1;
    }
    out
}

#[derive(Clone, Debug)]
pub struct BoundParamObj {
    pub symbol: SymbolRef,
}

impl BoundParamObj {
    pub fn new(symbol: impl IntoSymbolRef) -> Self {
        Self {
            symbol: symbol.into_symbol_ref(),
        }
    }

    pub fn name(&self) -> &str {
        self.symbol.display_name()
    }
}

impl PartialEq for BoundParamObj {
    fn eq(&self, other: &Self) -> bool {
        self.symbol == other.symbol
    }
}

impl Eq for BoundParamObj {}

impl fmt::Display for BoundParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write_symbol_identity_spine(f, &self.symbol, self.name())
    }
}

impl From<BoundParamObj> for Obj {
    fn from(v: BoundParamObj) -> Self {
        Obj::Atom(AtomObj::Bound(v))
    }
}

/// Bound-parameter [`Obj`] for runtime-synthesized facts.
///
/// The binder's syntactic source (forall/exist/function/etc.) belongs to the
/// enclosing AST node. Occurrences carry only their symbol identity.
pub fn obj_for_bound_param_in_scope(binding: impl IntoSymbolRef) -> Obj {
    BoundParamObj::new(binding).into()
}

/// Element [`Obj`] for stored typing / membership facts so keys match parsed bound names (`~tag` spine).
pub fn param_binding_element_obj_for_store(
    binding: &SymbolBinding,
    binding_scope: BindingScope,
) -> Obj {
    if binding_scope.is_definition_binding() {
        Identifier::new_bound(binding.name().to_string(), binding.as_ref()).into()
    } else {
        obj_for_bound_param_in_scope(binding)
    }
}

#[cfg(test)]
#[path = "../../tests/unit/obj/free_param_obj/strip_numeric_tags_tests.rs"]
mod strip_numeric_tags_tests;
