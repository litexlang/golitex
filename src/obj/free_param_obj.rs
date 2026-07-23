use crate::prelude::*;
use std::collections::HashMap;
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParamObjType {
    Identifier,
    Forall,
    DefHeader,
    Exist,
    SetBuilder,
    FnSet,
    Induc,
    DefAlgo,
    DefStructField,
    TupleIndex,
    CartIndex,
    TheoremInstantiation,
    AlphaRename,
    BinderRetag(BinderRetagSource),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinderRetagSource {
    Forall,
    Exist,
    FnSet,
    Induc,
    DefAlgo,
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
pub struct ForallFreeParamObj {
    pub name: String,
    pub symbol: SymbolRef,
}

#[derive(Clone, Debug)]
pub struct DefHeaderFreeParamObj {
    pub name: String,
    pub symbol: SymbolRef,
}

#[derive(Clone, Debug)]
pub struct ExistFreeParamObj {
    pub name: String,
    pub symbol: SymbolRef,
}

#[derive(Clone, Debug)]
pub struct SetBuilderFreeParamObj {
    pub name: String,
    pub symbol: SymbolRef,
}

#[derive(Clone, Debug)]
pub struct FnSetFreeParamObj {
    pub name: String,
    pub symbol: SymbolRef,
}

#[derive(Clone, Debug)]
pub struct ByInducFreeParamObj {
    pub name: String,
    pub symbol: SymbolRef,
}

#[derive(Clone, Debug)]
pub struct DefAlgoFreeParamObj {
    pub name: String,
    pub symbol: SymbolRef,
}

#[derive(Clone, Debug)]
pub struct DefStructFieldFreeParamObj {
    pub name: String,
    pub symbol: SymbolRef,
}

#[derive(Clone, Debug)]
pub struct TupleIndexFreeParamObj {
    pub name: String,
    pub symbol: SymbolRef,
}

#[derive(Clone, Debug)]
pub struct CartIndexFreeParamObj {
    pub name: String,
    pub symbol: SymbolRef,
}

impl ForallFreeParamObj {
    pub fn new(symbol: impl IntoSymbolRef) -> Self {
        let symbol = symbol.into_symbol_ref();
        ForallFreeParamObj {
            name: symbol.display_name().to_string(),
            symbol,
        }
    }
}

impl DefHeaderFreeParamObj {
    pub fn new(symbol: impl IntoSymbolRef) -> Self {
        let symbol = symbol.into_symbol_ref();
        DefHeaderFreeParamObj {
            name: symbol.display_name().to_string(),
            symbol,
        }
    }
}

impl ExistFreeParamObj {
    pub fn new(symbol: impl IntoSymbolRef) -> Self {
        let symbol = symbol.into_symbol_ref();
        ExistFreeParamObj {
            name: symbol.display_name().to_string(),
            symbol,
        }
    }
}

impl SetBuilderFreeParamObj {
    pub fn new(symbol: impl IntoSymbolRef) -> Self {
        let symbol = symbol.into_symbol_ref();
        SetBuilderFreeParamObj {
            name: symbol.display_name().to_string(),
            symbol,
        }
    }
}

impl FnSetFreeParamObj {
    pub fn new(symbol: impl IntoSymbolRef) -> Self {
        let symbol = symbol.into_symbol_ref();
        FnSetFreeParamObj {
            name: symbol.display_name().to_string(),
            symbol,
        }
    }
}

impl ByInducFreeParamObj {
    pub fn new(symbol: impl IntoSymbolRef) -> Self {
        let symbol = symbol.into_symbol_ref();
        ByInducFreeParamObj {
            name: symbol.display_name().to_string(),
            symbol,
        }
    }
}

impl DefAlgoFreeParamObj {
    pub fn new(symbol: impl IntoSymbolRef) -> Self {
        let symbol = symbol.into_symbol_ref();
        DefAlgoFreeParamObj {
            name: symbol.display_name().to_string(),
            symbol,
        }
    }
}

impl DefStructFieldFreeParamObj {
    pub fn new(symbol: impl IntoSymbolRef) -> Self {
        let symbol = symbol.into_symbol_ref();
        DefStructFieldFreeParamObj {
            name: symbol.display_name().to_string(),
            symbol,
        }
    }
}

impl TupleIndexFreeParamObj {
    pub fn new(symbol: impl IntoSymbolRef) -> Self {
        let symbol = symbol.into_symbol_ref();
        TupleIndexFreeParamObj {
            name: symbol.display_name().to_string(),
            symbol,
        }
    }
}

impl CartIndexFreeParamObj {
    pub fn new(symbol: impl IntoSymbolRef) -> Self {
        let symbol = symbol.into_symbol_ref();
        CartIndexFreeParamObj {
            name: symbol.display_name().to_string(),
            symbol,
        }
    }
}

macro_rules! impl_free_param_eq {
    ($($ty:ty),+ $(,)?) => {
        $(
            impl PartialEq for $ty {
                fn eq(&self, other: &Self) -> bool {
                    self.symbol == other.symbol
                }
            }

            impl Eq for $ty {}
        )+
    };
}

impl_free_param_eq!(
    ForallFreeParamObj,
    DefHeaderFreeParamObj,
    ExistFreeParamObj,
    SetBuilderFreeParamObj,
    FnSetFreeParamObj,
    ByInducFreeParamObj,
    DefAlgoFreeParamObj,
    DefStructFieldFreeParamObj,
    TupleIndexFreeParamObj,
    CartIndexFreeParamObj,
);

impl fmt::Display for ForallFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write_symbol_identity_spine(f, &self.symbol, &self.name)
    }
}

impl fmt::Display for DefHeaderFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write_symbol_identity_spine(f, &self.symbol, &self.name)
    }
}

impl fmt::Display for ExistFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write_symbol_identity_spine(f, &self.symbol, &self.name)
    }
}

impl fmt::Display for SetBuilderFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write_symbol_identity_spine(f, &self.symbol, &self.name)
    }
}

impl fmt::Display for FnSetFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write_symbol_identity_spine(f, &self.symbol, &self.name)
    }
}

impl fmt::Display for ByInducFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write_symbol_identity_spine(f, &self.symbol, &self.name)
    }
}

impl fmt::Display for DefAlgoFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write_symbol_identity_spine(f, &self.symbol, &self.name)
    }
}

impl fmt::Display for DefStructFieldFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write_symbol_identity_spine(f, &self.symbol, &self.name)
    }
}

impl fmt::Display for TupleIndexFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write_symbol_identity_spine(f, &self.symbol, &self.name)
    }
}

impl fmt::Display for CartIndexFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write_symbol_identity_spine(f, &self.symbol, &self.name)
    }
}

impl From<ForallFreeParamObj> for Obj {
    fn from(v: ForallFreeParamObj) -> Self {
        Obj::Atom(AtomObj::Forall(v))
    }
}

impl From<DefHeaderFreeParamObj> for Obj {
    fn from(v: DefHeaderFreeParamObj) -> Self {
        Obj::Atom(AtomObj::Def(v))
    }
}

impl From<ExistFreeParamObj> for Obj {
    fn from(v: ExistFreeParamObj) -> Self {
        Obj::Atom(AtomObj::Exist(v))
    }
}

impl From<SetBuilderFreeParamObj> for Obj {
    fn from(v: SetBuilderFreeParamObj) -> Self {
        Obj::Atom(AtomObj::SetBuilder(v))
    }
}

impl From<FnSetFreeParamObj> for Obj {
    fn from(v: FnSetFreeParamObj) -> Self {
        Obj::Atom(AtomObj::FnSet(v))
    }
}

impl From<ByInducFreeParamObj> for Obj {
    fn from(v: ByInducFreeParamObj) -> Self {
        Obj::Atom(AtomObj::Induc(v))
    }
}

impl From<DefAlgoFreeParamObj> for Obj {
    fn from(v: DefAlgoFreeParamObj) -> Self {
        Obj::Atom(AtomObj::DefAlgo(v))
    }
}

impl From<DefStructFieldFreeParamObj> for Obj {
    fn from(v: DefStructFieldFreeParamObj) -> Self {
        Obj::Atom(AtomObj::DefStructField(v))
    }
}

impl From<TupleIndexFreeParamObj> for Obj {
    fn from(v: TupleIndexFreeParamObj) -> Self {
        Obj::Atom(AtomObj::TupleIndex(v))
    }
}

impl From<CartIndexFreeParamObj> for Obj {
    fn from(v: CartIndexFreeParamObj) -> Self {
        Obj::Atom(AtomObj::CartIndex(v))
    }
}

/// Bound-parameter [`Obj`] for runtime-synthesized facts (`by` stmts, coverage, etc.), matching parse-time `~kind` tagging and [`Runtime::inst_obj`] substitution rules.
pub fn obj_for_bound_param_in_scope(binding: impl IntoSymbolRef, scope: ParamObjType) -> Obj {
    let symbol = binding.into_symbol_ref();
    match scope {
        ParamObjType::Forall => ForallFreeParamObj::new(symbol).into(),
        ParamObjType::Exist => ExistFreeParamObj::new(symbol).into(),
        ParamObjType::DefHeader => DefHeaderFreeParamObj::new(symbol).into(),
        ParamObjType::SetBuilder => SetBuilderFreeParamObj::new(symbol).into(),
        ParamObjType::FnSet => FnSetFreeParamObj::new(symbol).into(),
        ParamObjType::Induc => ByInducFreeParamObj::new(symbol).into(),
        ParamObjType::DefAlgo => DefAlgoFreeParamObj::new(symbol).into(),
        ParamObjType::DefStructField => DefStructFieldFreeParamObj::new(symbol).into(),
        ParamObjType::TupleIndex => TupleIndexFreeParamObj::new(symbol).into(),
        ParamObjType::CartIndex => CartIndexFreeParamObj::new(symbol).into(),
        ParamObjType::Identifier
        | ParamObjType::TheoremInstantiation
        | ParamObjType::AlphaRename
        | ParamObjType::BinderRetag(_) => {
            unreachable!(
                "obj_for_bound_param_in_scope: {:?} is not a bare-name binding scope",
                scope
            );
        }
    }
}

/// Element [`Obj`] for stored typing / membership facts so keys match parsed bound names (`~tag` spine).
pub fn param_binding_element_obj_for_store(
    binding: &SymbolBinding,
    binding_kind: ParamObjType,
) -> Obj {
    match binding_kind {
        ParamObjType::Identifier => {
            Identifier::new_bound(binding.name().to_string(), binding.as_ref()).into()
        }
        ParamObjType::Forall
        | ParamObjType::Exist
        | ParamObjType::DefHeader
        | ParamObjType::SetBuilder
        | ParamObjType::FnSet
        | ParamObjType::Induc
        | ParamObjType::DefAlgo
        | ParamObjType::DefStructField
        | ParamObjType::TupleIndex
        | ParamObjType::CartIndex => obj_for_bound_param_in_scope(binding, binding_kind),
        ParamObjType::TheoremInstantiation
        | ParamObjType::AlphaRename
        | ParamObjType::BinderRetag(_) => unreachable!(
            "param_binding_element_obj_for_store: instantiation modes are not binding kinds"
        ),
    }
}

#[cfg(test)]
mod strip_numeric_tags_tests {
    use super::strip_free_param_numeric_tags_in_display;

    #[test]
    fn tilde_digits_removed_suffix_kept() {
        assert_eq!(strip_free_param_numeric_tags_in_display("~2aaa"), "aaa");
        assert_eq!(
            strip_free_param_numeric_tags_in_display(r#""x": "~2foo""#),
            r#""x": "foo""#
        );
    }

    #[test]
    fn tilde_not_followed_by_digit_kept() {
        assert_eq!(
            strip_free_param_numeric_tags_in_display("~/tmp.lit"),
            "~/tmp.lit"
        );
        assert_eq!(strip_free_param_numeric_tags_in_display("~"), "~");
    }

    #[test]
    fn symbol_identity_prefix_is_removed_without_touching_ordinary_hash_text() {
        assert_eq!(
            strip_free_param_numeric_tags_in_display("#17#A::x = #42#y"),
            "A::x = y"
        );
        assert_eq!(
            strip_free_param_numeric_tags_in_display("#abc #12"),
            "#abc #12"
        );
    }

    #[test]
    fn generated_binder_names_are_stable_and_hide_internal_ids() {
        assert_eq!(
            strip_free_param_numeric_tags_in_display(
                "forall #17##binder_17, #42##binder_42: #17##binder_17 = #42##binder_42"
            ),
            "forall _generated_1, _generated_2: _generated_1 = _generated_2"
        );
    }
}
