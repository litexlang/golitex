use crate::prelude::*;
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
}

impl ParamObjType {
    pub fn free_param_display_tag(self) -> u8 {
        match self {
            ParamObjType::Identifier => 0,
            ParamObjType::Forall => 1,
            ParamObjType::DefHeader => 2,
            ParamObjType::Exist => 3,
            ParamObjType::SetBuilder => 4,
            ParamObjType::FnSet => 5,
            ParamObjType::Induc => 6,
            ParamObjType::DefAlgo => 7,
        }
    }
}

const FREE_PARAM_DISPLAY_TAG_PREFIX: char = '~';

fn write_parsing_free_param_tagged_spine(
    f: &mut fmt::Formatter<'_>,
    kind: ParamObjType,
    spine: &str,
) -> fmt::Result {
    write!(
        f,
        "{}{}{}",
        FREE_PARAM_DISPLAY_TAG_PREFIX,
        kind.free_param_display_tag(),
        spine
    )
}

pub fn strip_parsing_free_param_tags_for_user_display(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut it = text.chars().peekable();
    while let Some(c) = it.next() {
        if c == FREE_PARAM_DISPLAY_TAG_PREFIX {
            while it.peek().map(|x| x.is_ascii_digit()).unwrap_or(false) {
                it.next();
            }
        } else {
            out.push(c);
        }
    }
    out
}

/// Removes `~` plus following ASCII digits everywhere (e.g. `~2aaa` → `aaa`). Used on full
/// display JSON so every field is normalized; keeps `~` when not followed by digits (e.g. `~/`).
pub fn strip_free_param_numeric_tags_in_display(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut it = text.chars().peekable();
    while let Some(c) = it.next() {
        if c == FREE_PARAM_DISPLAY_TAG_PREFIX {
            if it.peek().map(|x| x.is_ascii_digit()).unwrap_or(false) {
                while it.peek().map(|x| x.is_ascii_digit()).unwrap_or(false) {
                    it.next();
                }
            } else {
                out.push(c);
            }
        } else {
            out.push(c);
        }
    }
    out
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForallFreeParamObj {
    pub name: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefHeaderFreeParamObj {
    pub name: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExistFreeParamObj {
    pub name: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SetBuilderFreeParamObj {
    pub name: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnSetFreeParamObj {
    pub name: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByInducFreeParamObj {
    pub name: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefAlgoFreeParamObj {
    pub name: String,
}

impl ForallFreeParamObj {
    pub fn new(name: String) -> Self {
        ForallFreeParamObj { name }
    }
}

impl DefHeaderFreeParamObj {
    pub fn new(name: String) -> Self {
        DefHeaderFreeParamObj { name }
    }
}

impl ExistFreeParamObj {
    pub fn new(name: String) -> Self {
        ExistFreeParamObj { name }
    }
}

impl SetBuilderFreeParamObj {
    pub fn new(name: String) -> Self {
        SetBuilderFreeParamObj { name }
    }
}

impl FnSetFreeParamObj {
    pub fn new(name: String) -> Self {
        FnSetFreeParamObj { name }
    }
}

impl ByInducFreeParamObj {
    pub fn new(name: String) -> Self {
        ByInducFreeParamObj { name }
    }
}

impl DefAlgoFreeParamObj {
    pub fn new(name: String) -> Self {
        DefAlgoFreeParamObj { name }
    }
}

impl fmt::Display for ForallFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_parsing_free_param_tagged_spine(f, ParamObjType::Forall, &self.name)
    }
}

impl fmt::Display for DefHeaderFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_parsing_free_param_tagged_spine(f, ParamObjType::DefHeader, &self.name)
    }
}

impl fmt::Display for ExistFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_parsing_free_param_tagged_spine(f, ParamObjType::Exist, &self.name)
    }
}

impl fmt::Display for SetBuilderFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_parsing_free_param_tagged_spine(f, ParamObjType::SetBuilder, &self.name)
    }
}

impl fmt::Display for FnSetFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_parsing_free_param_tagged_spine(f, ParamObjType::FnSet, &self.name)
    }
}

impl fmt::Display for ByInducFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_parsing_free_param_tagged_spine(f, ParamObjType::Induc, &self.name)
    }
}

impl fmt::Display for DefAlgoFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_parsing_free_param_tagged_spine(f, ParamObjType::DefAlgo, &self.name)
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

/// Bound-parameter [`Obj`] for runtime-synthesized facts (`by` stmts, coverage, etc.), matching parse-time `~kind` tagging and [`Runtime::inst_obj`] substitution rules.
pub fn obj_for_bound_param_in_scope(name: String, scope: ParamObjType) -> Obj {
    match scope {
        ParamObjType::Forall => ForallFreeParamObj::new(name).into(),
        ParamObjType::Exist => ExistFreeParamObj::new(name).into(),
        ParamObjType::DefHeader => DefHeaderFreeParamObj::new(name).into(),
        ParamObjType::SetBuilder => SetBuilderFreeParamObj::new(name).into(),
        ParamObjType::FnSet => FnSetFreeParamObj::new(name).into(),
        ParamObjType::Induc => ByInducFreeParamObj::new(name).into(),
        ParamObjType::DefAlgo => DefAlgoFreeParamObj::new(name).into(),
        ParamObjType::Identifier => {
            unreachable!(
                "obj_for_bound_param_in_scope: {:?} is not a bare-name binding scope",
                scope
            );
        }
    }
}

/// Element [`Obj`] for stored typing / membership facts so keys match parsed bound names (`~tag` spine).
pub fn param_binding_element_obj_for_store(name: String, binding_kind: ParamObjType) -> Obj {
    match binding_kind {
        ParamObjType::Identifier => Identifier::new(name).into(),
        ParamObjType::Forall
        | ParamObjType::Exist
        | ParamObjType::DefHeader
        | ParamObjType::SetBuilder
        | ParamObjType::FnSet
        | ParamObjType::Induc
        | ParamObjType::DefAlgo => obj_for_bound_param_in_scope(name, binding_kind),
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
}
