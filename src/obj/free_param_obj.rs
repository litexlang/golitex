use crate::prelude::*;
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParamObjType {
    Identifier,
    Forall,
    DefProp,
    Exist,
    SetBuilder,
    FnSet,
    StructSelf,
    Induc,
    DefAlgo,
}

impl ParamObjType {
    pub fn free_param_display_tag(self) -> u8 {
        match self {
            ParamObjType::Identifier => 0,
            ParamObjType::Forall => 1,
            ParamObjType::DefProp => 2,
            ParamObjType::Exist => 3,
            ParamObjType::SetBuilder => 4,
            ParamObjType::FnSet => 5,
            ParamObjType::StructSelf => 6,
            ParamObjType::Induc => 7,
            ParamObjType::DefAlgo => 8,
        }
    }
}

pub type InstObjState = ParamObjType;
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForallFreeParamObj {
    pub name: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefPropFreeParamObj {
    pub name: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForallFieldAccessObj {
    pub name: String,
    pub field: String,
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
pub struct StructSelfFieldFreeParamObj {
    pub field: String,
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

impl ForallFieldAccessObj {
    pub fn new(name: String, field: String) -> Self {
        ForallFieldAccessObj { name, field }
    }
}

impl DefPropFreeParamObj {
    pub fn new(name: String) -> Self {
        DefPropFreeParamObj { name }
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

impl StructSelfFieldFreeParamObj {
    pub fn new(field: String) -> Self {
        StructSelfFieldFreeParamObj { field }
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

impl fmt::Display for ForallFieldAccessObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let spine = field_access_to_string(&self.name, &self.field);
        write_parsing_free_param_tagged_spine(f, ParamObjType::Forall, &spine)
    }
}

impl fmt::Display for DefPropFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_parsing_free_param_tagged_spine(f, ParamObjType::DefProp, &self.name)
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

impl fmt::Display for StructSelfFieldFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let spine = field_access_to_string(SELF, &self.field);
        write_parsing_free_param_tagged_spine(f, ParamObjType::StructSelf, &spine)
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
        Obj::ForallFreeParamObj(v)
    }
}

impl From<ForallFieldAccessObj> for Obj {
    fn from(v: ForallFieldAccessObj) -> Self {
        Obj::ForallFieldAccessObj(v)
    }
}

impl From<DefPropFreeParamObj> for Obj {
    fn from(v: DefPropFreeParamObj) -> Self {
        Obj::DefFreeParamObj(v)
    }
}

impl From<ExistFreeParamObj> for Obj {
    fn from(v: ExistFreeParamObj) -> Self {
        Obj::ExistFreeParamObj(v)
    }
}

impl From<SetBuilderFreeParamObj> for Obj {
    fn from(v: SetBuilderFreeParamObj) -> Self {
        Obj::SetBuilderFreeParamObj(v)
    }
}

impl From<FnSetFreeParamObj> for Obj {
    fn from(v: FnSetFreeParamObj) -> Self {
        Obj::FnSetFreeParamObj(v)
    }
}

impl From<StructSelfFieldFreeParamObj> for Obj {
    fn from(v: StructSelfFieldFreeParamObj) -> Self {
        Obj::StructSelfFieldFreeParamObj(v)
    }
}

impl From<ByInducFreeParamObj> for Obj {
    fn from(v: ByInducFreeParamObj) -> Self {
        Obj::ByInducFreeParamObj(v)
    }
}

impl From<DefAlgoFreeParamObj> for Obj {
    fn from(v: DefAlgoFreeParamObj) -> Self {
        Obj::DefAlgoFreeParamObj(v)
    }
}
