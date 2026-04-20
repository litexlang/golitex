use super::field_access_to_string;
use super::Obj;
use crate::common::keywords::SELF;
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForallFreeParamObj {
    pub name: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefFreeParamObj {
    pub name: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForallFreeParamFieldAccess {
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

impl ForallFreeParamObj {
    pub fn new(name: String) -> Self {
        ForallFreeParamObj { name }
    }
}

impl ForallFreeParamFieldAccess {
    pub fn new(name: String, field: String) -> Self {
        ForallFreeParamFieldAccess { name, field }
    }
}

impl DefFreeParamObj {
    pub fn new(name: String) -> Self {
        DefFreeParamObj { name }
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

impl fmt::Display for ForallFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl fmt::Display for ForallFreeParamFieldAccess {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", field_access_to_string(&self.name, &self.field))
    }
}

impl fmt::Display for DefFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl fmt::Display for ExistFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl fmt::Display for SetBuilderFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl fmt::Display for FnSetFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl fmt::Display for StructSelfFieldFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", field_access_to_string(SELF, &self.field))
    }
}

impl From<ForallFreeParamObj> for Obj {
    fn from(v: ForallFreeParamObj) -> Self {
        Obj::ForallFreeParam(v)
    }
}

impl From<ForallFreeParamFieldAccess> for Obj {
    fn from(v: ForallFreeParamFieldAccess) -> Self {
        Obj::ForallFreeParamFieldAccess(v)
    }
}

impl From<DefFreeParamObj> for Obj {
    fn from(v: DefFreeParamObj) -> Self {
        Obj::DefFreeParam(v)
    }
}

impl From<ExistFreeParamObj> for Obj {
    fn from(v: ExistFreeParamObj) -> Self {
        Obj::ExistFreeParam(v)
    }
}

impl From<SetBuilderFreeParamObj> for Obj {
    fn from(v: SetBuilderFreeParamObj) -> Self {
        Obj::SetBuilderFreeParam(v)
    }
}

impl From<FnSetFreeParamObj> for Obj {
    fn from(v: FnSetFreeParamObj) -> Self {
        Obj::FnSetFreeParam(v)
    }
}

impl From<StructSelfFieldFreeParamObj> for Obj {
    fn from(v: StructSelfFieldFreeParamObj) -> Self {
        Obj::StructSelfFieldFreeParam(v)
    }
}
