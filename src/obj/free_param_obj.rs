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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByInducFreeParamObj {
    pub name: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FreeParamObj {
    Forall(ForallFreeParamObj),
    ForallFieldAccess(ForallFreeParamFieldAccess),
    Def(DefFreeParamObj),
    Exist(ExistFreeParamObj),
    SetBuilder(SetBuilderFreeParamObj),
    FnSet(FnSetFreeParamObj),
    StructSelfField(StructSelfFieldFreeParamObj),
    Induc(ByInducFreeParamObj),
}

impl FreeParamObj {
    pub fn replace_bound_identifier(self, from: &str, to: &str) -> Self {
        if from == to {
            return self;
        }
        match self {
            FreeParamObj::Forall(p) => {
                let name = if p.name == from {
                    to.to_string()
                } else {
                    p.name
                };
                FreeParamObj::Forall(ForallFreeParamObj::new(name))
            }
            FreeParamObj::ForallFieldAccess(p) => {
                let name = if p.name == from {
                    to.to_string()
                } else {
                    p.name
                };
                let field = if p.field == from {
                    to.to_string()
                } else {
                    p.field
                };
                FreeParamObj::ForallFieldAccess(ForallFreeParamFieldAccess::new(name, field))
            }
            FreeParamObj::Def(p) => {
                let name = if p.name == from {
                    to.to_string()
                } else {
                    p.name
                };
                FreeParamObj::Def(DefFreeParamObj::new(name))
            }
            FreeParamObj::Exist(p) => {
                let name = if p.name == from {
                    to.to_string()
                } else {
                    p.name
                };
                FreeParamObj::Exist(ExistFreeParamObj::new(name))
            }
            FreeParamObj::SetBuilder(p) => {
                let name = if p.name == from {
                    to.to_string()
                } else {
                    p.name
                };
                FreeParamObj::SetBuilder(SetBuilderFreeParamObj::new(name))
            }
            FreeParamObj::FnSet(p) => {
                let name = if p.name == from {
                    to.to_string()
                } else {
                    p.name
                };
                FreeParamObj::FnSet(FnSetFreeParamObj::new(name))
            }
            FreeParamObj::StructSelfField(p) => {
                let field = if p.field == from {
                    to.to_string()
                } else {
                    p.field
                };
                FreeParamObj::StructSelfField(StructSelfFieldFreeParamObj::new(field))
            }
            FreeParamObj::Induc(p) => {
                let name = if p.name == from {
                    to.to_string()
                } else {
                    p.name
                };
                FreeParamObj::Induc(ByInducFreeParamObj::new(name))
            }
        }
    }
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

impl ByInducFreeParamObj {
    pub fn new(name: String) -> Self {
        ByInducFreeParamObj { name }
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

impl fmt::Display for ByInducFreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl fmt::Display for FreeParamObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FreeParamObj::Forall(x) => write!(f, "{}", x),
            FreeParamObj::ForallFieldAccess(x) => write!(f, "{}", x),
            FreeParamObj::Def(x) => write!(f, "{}", x),
            FreeParamObj::Exist(x) => write!(f, "{}", x),
            FreeParamObj::SetBuilder(x) => write!(f, "{}", x),
            FreeParamObj::FnSet(x) => write!(f, "{}", x),
            FreeParamObj::StructSelfField(x) => write!(f, "{}", x),
            FreeParamObj::Induc(x) => write!(f, "{}", x),
        }
    }
}

impl From<ForallFreeParamObj> for FreeParamObj {
    fn from(v: ForallFreeParamObj) -> Self {
        FreeParamObj::Forall(v)
    }
}

impl From<ForallFreeParamFieldAccess> for FreeParamObj {
    fn from(v: ForallFreeParamFieldAccess) -> Self {
        FreeParamObj::ForallFieldAccess(v)
    }
}

impl From<DefFreeParamObj> for FreeParamObj {
    fn from(v: DefFreeParamObj) -> Self {
        FreeParamObj::Def(v)
    }
}

impl From<ExistFreeParamObj> for FreeParamObj {
    fn from(v: ExistFreeParamObj) -> Self {
        FreeParamObj::Exist(v)
    }
}

impl From<SetBuilderFreeParamObj> for FreeParamObj {
    fn from(v: SetBuilderFreeParamObj) -> Self {
        FreeParamObj::SetBuilder(v)
    }
}

impl From<FnSetFreeParamObj> for FreeParamObj {
    fn from(v: FnSetFreeParamObj) -> Self {
        FreeParamObj::FnSet(v)
    }
}

impl From<StructSelfFieldFreeParamObj> for FreeParamObj {
    fn from(v: StructSelfFieldFreeParamObj) -> Self {
        FreeParamObj::StructSelfField(v)
    }
}

impl From<ByInducFreeParamObj> for FreeParamObj {
    fn from(v: ByInducFreeParamObj) -> Self {
        FreeParamObj::Induc(v)
    }
}

impl From<FreeParamObj> for Obj {
    fn from(v: FreeParamObj) -> Self {
        Obj::FreeParam(v)
    }
}

impl From<ForallFreeParamObj> for Obj {
    fn from(v: ForallFreeParamObj) -> Self {
        FreeParamObj::from(v).into()
    }
}

impl From<ForallFreeParamFieldAccess> for Obj {
    fn from(v: ForallFreeParamFieldAccess) -> Self {
        FreeParamObj::from(v).into()
    }
}

impl From<DefFreeParamObj> for Obj {
    fn from(v: DefFreeParamObj) -> Self {
        FreeParamObj::from(v).into()
    }
}

impl From<ExistFreeParamObj> for Obj {
    fn from(v: ExistFreeParamObj) -> Self {
        FreeParamObj::from(v).into()
    }
}

impl From<SetBuilderFreeParamObj> for Obj {
    fn from(v: SetBuilderFreeParamObj) -> Self {
        FreeParamObj::from(v).into()
    }
}

impl From<FnSetFreeParamObj> for Obj {
    fn from(v: FnSetFreeParamObj) -> Self {
        FreeParamObj::from(v).into()
    }
}

impl From<StructSelfFieldFreeParamObj> for Obj {
    fn from(v: StructSelfFieldFreeParamObj) -> Self {
        FreeParamObj::from(v).into()
    }
}

impl From<ByInducFreeParamObj> for Obj {
    fn from(v: ByInducFreeParamObj) -> Self {
        FreeParamObj::from(v).into()
    }
}
