//! Parameter list and AtomicName IR + display_string.

use super::types::ParamIR;
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::param::{
    FiniteSet, NonemptySet, ParamType, Set, SetBoundParameterGroup, SetBoundParameterList,
    TypedParameterGroup, TypedParameterList,
};
use crate::new_pipeline::parse::keywords::{COMMA, FINITE_SET, MOD_SIGN, NONEMPTY_SET, SET};

impl AtomicName {
    pub fn ir(&self) -> ParamIR {
        match self {
            AtomicName::WithoutMod(name) => ParamIR(name.clone()),
            AtomicName::WithMod(mod_name, name) => ParamIR(format!(
                "{}{}{}",
                mod_name, MOD_SIGN, name
            )),
        }
    }
    pub fn display_string(&self) -> String {
        self.ir().display_string()
    }
}

impl TypedParameterList {
    pub fn ir(&self) -> ParamIR {
        ParamIR(
            self.groups
                .iter()
                .map(|g| g.ir())
                .collect::<Vec<_>>()
                .join(&format!("{} ", COMMA)),
        )
    }
    pub fn display_string(&self) -> String {
        self.ir().display_string()
    }
}

impl SetBoundParameterList {
    pub fn ir(&self) -> ParamIR {
        ParamIR(
            self.groups
                .iter()
                .map(|g| g.ir())
                .collect::<Vec<_>>()
                .join(&format!("{} ", COMMA)),
        )
    }
    pub fn display_string(&self) -> String {
        self.ir().display_string()
    }
}

impl TypedParameterGroup {
    pub fn ir(&self) -> ParamIR {
        let params = self
            .params
            .iter()
            .map(|p| p.ir())
            .collect::<Vec<_>>()
            .join(", ");
        ParamIR(format!(
            "{} {}",
            params,
            self.param_type.ir()
        ))
    }
    pub fn display_string(&self) -> String {
        self.ir().display_string()
    }
}

impl SetBoundParameterGroup {
    pub fn ir(&self) -> ParamIR {
        let params = self
            .params
            .iter()
            .map(|p| p.ir())
            .collect::<Vec<_>>()
            .join(", ");
        ParamIR(format!(
            "{} {}",
            params,
            self.param_type.as_ref().ir()
        ))
    }
    pub fn display_string(&self) -> String {
        self.ir().display_string()
    }
}

impl ParamType {
    pub fn ir(&self) -> ParamIR {
        match self {
            ParamType::Set(set) => set.ir(),
            ParamType::NonemptySet(nonempty_set) => nonempty_set.ir(),
            ParamType::FiniteSet(finite_set) => finite_set.ir(),
            ParamType::Obj(obj) => ParamIR(format!(
                "{}",
                obj.ir()
            )),
        }
    }
    pub fn display_string(&self) -> String {
        self.ir().display_string()
    }
}

impl Set {
    pub fn ir(&self) -> ParamIR {
        ParamIR(SET.to_string())
    }
    pub fn display_string(&self) -> String {
        self.ir().display_string()
    }
}

impl NonemptySet {
    pub fn ir(&self) -> ParamIR {
        ParamIR(NONEMPTY_SET.to_string())
    }
    pub fn display_string(&self) -> String {
        self.ir().display_string()
    }
}

impl FiniteSet {
    pub fn ir(&self) -> ParamIR {
        ParamIR(FINITE_SET.to_string())
    }
    pub fn display_string(&self) -> String {
        self.ir().display_string()
    }
}
