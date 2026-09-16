//! Parameter list and AtomicName IR + display_string.

use super::types::ParamIR;
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::param::{
    FiniteSet, NonemptySet, ParamType, Set, SetBoundParameterGroup, SetBoundParameterList,
    TypedParameterGroup, TypedParameterList,
};
use crate::new_pipeline::parse::keywords::{COMMA, FINITE_SET, NONEMPTY_SET, SET};

impl AtomicName {
    pub fn ir(&self) -> ParamIR {
        ParamIR(self.display_string())
    }
}

impl TypedParameterList {
    pub fn ir(&self) -> ParamIR {
        ParamIR(
            self.groups
                .iter()
                .map(|g| g.ir().0)
                .collect::<Vec<_>>()
                .join(&format!("{} ", COMMA)),
        )
    }
    pub fn display_string(&self) -> String {
        self.groups
            .iter()
            .map(|g| g.display_string())
            .collect::<Vec<_>>()
            .join(&format!("{} ", COMMA))
    }
}

impl SetBoundParameterList {
    pub fn ir(&self) -> ParamIR {
        ParamIR(
            self.groups
                .iter()
                .map(|g| g.ir().0)
                .collect::<Vec<_>>()
                .join(&format!("{} ", COMMA)),
        )
    }
    pub fn display_string(&self) -> String {
        self.groups
            .iter()
            .map(|g| g.display_string())
            .collect::<Vec<_>>()
            .join(&format!("{} ", COMMA))
    }
}

impl TypedParameterGroup {
    pub fn ir(&self) -> ParamIR {
        let params = self
            .params
            .iter()
            .map(|p| p.ir_string())
            .collect::<Vec<_>>()
            .join(", ");
        ParamIR(format!("{} {}", params, self.param_type.ir().0))
    }
    pub fn display_string(&self) -> String {
        let params = self
            .params
            .iter()
            .map(|p| p.name.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        format!("{} {}", params, self.param_type.display_string())
    }
}

impl SetBoundParameterGroup {
    pub fn ir(&self) -> ParamIR {
        let params = self
            .params
            .iter()
            .map(|p| p.ir_string())
            .collect::<Vec<_>>()
            .join(", ");
        ParamIR(format!("{} {}", params, self.param_type.as_ref().ir().0))
    }
    pub fn display_string(&self) -> String {
        let params = self
            .params
            .iter()
            .map(|p| p.name.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        format!("{} {}", params, self.param_type.display_string())
    }
}

impl ParamType {
    pub fn ir(&self) -> ParamIR {
        match self {
            ParamType::Set(set) => set.ir(),
            ParamType::NonemptySet(nonempty_set) => nonempty_set.ir(),
            ParamType::FiniteSet(finite_set) => finite_set.ir(),
            ParamType::Obj(obj) => ParamIR(format!("{}", obj.ir().0)),
        }
    }
    pub fn display_string(&self) -> String {
        match self {
            ParamType::Set(set) => set.display_string(),
            ParamType::NonemptySet(nonempty_set) => nonempty_set.display_string(),
            ParamType::FiniteSet(finite_set) => finite_set.display_string(),
            ParamType::Obj(obj) => obj.display_string(),
        }
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
