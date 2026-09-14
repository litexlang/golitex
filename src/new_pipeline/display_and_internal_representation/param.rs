//! Parameter list and AtomicName internal representation + display_string.

use super::types::ParamInternalRepresentation;
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::param::{
    FiniteSet, NonemptySet, ParamType, Set, SetBoundParameterGroup, SetBoundParameterList,
    TypedParameterGroup, TypedParameterList,
};
use crate::new_pipeline::parse::keywords::{COMMA, FINITE_SET, MOD_SIGN, NONEMPTY_SET, SET};

impl AtomicName {
    pub fn internal_representation(&self) -> ParamInternalRepresentation {
        match self {
            AtomicName::WithoutMod(name) => ParamInternalRepresentation(name.clone()),
            AtomicName::WithMod(mod_name, name) => ParamInternalRepresentation(format!(
                "{}{}{}",
                mod_name, MOD_SIGN, name
            )),
        }
    }
    pub fn display_string(&self) -> String {
        self.internal_representation().display_string()
    }
}

impl TypedParameterList {
    pub fn internal_representation(&self) -> ParamInternalRepresentation {
        ParamInternalRepresentation(
            self.groups
                .iter()
                .map(|g| g.internal_representation())
                .collect::<Vec<_>>()
                .join(&format!("{} ", COMMA)),
        )
    }
    pub fn display_string(&self) -> String {
        self.internal_representation().display_string()
    }
}

impl SetBoundParameterList {
    pub fn internal_representation(&self) -> ParamInternalRepresentation {
        ParamInternalRepresentation(
            self.groups
                .iter()
                .map(|g| g.internal_representation())
                .collect::<Vec<_>>()
                .join(&format!("{} ", COMMA)),
        )
    }
    pub fn display_string(&self) -> String {
        self.internal_representation().display_string()
    }
}

impl TypedParameterGroup {
    pub fn internal_representation(&self) -> ParamInternalRepresentation {
        let params = self
            .params
            .iter()
            .map(|p| p.internal_representation())
            .collect::<Vec<_>>()
            .join(", ");
        ParamInternalRepresentation(format!(
            "{} {}",
            params,
            self.param_type.internal_representation()
        ))
    }
    pub fn display_string(&self) -> String {
        self.internal_representation().display_string()
    }
}

impl SetBoundParameterGroup {
    pub fn internal_representation(&self) -> ParamInternalRepresentation {
        let params = self
            .params
            .iter()
            .map(|p| p.internal_representation())
            .collect::<Vec<_>>()
            .join(", ");
        ParamInternalRepresentation(format!(
            "{} {}",
            params,
            self.param_type.as_ref().internal_representation()
        ))
    }
    pub fn display_string(&self) -> String {
        self.internal_representation().display_string()
    }
}

impl ParamType {
    pub fn internal_representation(&self) -> ParamInternalRepresentation {
        match self {
            ParamType::Set(set) => set.internal_representation(),
            ParamType::NonemptySet(nonempty_set) => nonempty_set.internal_representation(),
            ParamType::FiniteSet(finite_set) => finite_set.internal_representation(),
            ParamType::Obj(obj) => ParamInternalRepresentation(format!(
                "{}",
                obj.internal_representation()
            )),
        }
    }
    pub fn display_string(&self) -> String {
        self.internal_representation().display_string()
    }
}

impl Set {
    pub fn internal_representation(&self) -> ParamInternalRepresentation {
        ParamInternalRepresentation(SET.to_string())
    }
    pub fn display_string(&self) -> String {
        self.internal_representation().display_string()
    }
}

impl NonemptySet {
    pub fn internal_representation(&self) -> ParamInternalRepresentation {
        ParamInternalRepresentation(NONEMPTY_SET.to_string())
    }
    pub fn display_string(&self) -> String {
        self.internal_representation().display_string()
    }
}

impl FiniteSet {
    pub fn internal_representation(&self) -> ParamInternalRepresentation {
        ParamInternalRepresentation(FINITE_SET.to_string())
    }
    pub fn display_string(&self) -> String {
        self.internal_representation().display_string()
    }
}
