//! Parameter list and AtomicName internal representation + display_string.

use super::helper::strip_identifier_id_tags;
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::param::{
    FiniteSet, NonemptySet, ParamType, Set, SetBoundParameterGroup, SetBoundParameterList,
    TypedParameterGroup, TypedParameterList,
};
use crate::new_pipeline::parse::keywords::{COMMA, FINITE_SET, MOD_SIGN, NONEMPTY_SET, SET};

impl AtomicName {
    pub fn internal_representation(&self) -> String {
        match self {
            AtomicName::WithoutMod(name) => name.clone(),
            AtomicName::WithMod(mod_name, name) => {
                format!("{}{}{}", mod_name, MOD_SIGN, name)
            }
        }
    }
    pub fn display_string(&self) -> String {
        strip_identifier_id_tags(&self.internal_representation())
    }
}

impl TypedParameterList {
    pub fn internal_representation(&self) -> String {
        self.groups
            .iter()
            .map(|g| g.internal_representation())
            .collect::<Vec<_>>()
            .join(&format!("{} ", COMMA))
    }
    pub fn display_string(&self) -> String {
        strip_identifier_id_tags(&self.internal_representation())
    }
}

impl SetBoundParameterList {
    pub fn internal_representation(&self) -> String {
        self.groups
            .iter()
            .map(|g| g.internal_representation())
            .collect::<Vec<_>>()
            .join(&format!("{} ", COMMA))
    }
    pub fn display_string(&self) -> String {
        strip_identifier_id_tags(&self.internal_representation())
    }
}

impl TypedParameterGroup {
    pub fn internal_representation(&self) -> String {
        let params = self
            .params
            .iter()
            .map(|p| p.internal_representation())
            .collect::<Vec<_>>()
            .join(", ");
        format!("{} {}", params, self.param_type.internal_representation())
    }
    pub fn display_string(&self) -> String {
        strip_identifier_id_tags(&self.internal_representation())
    }
}

impl SetBoundParameterGroup {
    pub fn internal_representation(&self) -> String {
        let params = self
            .params
            .iter()
            .map(|p| p.internal_representation())
            .collect::<Vec<_>>()
            .join(", ");
        format!(
            "{} {}",
            params,
            self.param_type.as_ref().internal_representation()
        )
    }
    pub fn display_string(&self) -> String {
        strip_identifier_id_tags(&self.internal_representation())
    }
}

impl ParamType {
    pub fn internal_representation(&self) -> String {
        match self {
            ParamType::Set(set) => set.internal_representation(),
            ParamType::NonemptySet(nonempty_set) => nonempty_set.internal_representation(),
            ParamType::FiniteSet(finite_set) => finite_set.internal_representation(),
            ParamType::Obj(obj) => obj.internal_representation(),
        }
    }
    pub fn display_string(&self) -> String {
        strip_identifier_id_tags(&self.internal_representation())
    }
}

impl Set {
    pub fn internal_representation(&self) -> String {
        SET.to_string()
    }
    pub fn display_string(&self) -> String {
        strip_identifier_id_tags(&self.internal_representation())
    }
}

impl NonemptySet {
    pub fn internal_representation(&self) -> String {
        NONEMPTY_SET.to_string()
    }
    pub fn display_string(&self) -> String {
        strip_identifier_id_tags(&self.internal_representation())
    }
}

impl FiniteSet {
    pub fn internal_representation(&self) -> String {
        FINITE_SET.to_string()
    }
    pub fn display_string(&self) -> String {
        strip_identifier_id_tags(&self.internal_representation())
    }
}
