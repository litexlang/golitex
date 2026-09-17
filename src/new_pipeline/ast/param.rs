//! Framework AST data shapes for new_pipeline.
//! Field taxonomy follows the legacy language; methods are added later.
//! Identity: parameter lists store BoundName (name + IdentifierId).

use super::names::BoundName;
use super::obj::Obj;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParamType {
    Set(Set),
    NonemptySet(NonemptySet),
    FiniteSet(FiniteSet),
    Obj(Obj),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedParameterList {
    pub groups: Vec<TypedParameterGroup>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SetBoundParameterList {
    pub groups: Vec<SetBoundParameterGroup>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SetBoundParameterGroup {
    pub params: Vec<BoundName>,
    pub param_type: Box<Obj>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedParameterGroup {
    pub params: Vec<BoundName>,
    pub param_type: ParamType,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Set {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NonemptySet {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteSet {}

impl TypedParameterList {
    // Flatten `groups -> params` into declaration order.
    // Example: `x, y R, z N` -> [id(x), id(y), id(z)].
    pub fn ordered_param_ids(&self) -> Vec<IdentifierId> {
        let mut ids = Vec::new();
        for group in &self.groups {
            for param in &group.params {
                ids.push(param.id);
            }
        }
        ids
    }
}
