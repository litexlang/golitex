//! Framework AST data shapes for new_pipeline.
//! Field taxonomy follows the legacy language; methods are added later.
//! Identity: parameter lists store BoundName (name + IdentifierId).

use super::names::BoundName;
use super::obj::Obj;

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
