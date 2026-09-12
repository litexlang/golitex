//! Framework AST data shapes for new_pipeline.
//! Field taxonomy follows the legacy language; methods are added later.
//! Identity: String names, FactId, SourceSpan — no SymbolId / AtomId.

use super::obj::Obj;

// from statement/definitions/parameters.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParamType {
    Set(Set),
    NonemptySet(NonemptySet),
    FiniteSet(FiniteSet),
    Obj(Obj),
}

// from statement/definitions/parameters.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedParameterList {
    pub groups: Vec<TypedParameterGroup>,
}

// from statement/definitions/parameters.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SetBoundParameterList {
    pub groups: Vec<SetBoundParameterGroup>,
}

// from statement/definitions/parameters.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SetBoundParameterGroup {    pub params: Vec<String>,
    pub param_type: Box<Obj>,
}

// from statement/definitions/parameters.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedParameterGroup {    pub params: Vec<String>,
    pub param_type: ParamType,
}

// from statement/definitions/parameters.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Set {}

// from statement/definitions/parameters.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NonemptySet {}

// from statement/definitions/parameters.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteSet {}

