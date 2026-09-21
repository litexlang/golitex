//! Framework AST data shapes for new_pipeline.
//! Field taxonomy follows the legacy language; methods are added later.
//! Identity: parameter lists store BoundName (name + IdentifierId).

use super::names::BoundName;
use super::obj::Obj;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;

// Binder shape for have / forall / template / prop / struct, etc.
//
// `Set` / `NonemptySet` / `FiniteSet` are binder *kinds* (`A set` ⇒ `$is_set(A)`),
// not a universal collection of all sets. `Obj(S)` is element binding (`x S` ⇒ `x $in S`).
// Function spaces and set builders must use SetBoundParameterList (Obj domains only);
// for definitions parameterized by an arbitrary set, use `template<A set>`, not `fn(A set)`.
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

// Set-forming / function-space parameters: always element-of-a-set, never a binder kind.
//
// Unlike TypedParameterList (which may use ParamType::Set / NonemptySet / FiniteSet),
// these groups fix the domain to an ordinary Obj `S`. Syntax `x S` means introduce `x`
// with fact `x $in S`; `S` may be N, R, a user set, power_set(...), etc.
//
// This is the kernel surface for bounded quantification used by fn / anonymous fn
// (and the same Obj-domain idea as SetBuilder `{x S: ...}`):
// - no unrestricted comprehension over "all objects"
// - no `fn(A set)` treating the binder kind `set` as a universal collection of sets
// - Object remains a meta-level carrier, not an internal set writable on `$in`
// Together with "every WD object is set-coded", this keeps pure-set coding without
// Russell-style "the set of all sets / all objects satisfying P".
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SetBoundParameterList {
    pub groups: Vec<SetBoundParameterGroup>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SetBoundParameterGroup {
    pub params: Vec<BoundName>,
    // Always an object-domain `S` (element binding), not ParamType::Set / etc.
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
