//! Function contracts and well-defined object cache entries.

use crate::prelude::*;

/// The callable contract selected while checking a function application.
/// Stored membership facts are the canonical contract identity. A structural
/// fallback is retained for kernel-owned callables that have no ordinary
/// membership fact, such as an anonymous function literal.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum WellDefinedFunctionContract {
    StoredMembershipFact(FactId),
    Structural(ObjString),
}

/// Cache identity of an object under the exact context-sensitive function
/// contracts selected by the verifier.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct WellDefinedCacheKey {
    pub object_key: ObjString,
    pub function_contracts: Vec<WellDefinedFunctionContract>,
}

impl WellDefinedCacheKey {
    pub fn new(
        object_key: ObjString,
        function_contracts: Vec<WellDefinedFunctionContract>,
    ) -> Self {
        Self {
            object_key,
            function_contracts,
        }
    }

    pub fn without_function_contract(object_key: ObjString) -> Self {
        Self::new(object_key, Vec::new())
    }
}

/// Ordinary verification may cache truth without constructing compiler
/// evidence. To-Lean may reuse an entry only when `obj_id` is present.
#[derive(Clone, Debug)]
pub struct CachedWellDefinedObj {
    pub obj_id: Option<WellDefinedObjId>,
}

impl CachedWellDefinedObj {
    pub fn ordinary() -> Self {
        Self { obj_id: None }
    }

    pub fn with_obj(obj_id: WellDefinedObjId) -> Self {
        Self {
            obj_id: Some(obj_id),
        }
    }
}
