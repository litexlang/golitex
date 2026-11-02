//! Interfaces actually consumed while computing a checked call's return set.
use crate::prelude::*;

/// This records interface computation, not a separate argument/WD proof.
/// Each layer is captured before its arguments instantiate the return set.
/// The caller still owns the successful application-domain check.
pub struct AppliedFnSetReturnSignature {
    pub application: FnObj,
    pub layers: Vec<FnSet>,
    pub return_set: Obj,
}
