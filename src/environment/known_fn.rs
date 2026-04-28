use crate::prelude::*;

#[derive(Clone)]
pub struct KnownFnInfo {
    pub fn_set: Option<FnSetBody>,
    /// Defining expression: `have fn … = rhs` or `name = '…{…}` anonymous body.
    pub equal_to: Option<Obj>,
    pub restrict_to: Option<FnSetBody>,
}

impl KnownFnInfo {
    pub fn with_fn_set(body: FnSetBody, equal_to: Option<Obj>) -> Self {
        KnownFnInfo {
            fn_set: Some(body),
            equal_to,
            restrict_to: None,
        }
    }
}
