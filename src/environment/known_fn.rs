use crate::prelude::*;

#[derive(Clone, Default)]
pub struct KnownFnInfo {
    pub fn_set: Option<FnSetBody>,
    /// Defining expression: `have fn … = rhs` or `name = '…{…}` anonymous body.
    pub equal_to: Option<Obj>,
    /// Narrower `$restrict_fn_in` target signature; newer facts replace the previous value.
    pub restrict_to: Option<FnSetBody>,
}

impl KnownFnInfo {
    /// Build from optional pieces; fields can be filled later via `update_*`.
    pub fn with_fn_set(fn_set: Option<FnSetBody>, equal_to: Option<Obj>) -> Self {
        KnownFnInfo {
            fn_set,
            equal_to,
            restrict_to: None,
        }
    }

    pub fn update_restrict_to(&mut self, restrict_to: FnSetBody) {
        self.restrict_to = Some(restrict_to);
    }

    pub fn update_equal_to(&mut self, equal_to: Obj) {
        self.equal_to = Some(equal_to);
    }

    pub fn update_fn_set(&mut self, fn_set: FnSetBody) {
        self.fn_set = Some(fn_set);
    }
}
