use crate::prelude::*;

#[derive(Clone, Default)]
pub struct KnownFnInfo {
    pub fn_set: Option<(FnSetBody, LineFile)>,
    /// Exact ordinary fact whose current-slot membership installed `fn_set`.
    /// Kernel-derived callable shapes may have no such fact and use a
    /// structural WD-cache contract instead.
    pub fn_set_membership_fact_id: Option<FactId>,
    /// Defining expression: `have fn … = rhs` or `name = '…{…}` anonymous body.
    pub equal_to: Option<(Obj, LineFile)>,
}

impl KnownFnInfo {
    /// Build from optional pieces; fields can be filled later via `update_*`.
    pub fn merge_fn_set_equal_to(
        fn_set: Option<(FnSetBody, LineFile)>,
        equal_to: Option<(Obj, LineFile)>,
    ) -> Self {
        KnownFnInfo {
            fn_set,
            fn_set_membership_fact_id: None,
            equal_to,
        }
    }

    pub fn update_equal_to(&mut self, equal_to: Obj, line_file: LineFile) {
        self.equal_to = Some((equal_to, line_file));
    }

    pub fn update_fn_set(&mut self, fn_set: FnSetBody, line_file: LineFile) {
        self.fn_set = Some((fn_set, line_file));
        self.fn_set_membership_fact_id = None;
    }
}
