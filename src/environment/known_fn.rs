use crate::prelude::*;

#[derive(Clone, Default)]
pub struct KnownFnInfo {
    pub fn_set: Option<(FnSetBody, LineFile)>,
    /// Defining expression: `have fn … = rhs` or `name = '…{…}` anonymous body.
    pub equal_to: Option<(Obj, LineFile)>,
    /// Narrower `$restrict_fn_in` target signature; newer facts replace the previous value.
    pub restrict_to: Option<(FnSetBody, LineFile)>,
}

impl KnownFnInfo {
    /// Build from optional pieces; fields can be filled later via `update_*`.
    pub fn merge_fn_set_equal_to(
        fn_set: Option<(FnSetBody, LineFile)>,
        equal_to: Option<(Obj, LineFile)>,
    ) -> Self {
        KnownFnInfo {
            fn_set,
            equal_to,
            restrict_to: None,
        }
    }

    pub fn update_restrict_to(&mut self, restrict_to: FnSetBody, line_file: LineFile) {
        self.restrict_to = Some((restrict_to, line_file));
    }

    pub fn update_equal_to(&mut self, equal_to: Obj, line_file: LineFile) {
        self.equal_to = Some((equal_to, line_file));
    }

    pub fn update_fn_set(&mut self, fn_set: FnSetBody, line_file: LineFile) {
        self.fn_set = Some((fn_set, line_file));
    }
}
