#[derive(Clone)]
pub struct VerifyState {
    // Forall lookup is one layer only. Nested forall→forall search grows
    // exponentially, so nested proof steps turn this off.
    pub can_use_def_and_known_forall_and_known_strategy: bool,

    // Blocks rewrite loops, e.g. `$p(a, b)` via symmetry needs `$p(b, a)`,
    // which must not try symmetry back to `$p(a, b)`.
    pub can_use_rewrite: bool,

    // If every successful WD check were stored, the env would fill with
    // mostly unused records. Only top-level exec_fact (and similar stmt
    // entries) pass true; exploratory search keeps this false.
    pub store_well_defined_fact: bool,
}

impl VerifyState {
    // Truth-search may read existing WD on the env stack, but must not
    // record new WD as a side effect of trying a proof route.
    pub fn without_well_defined_storage(&self) -> Self {
        let mut search_state = self.clone();
        search_state.store_well_defined_fact = false;
        search_state
    }
}
