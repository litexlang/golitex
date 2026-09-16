#[derive(Clone)]
pub struct VerifyState {
    pub can_use_forall_fact: bool,
    pub can_use_rewrite: bool,
    pub store_well_defined_fact: bool,
}

impl VerifyState {
    /// Derive the read-only state used while searching for a truth proof.
    ///
    /// Truth search may reuse WD records that are already visible in the
    /// current execution-environment stack, but it must not add new records
    /// as a side effect of trying a proof route.
    pub fn without_well_defined_storage(&self) -> Self {
        let mut search_state = self.clone();
        search_state.store_well_defined_fact = false;
        search_state
    }
}
