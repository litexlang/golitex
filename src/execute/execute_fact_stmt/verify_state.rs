#[derive(Clone)]
pub struct VerifyState {
    // One premise-producing builtin-rule step. After a builtin rule fires,
    // nested truth-search inherits false and may only use known / direct paths.
    pub can_use_builtin_rule: bool,

    // Deep search phase: prop definition, known forall, known/user strategy,
    // builtin strategy, and (with can_use_rewrite) rewrite. Nested steps that
    // must stay "known-only" turn this off together with can_use_builtin_rule.
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
    // Full top-level truth search (stmt entry / WD entry).
    pub fn top_level() -> Self {
        Self {
            can_use_builtin_rule: true,
            can_use_def_and_known_forall_and_known_strategy: true,
            can_use_rewrite: true,
            store_well_defined_fact: true,
        }
    }

    // Truth-search may read existing WD on the env stack, but must not
    // record new WD as a side effect of trying a proof route.
    pub fn without_well_defined_storage(&self) -> Self {
        let mut search_state = self.clone();
        search_state.store_well_defined_fact = false;
        search_state
    }

    // Child of a premise-producing builtin rule: known / direct only.
    pub fn after_builtin_rule(&self) -> Self {
        Self {
            can_use_builtin_rule: false,
            can_use_def_and_known_forall_and_known_strategy: false,
            can_use_rewrite: false,
            store_well_defined_fact: false,
        }
    }

    // Nested equality / matching peel: no deep search, no rewrite, no WD store.
    pub fn known_only_no_wd(&self) -> Self {
        Self {
            can_use_builtin_rule: false,
            can_use_def_and_known_forall_and_known_strategy: false,
            can_use_rewrite: false,
            store_well_defined_fact: false,
        }
    }

    // Builtin-strategy children: one nested builtin layer, no nested strategy/def/forall/rewrite.
    pub fn after_strategy(&self) -> Self {
        Self {
            can_use_builtin_rule: true,
            can_use_def_and_known_forall_and_known_strategy: false,
            can_use_rewrite: false,
            store_well_defined_fact: false,
        }
    }
}
