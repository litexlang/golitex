#[derive(Clone)]
pub struct VerifyState {
    // Ordinary builtin entry is allowed once; builtin premises disable it.
    // Strategy may still call calculation / known-citation leaves directly.
    pub can_use_builtin_rule: bool,

    // Deep phase budget: definition / known-forall / strategy entry / rewrite.
    // Strategy requirements retain their independent StrategySearch depth.
    pub remaining_deep_search_depth: u8,

    // Deep search phase: prop definition, known forall, and (with
    // can_use_rewrite) rewrite. Also gates the one top-level entry into
    // `verify_by_strategy`. Nested strategy recursion uses StrategySearch,
    // not this flag. A zero remaining_deep_search_depth also blocks deep entry.
    pub can_use_def_and_known_forall_and_known_strategy: bool,

    // Blocks rewrite loops, e.g. `$p(a, b)` via symmetry needs `$p(b, a)`,
    // which must not try symmetry back to `$p(a, b)`.
    pub can_use_rewrite: bool,

    // If every successful WD check were stored, the env would fill with
    // mostly unused records. Only top-level exec_fact (and similar stmt
    // entries) pass true; exploratory search keeps this false.
    pub store_well_defined_fact: bool,

    // Peer comparison is independent of builtin permission. Verifier calls carrying
    // this state may cite stored paths without expanding another class. This
    // is not a global inference policy: binder WD keeps its existing local
    // store/infer entry, whose inferred obligations construct their own state.
    pub equality_class_search: EqualityClassSearchMode,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EqualityClassSearchMode {
    StoredPathsOnly,
    AllowPeerComparison,
}

impl VerifyState {
    pub const TOP_DEEP_SEARCH_DEPTH: u8 = 3;

    // Full top-level truth search (stmt entry / WD entry).
    pub fn top_level() -> Self {
        Self {
            can_use_builtin_rule: true,
            remaining_deep_search_depth: Self::TOP_DEEP_SEARCH_DEPTH,
            can_use_def_and_known_forall_and_known_strategy: true,
            can_use_rewrite: true,
            store_well_defined_fact: true,
            equality_class_search: EqualityClassSearchMode::AllowPeerComparison,
        }
    }

    // Truth-search may read existing WD on the env stack, but must not
    // record new WD as a side effect of trying a proof route.
    pub fn without_well_defined_storage(&self) -> Self {
        let mut search_state = self.clone();
        search_state.store_well_defined_fact = false;
        search_state
    }

    // Builtin premises use known evidence, without another builtin/deep entry.
    pub fn after_builtin_rule(&self) -> Self {
        Self {
            can_use_builtin_rule: false,
            remaining_deep_search_depth: self.remaining_deep_search_depth,
            can_use_def_and_known_forall_and_known_strategy: false,
            can_use_rewrite: false,
            store_well_defined_fact: false,
            equality_class_search: self.equality_class_search,
        }
    }

    // Enter the deep phase; builtin permission and all other flags are inherited.
    pub fn after_deep_search(&self) -> Self {
        let mut next = self.clone();
        next.remaining_deep_search_depth = next.remaining_deep_search_depth.saturating_sub(1);
        next
    }

    // Nested equality / matching peel: no deep search, no rewrite, no WD store.
    pub fn known_only_no_wd(&self) -> Self {
        Self {
            can_use_builtin_rule: false,
            remaining_deep_search_depth: 0,
            can_use_def_and_known_forall_and_known_strategy: false,
            can_use_rewrite: false,
            store_well_defined_fact: false,
            equality_class_search: self.equality_class_search,
        }
    }

    // WD / known cite inside a strategy subtree: no deep search, no rewrite,
    // no WD store. Calculation / known-citation builtin leaves remain callable.
    pub fn strategy_wd() -> Self {
        Self {
            can_use_builtin_rule: false,
            remaining_deep_search_depth: 0,
            can_use_def_and_known_forall_and_known_strategy: false,
            can_use_rewrite: false,
            store_well_defined_fact: false,
            equality_class_search: EqualityClassSearchMode::AllowPeerComparison,
        }
    }

    // Keep the caller's builtin permission; disable deep search, rewrites, WD storage and
    // peer expansion in child verifier calls, including direct WD obligations.
    pub fn for_equality_peer_comparison(&self) -> Self {
        let mut child = self.without_well_defined_storage();
        child.can_use_def_and_known_forall_and_known_strategy = false;
        child.can_use_rewrite = false;
        child.equality_class_search = EqualityClassSearchMode::StoredPathsOnly;
        child
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/execute/builtin_entry_policy/tests.rs"]
mod builtin_entry_policy_tests;

pub struct VerifyState {
    level: VerifyStateLevel
    can_rewrite: bool,
}

pub enum VerifyStateLevel {
    
}