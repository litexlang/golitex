#[derive(Clone)]
pub struct VerifyState {
    // Remaining budget shared by builtin-rule entry and deep entry
    // (strategy / by-def / known-forall / rewrite). Top-level starts at 3;
    // deep search at round zero is blocked, while two nested premise steps
    // remain available for ordinary builtin proofs.
    // Entering either phase requires round > 0 and passes with_one_less_round()
    // (round - 1). Premise-producing arms may after_builtin_rule() again
    // (round - 1, deep/rewrite off). Cite-only still runs at round 0 inside
    // an entered builtin call; strategy cite-only bypasses the search entry.
    pub can_use_builtin_rule_round: u8,

    // Deep search phase: prop definition, known forall, and (with
    // can_use_rewrite) rewrite. Also gates the one top-level entry into
    // `verify_by_strategy`. Nested strategy recursion uses StrategySearch,
    // not this flag. Round == 0 also blocks deep entry.
    pub can_use_def_and_known_forall_and_known_strategy: bool,

    // Blocks rewrite loops, e.g. `$p(a, b)` via symmetry needs `$p(b, a)`,
    // which must not try symmetry back to `$p(a, b)`.
    pub can_use_rewrite: bool,

    // If every successful WD check were stored, the env would fill with
    // mostly unused records. Only top-level exec_fact (and similar stmt
    // entries) pass true; exploratory search keeps this false.
    pub store_well_defined_fact: bool,

    // Peer comparison is independent of builtin fuel. Verifier calls carrying
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
    pub const TOP_BUILTIN_RULE_ROUND: u8 = 3;

    // Full top-level truth search (stmt entry / WD entry).
    pub fn top_level() -> Self {
        Self {
            can_use_builtin_rule_round: Self::TOP_BUILTIN_RULE_ROUND,
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

    // Child of a premise-producing builtin rule: round - 1, known / direct only.
    pub fn after_builtin_rule(&self) -> Self {
        Self {
            can_use_builtin_rule_round: self.can_use_builtin_rule_round.saturating_sub(1),
            can_use_def_and_known_forall_and_known_strategy: false,
            can_use_rewrite: false,
            store_well_defined_fact: false,
            equality_class_search: self.equality_class_search,
        }
    }

    // Enter builtin-rule or deep phase: round - 1, other flags unchanged.
    pub fn with_one_less_round(&self) -> Self {
        let mut next = self.clone();
        next.can_use_builtin_rule_round = next.can_use_builtin_rule_round.saturating_sub(1);
        next
    }

    // Nested equality / matching peel: no deep search, no rewrite, no WD store.
    pub fn known_only_no_wd(&self) -> Self {
        Self {
            can_use_builtin_rule_round: 0,
            can_use_def_and_known_forall_and_known_strategy: false,
            can_use_rewrite: false,
            store_well_defined_fact: false,
            equality_class_search: self.equality_class_search,
        }
    }

    // WD / known cite inside a strategy subtree: no deep search, no rewrite,
    // no WD store. Cite-only builtin arms still run at round 0.
    pub fn strategy_wd() -> Self {
        Self {
            can_use_builtin_rule_round: 0,
            can_use_def_and_known_forall_and_known_strategy: false,
            can_use_rewrite: false,
            store_well_defined_fact: false,
            equality_class_search: EqualityClassSearchMode::AllowPeerComparison,
        }
    }

    // Keep the caller's fuel; disable deep search, rewrites, WD storage and
    // peer expansion in child verifier calls, including direct WD obligations.
    pub fn for_equality_peer_comparison(&self) -> Self {
        let mut child = self.without_well_defined_storage();
        child.can_use_def_and_known_forall_and_known_strategy = false;
        child.can_use_rewrite = false;
        child.equality_class_search = EqualityClassSearchMode::StoredPathsOnly;
        child
    }
}
