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

    // How many nested builtin-strategy layers remain below this state.
    // Top-level starts at BUILTIN_STRATEGY_DEPTH_LIMIT; each after_strategy
    // decrements. When the next depth would be 0, deep search turns off so
    // strategy children can still nest carrier closures a bounded number of
    // times (e.g. `(a - (a % b)) $in Z`) without unbounded recursion.
    pub builtin_strategy_depth_remaining: u8,
}

impl VerifyState {
    // Max nested strategy layers under a top-level search.
    pub const BUILTIN_STRATEGY_DEPTH_LIMIT: u8 = 4;

    // Full top-level truth search (stmt entry / WD entry).
    pub fn top_level() -> Self {
        Self {
            can_use_builtin_rule: true,
            can_use_def_and_known_forall_and_known_strategy: true,
            can_use_rewrite: true,
            store_well_defined_fact: true,
            builtin_strategy_depth_remaining: Self::BUILTIN_STRATEGY_DEPTH_LIMIT,
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
            builtin_strategy_depth_remaining: 0,
        }
    }

    // Nested equality / matching peel: no deep search, no rewrite, no WD store.
    pub fn known_only_no_wd(&self) -> Self {
        Self {
            can_use_builtin_rule: false,
            can_use_def_and_known_forall_and_known_strategy: false,
            can_use_rewrite: false,
            store_well_defined_fact: false,
            builtin_strategy_depth_remaining: 0,
        }
    }

    // Builtin-strategy children: keep builtin rules; allow nested strategy /
    // def / forall while depth remains; rewrite stays off.
    pub fn after_strategy(&self) -> Self {
        let next_depth = self.builtin_strategy_depth_remaining.saturating_sub(1);
        Self {
            can_use_builtin_rule: true,
            can_use_def_and_known_forall_and_known_strategy: self
                .can_use_def_and_known_forall_and_known_strategy
                && next_depth > 0,
            can_use_rewrite: false,
            store_well_defined_fact: false,
            builtin_strategy_depth_remaining: next_depth,
        }
    }
}
