//! Shared truth-search permissions. Family dispatch preserves these permissions.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifyState {
    level: VerifyStateLevel,
    can_rewrite: bool,
}

// Order denotes the maximum available truth-search stage, not recursion depth.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum VerifyStateLevel {
    // Stored/identity evidence, then pure closed calculation; no search premises.
    Direct = 0,
    KnownSpecialProperty = 1,
    BuiltinRule = 2,
    Strategy = 3,
    DefinitionAndForall = 4,
}

impl VerifyState {
    // Explicit restricted entry, e.g. stored facts plus closed calculation.
    // Recursive callers must derive their state from their parent instead.
    pub fn new(level: VerifyStateLevel) -> Self {
        Self {
            level,
            can_rewrite: false,
        }
    }

    // New root proof attempt only; never reset to this inside WD or a premise.
    pub fn top_level() -> Self {
        Self {
            level: VerifyStateLevel::DefinitionAndForall,
            can_rewrite: true,
        }
    }

    // A restricted child can only retain or reduce its parent's ceiling.
    pub fn capped_at(self, ceiling: VerifyStateLevel) -> Self {
        Self {
            level: self.level.min(ceiling),
            can_rewrite: false,
        }
    }

    pub fn level(self) -> VerifyStateLevel {
        self.level
    }

    pub fn allows(self, stage: VerifyStateLevel) -> bool {
        self.level >= stage
    }

    // One central stage-to-premise policy. The stage caller checks this once;
    // its rule implementations receive the returned premise state as-is.
    // None: stage forbidden, or Direct (a leaf that has no search premises).
    pub fn for_premises(self, stage: VerifyStateLevel) -> Option<Self> {
        if !self.allows(stage) {
            return None;
        }
        let level = match stage {
            VerifyStateLevel::Direct => return None,
            VerifyStateLevel::KnownSpecialProperty => VerifyStateLevel::Direct,
            VerifyStateLevel::BuiltinRule => VerifyStateLevel::KnownSpecialProperty,
            VerifyStateLevel::Strategy | VerifyStateLevel::DefinitionAndForall => {
                VerifyStateLevel::BuiltinRule
            }
        };
        Some(Self {
            level,
            can_rewrite: false,
        })
    }

    // For a caller that forbids rewrite while retaining the same truth ceiling.
    pub fn without_rewrite(self) -> Self {
        Self {
            level: self.level,
            can_rewrite: false,
        }
    }

    // Gate and consume the single rewrite opportunity on this branch.
    pub fn after_rewrite(self) -> Option<Self> {
        if self.level != VerifyStateLevel::DefinitionAndForall || !self.can_rewrite {
            return None;
        }
        Some(self.without_rewrite())
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/execute/builtin_entry_policy/tests.rs"]
mod builtin_entry_policy_tests;
