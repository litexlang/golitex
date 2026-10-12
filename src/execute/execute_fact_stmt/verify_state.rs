//! Shared truth-search permissions. Family dispatch preserves these permissions.
//! Rewrite is a final fallback with one opportunity per branch. Ordinary rule
//! premises and rewrite residuals must not create a fresh top-level state.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifyState {
    level: VerifyStateLevel,
    can_rewrite: bool,
    can_infer: bool,
}

// Order denotes the maximum available truth-search stage, not recursion depth.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum VerifyStateLevel {
    // Stored/identity evidence, closed calculation, structural carriers; no search premises.
    Direct = 0,
    KnownSpecialProperty = 1,
    BuiltinRule = 2,
    Strategy = 3,
    DefinitionAndForall = 4,
}

impl VerifyState {
    // Explicit restricted entry, e.g. the deterministic Direct routes.
    // Recursive callers must derive their state from their parent instead.
    pub fn new(level: VerifyStateLevel) -> Self {
        Self {
            level,
            can_rewrite: false,
            can_infer: true,
        }
    }

    // New root proof attempt only; never reset to this inside WD or a premise.
    pub fn top_level() -> Self {
        Self {
            level: VerifyStateLevel::DefinitionAndForall,
            can_rewrite: true,
            can_infer: true,
        }
    }

    // A restricted child can only retain or reduce its parent's ceiling.
    pub fn capped_at(self, ceiling: VerifyStateLevel) -> Self {
        Self {
            level: self.level.min(ceiling),
            can_rewrite: false,
            can_infer: self.can_infer,
        }
    }

    pub fn allows_inference(self) -> bool {
        self.can_infer
    }

    // Derived-fact formation must not reopen inference in its binder scopes.
    pub fn without_inference(self) -> Self {
        Self {
            can_infer: false,
            ..self
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
            can_infer: self.can_infer,
        })
    }

    // For a caller that forbids rewrite while retaining the same truth ceiling.
    pub fn without_rewrite(self) -> Self {
        Self {
            level: self.level,
            can_rewrite: false,
            can_infer: self.can_infer,
        }
    }

    // Final fallback only: consume this branch's rewrite permission before
    // checking replacements or residuals. Independent facts and chain segments
    // may each inherit a permission; this is not a theorem-wide counter.
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
