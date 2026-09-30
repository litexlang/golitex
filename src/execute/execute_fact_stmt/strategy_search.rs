//! Search context used only inside the strategy subtree.
//!
//! Once `verify_by_strategy` is entered, nested requirement proofs use
//! StrategySearch instead of VerifyState deep/strategy flags. Depth starts
//! at DEPTH_LIMIT and decrements each strategy layer; at 0 only known and
//! cite-only builtin are allowed.

#[derive(Clone, Copy, Debug)]
pub struct StrategySearch {
    // Remaining strategy layers including the current try.
    // Top entry uses DEPTH_LIMIT; each requirement nest decrements by 1.
    // At 0, only known search is allowed.
    pub depth: u8
}

impl StrategySearch {
    pub const DEPTH_LIMIT: u8 = 16;

    pub fn top() -> Self {
        Self {
            depth: Self::DEPTH_LIMIT
        }
    }

    // Child context after one strategy layer is consumed.
    pub fn after_layer(self) -> Self {
        Self {
            depth: self.depth.saturating_sub(1)
        }
    }

    pub fn can_use_strategy(self) -> bool {
        self.depth > 0
    }
}
