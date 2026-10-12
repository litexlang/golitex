use crate::prelude::*;

pub struct AddZeroLeftFromEqualitiesBuiltinRuleProof {
    pub remaining_equal: VerifyFactResult,
    pub zero_equal: VerifyFactResult,
    pub reversed: bool,
}

impl AddZeroLeftFromEqualitiesBuiltinRuleProof {
    pub fn new(
        remaining_equal: VerifyFactResult,
        zero_equal: VerifyFactResult,
        reversed: bool,
    ) -> Self {
        Self {
            remaining_equal,
            zero_equal,
            reversed,
        }
    }
}

pub struct AddZeroRightFromEqualitiesBuiltinRuleProof {
    pub remaining_equal: VerifyFactResult,
    pub zero_equal: VerifyFactResult,
    pub reversed: bool,
}

impl AddZeroRightFromEqualitiesBuiltinRuleProof {
    pub fn new(
        remaining_equal: VerifyFactResult,
        zero_equal: VerifyFactResult,
        reversed: bool,
    ) -> Self {
        Self {
            remaining_equal,
            zero_equal,
            reversed,
        }
    }
}
