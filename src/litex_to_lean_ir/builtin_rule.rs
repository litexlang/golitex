use crate::prelude::*;

/// Builtin arithmetic certificates for which the Lean backend has a complete
/// replay adapter. Unsupported verifier rules never enter the success IR.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LitexToLeanArithmeticBuiltinRuleIr {
    AddNonnegative,
    AddPositiveLeftStrict,
    AddPositiveRightStrict,
}

/// A verifier-selected builtin rule with a concrete Lean replay route.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LitexToLeanBuiltinRuleIr {
    Arithmetic(LitexToLeanArithmeticBuiltinRuleIr),
    RealAddMembershipClosure,
    NotEqualSymmetry,
}

impl LitexToLeanBuiltinRuleIr {
    pub(crate) fn from_legacy_evidence(evidence: &BuiltinRuleEvidence) -> Option<Self> {
        match evidence {
            BuiltinRuleEvidence::Arithmetic(ArithmeticBuiltinRule::AddNonnegative) => Some(
                Self::Arithmetic(LitexToLeanArithmeticBuiltinRuleIr::AddNonnegative),
            ),
            BuiltinRuleEvidence::Arithmetic(ArithmeticBuiltinRule::AddPositiveLeftStrict) => Some(
                Self::Arithmetic(LitexToLeanArithmeticBuiltinRuleIr::AddPositiveLeftStrict),
            ),
            BuiltinRuleEvidence::Arithmetic(ArithmeticBuiltinRule::AddPositiveRightStrict) => Some(
                Self::Arithmetic(LitexToLeanArithmeticBuiltinRuleIr::AddPositiveRightStrict),
            ),
            BuiltinRuleEvidence::RealArithmeticMembershipClosure(
                RealArithmeticMembershipClosureBuiltinRule::Add,
            ) => Some(Self::RealAddMembershipClosure),
            BuiltinRuleEvidence::NotEqualSymmetry => Some(Self::NotEqualSymmetry),
            _ => None,
        }
    }
}
