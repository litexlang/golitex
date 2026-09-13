use super::literally_the_same::LiterallyTheSameBuiltinRuleProof;

// Each equality builtin rule gets its own variant and payload.
pub enum EqualitySearchProofByBuiltinRule {
    LiterallyTheSame(LiterallyTheSameBuiltinRuleProof),
    Calculation(EqualitySearchProofByCalculation),
}

// Placeholder until calculation builtin is wired.
pub struct EqualitySearchProofByCalculation {}
