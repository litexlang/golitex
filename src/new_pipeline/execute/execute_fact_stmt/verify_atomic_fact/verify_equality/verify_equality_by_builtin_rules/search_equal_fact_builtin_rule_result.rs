use super::by_equal_ir::ByEqualIrBuiltinRuleProof;

// Each equality builtin rule gets its own variant and payload.
pub enum EqualitySearchProofByBuiltinRule {
    ByEqualIr(ByEqualIrBuiltinRuleProof),
    Calculation(EqualitySearchProofByCalculation),
}

// Placeholder until calculation builtin is wired.
pub struct EqualitySearchProofByCalculation {}
