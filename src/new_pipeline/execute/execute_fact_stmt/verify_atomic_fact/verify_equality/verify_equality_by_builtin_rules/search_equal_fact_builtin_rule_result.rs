use super::by_equal_ir::ByEqualIrBuiltinRuleProof;

// Each equality builtin rule gets its own variant and payload.
pub enum EqualitySearchProofByBuiltinRule {
    ByEqualIr(ByEqualIrBuiltinRuleProof),
    Calculation(EqualitySearchProofByCalculation),
}

// Closed decimal keeps both normal forms; symbolic rational keeps no Obj nf
// (legacy compares monomial vectors, not reconstructed expressions).
// Lean can still choose norm_num vs ring_nf from the EqualFact + variant.
pub enum EqualitySearchProofByCalculation {
    ClosedDecimal {
        left_normal: String,
        right_normal: String,
    },
    Rational {},
}