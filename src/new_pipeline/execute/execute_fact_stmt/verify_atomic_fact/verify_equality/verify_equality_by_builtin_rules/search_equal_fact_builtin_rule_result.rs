use super::by_anonymous_fn_alpha_equal::ByAnonymousFnAlphaEqualBuiltinRuleProof;
use super::by_equal_ir::ByEqualIrBuiltinRuleProof;
use super::by_equal_to_obj_with_free_params_lookup::ByEqualToObjWithFreeParamsLookupBuiltinRuleProof;
use super::by_fn_set_alpha_equal::ByFnSetAlphaEqualBuiltinRuleProof;
use super::by_inverse_trig::{
    ArccosCosRightInverseBuiltinRuleProof, ArccosExactNegOneBuiltinRuleProof,
    ArccosExactOneBuiltinRuleProof, ArccosExactZeroBuiltinRuleProof,
    ArccotCotRightInverseBuiltinRuleProof, ArccotExactZeroBuiltinRuleProof,
    ArcsinExactNegOneBuiltinRuleProof, ArcsinExactOneBuiltinRuleProof,
    ArcsinExactZeroBuiltinRuleProof, ArcsinSinRightInverseBuiltinRuleProof,
    ArctanExactZeroBuiltinRuleProof, ArctanTanRightInverseBuiltinRuleProof,
    CosArccosLeftInverseBuiltinRuleProof, CotArccotLeftInverseBuiltinRuleProof,
    SinArcsinLeftInverseBuiltinRuleProof, TanArctanLeftInverseBuiltinRuleProof,
};
use super::by_set_builder_alpha_equal::BySetBuilderAlphaEqualBuiltinRuleProof;

// Each equality builtin rule gets its own variant and payload.
// Definitional unfolds are EqualitySearchProofByObjectDefinition, not here.
pub enum EqualitySearchProofByBuiltinRule {
    ByEqualIr(ByEqualIrBuiltinRuleProof),
    ByEqualToObjWithFreeParamsLookup(ByEqualToObjWithFreeParamsLookupBuiltinRuleProof),
    ByFnSetAlphaEqual(ByFnSetAlphaEqualBuiltinRuleProof),
    ByAnonymousFnAlphaEqual(ByAnonymousFnAlphaEqualBuiltinRuleProof),
    BySetBuilderAlphaEqual(BySetBuilderAlphaEqualBuiltinRuleProof),
    Calculation(EqualitySearchProofByCalculation),
    SinArcsinLeftInverse(SinArcsinLeftInverseBuiltinRuleProof),
    CosArccosLeftInverse(CosArccosLeftInverseBuiltinRuleProof),
    TanArctanLeftInverse(TanArctanLeftInverseBuiltinRuleProof),
    CotArccotLeftInverse(CotArccotLeftInverseBuiltinRuleProof),
    ArcsinSinRightInverse(ArcsinSinRightInverseBuiltinRuleProof),
    ArccosCosRightInverse(ArccosCosRightInverseBuiltinRuleProof),
    ArctanTanRightInverse(ArctanTanRightInverseBuiltinRuleProof),
    ArccotCotRightInverse(ArccotCotRightInverseBuiltinRuleProof),
    ArcsinExactZero(ArcsinExactZeroBuiltinRuleProof),
    ArcsinExactOne(ArcsinExactOneBuiltinRuleProof),
    ArcsinExactNegOne(ArcsinExactNegOneBuiltinRuleProof),
    ArccosExactOne(ArccosExactOneBuiltinRuleProof),
    ArccosExactZero(ArccosExactZeroBuiltinRuleProof),
    ArccosExactNegOne(ArccosExactNegOneBuiltinRuleProof),
    ArctanExactZero(ArctanExactZeroBuiltinRuleProof),
    ArccotExactZero(ArccotExactZeroBuiltinRuleProof),
}

// Builtin Calculation: both sides of an equality reduce to the same value
// without citing known equalities or forall facts.
//
// Mathematical property:
// - ClosedDecimal: closed numeric evaluation (decimal arithmetic).
// - Rational: zero-premise rational/polynomial monomial identity
//   (no denominator or negative-power obligations).
//
// Examples:
// - ClosedDecimal: `1 + 1 = 2`, `2 * 3 = 6`
// - Rational: `(x + 1) * (x - 1) = x^2 - 1`, `x + 0 = x`
//
// Payload: ClosedDecimal stores both normal forms; Rational stores none
// (legacy compares monomial vectors, not reconstructed Obj normals).
pub enum EqualitySearchProofByCalculation {
    // Both sides evaluate to the same normalized decimal.
    // Example: `1 + 1 = 2` with normals `"2"` and `"2"`.
    ClosedDecimal {
        left_normal: String,
        right_normal: String,
    },
    // Symbolic rational identity with an empty nonzero-obligation list.
    // Example: `(x + 1) * (x - 1) = x^2 - 1`.
    // Identities that need `d != 0` go to BuiltinStrategy::RationalWithNonzeroPremises.
    Rational {},
}
