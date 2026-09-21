use super::by_equal_ir::ByEqualIrBuiltinRuleProof;
use super::by_unfold_instantiated_template_have_fn_equal_application::ByUnfoldInstantiatedTemplateHaveFnEqualApplicationBuiltinRuleProof;
use super::by_unfold_instantiated_template_have_obj_equal::ByUnfoldInstantiatedTemplateHaveObjEqualBuiltinRuleProof;
use super::by_unfold_named_have_fn_equal_application::ByUnfoldNamedHaveFnEqualApplicationBuiltinRuleProof;

// Each equality builtin rule gets its own variant and payload.
pub enum EqualitySearchProofByBuiltinRule {
    ByEqualIr(ByEqualIrBuiltinRuleProof),
    Calculation(EqualitySearchProofByCalculation),
    ByUnfoldInstantiatedTemplateHaveObjEqual(
        ByUnfoldInstantiatedTemplateHaveObjEqualBuiltinRuleProof,
    ),
    ByUnfoldInstantiatedTemplateHaveFnEqualApplication(
        ByUnfoldInstantiatedTemplateHaveFnEqualApplicationBuiltinRuleProof,
    ),
    ByUnfoldNamedHaveFnEqualApplication(ByUnfoldNamedHaveFnEqualApplicationBuiltinRuleProof),
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
