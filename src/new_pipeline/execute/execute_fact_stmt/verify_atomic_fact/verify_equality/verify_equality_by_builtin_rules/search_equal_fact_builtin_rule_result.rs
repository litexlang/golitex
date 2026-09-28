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
use super::by_equality_identities_wave2::{
    AbsOfNegationBuiltinRuleProof, AbsProductBuiltinRuleProof, AbsSquareBuiltinRuleProof,
    LogArgPowerBuiltinRuleProof, LogBaseSelfBuiltinRuleProof, LogChangeOfBaseBuiltinRuleProof,
    LogOfOneBuiltinRuleProof, LogOfPowerSameBaseBuiltinRuleProof, LogProductBuiltinRuleProof,
    LogQuotientBuiltinRuleProof, LogReciprocalBuiltinRuleProof, ModOneBuiltinRuleProof,
    NestedSameModAbsorptionBuiltinRuleProof, OneModAtLeastTwoBuiltinRuleProof,
    OneToAnyPowerBuiltinRuleProof, SqrtOfSquareBuiltinRuleProof, SqrtOneBuiltinRuleProof,
    SqrtProductBuiltinRuleProof, SqrtQuotientBuiltinRuleProof, SqrtSquareBuiltinRuleProof,
    SqrtZeroBuiltinRuleProof, ZeroModBuiltinRuleProof, ZeroToPosNatPowerBuiltinRuleProof,
};
use super::by_equality_identities_wave3::{
    AbsAbsAbsorptionBuiltinRuleProof, CeilOfIntegerBuiltinRuleProof, ExpOfLnBuiltinRuleProof,
    FloorOfIntegerBuiltinRuleProof, LnOfExpBuiltinRuleProof, MaxCommutativeBuiltinRuleProof,
    MaxIdempotentBuiltinRuleProof, MinCommutativeBuiltinRuleProof, MinIdempotentBuiltinRuleProof,
    ModSelfZeroBuiltinRuleProof,
};
use super::by_equality_identities_wave4::{
    CeilOfFloorOfIntegerBuiltinRuleProof, FloorOfCeilOfIntegerBuiltinRuleProof,
    SqrtOfSquareEqualsAbsBuiltinRuleProof,
};
use super::by_equality_identities_wave5::{
    FactorialSuccessorBuiltinRuleProof, GcdCommutativeBuiltinRuleProof,
    GcdIdempotentAbsBuiltinRuleProof, GcdLeftZeroAbsBuiltinRuleProof,
    GcdRightZeroAbsBuiltinRuleProof, LcmCommutativeBuiltinRuleProof,
    LcmIdempotentAbsBuiltinRuleProof, QuotByOneBuiltinRuleProof, QuotSelfOneBuiltinRuleProof,
};
use super::by_equality_identities_wave6::{
    AbsNonnegEqualsSelfBuiltinRuleProof, AbsNonposEqualsNegationBuiltinRuleProof,
    MaxLeftWhenLessEqualBuiltinRuleProof, MaxRightWhenLessEqualBuiltinRuleProof,
    MinLeftWhenLessEqualBuiltinRuleProof, MinRightWhenLessEqualBuiltinRuleProof,
    SignOfNegativeBuiltinRuleProof, SignOfPositiveBuiltinRuleProof,
};
use super::by_equality_identities_wave7::{
    AbsEqualsSignTimesArgBuiltinRuleProof, DiffZeroFromEqualOperandsBuiltinRuleProof,
    EqualityFromTwoSidedWeakOrderBuiltinRuleProof, GcdDividesArgumentBuiltinRuleProof,
    ProductModFactorZeroBuiltinRuleProof, SignOfNegationBuiltinRuleProof,
    SignOfProductBuiltinRuleProof, SignTimesAbsEqualsArgBuiltinRuleProof,
    SubtractionFromKnownAdditionBuiltinRuleProof, ZeroProductCancelBuiltinRuleProof,
};
use super::by_equality_identities_wave8::{
    LcmGcdProductAbsBuiltinRuleProof, MinusOneOddNaturalPowerBuiltinRuleProof,
    ModDividendMinusRemainderZeroBuiltinRuleProof, QuotEuclideanDecompositionBuiltinRuleProof,
    SquareSumComponentZeroBuiltinRuleProof,
};
use super::by_power_laws::{
    PowerOfPowerBuiltinRuleProof, PowerOfProductBuiltinRuleProof,
    PowerProductSameBaseBuiltinRuleProof, QuotientAsMulNegOnePowerBuiltinRuleProof,
    ReciprocalAsNegOnePowerBuiltinRuleProof,
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
    PowerProductSameBase(PowerProductSameBaseBuiltinRuleProof),
    PowerOfPower(PowerOfPowerBuiltinRuleProof),
    PowerOfProduct(PowerOfProductBuiltinRuleProof),
    ReciprocalAsNegOnePower(ReciprocalAsNegOnePowerBuiltinRuleProof),
    QuotientAsMulNegOnePower(QuotientAsMulNegOnePowerBuiltinRuleProof),
    OneToAnyPower(OneToAnyPowerBuiltinRuleProof),
    ZeroToPosNatPower(ZeroToPosNatPowerBuiltinRuleProof),
    SqrtSquare(SqrtSquareBuiltinRuleProof),
    SqrtZero(SqrtZeroBuiltinRuleProof),
    SqrtOne(SqrtOneBuiltinRuleProof),
    SqrtOfSquare(SqrtOfSquareBuiltinRuleProof),
    SqrtProduct(SqrtProductBuiltinRuleProof),
    SqrtQuotient(SqrtQuotientBuiltinRuleProof),
    AbsOfNegation(AbsOfNegationBuiltinRuleProof),
    AbsProduct(AbsProductBuiltinRuleProof),
    AbsSquare(AbsSquareBuiltinRuleProof),
    LogBaseSelf(LogBaseSelfBuiltinRuleProof),
    LogOfOne(LogOfOneBuiltinRuleProof),
    LogOfPowerSameBase(LogOfPowerSameBaseBuiltinRuleProof),
    LogArgPower(LogArgPowerBuiltinRuleProof),
    LogProduct(LogProductBuiltinRuleProof),
    LogQuotient(LogQuotientBuiltinRuleProof),
    LogReciprocal(LogReciprocalBuiltinRuleProof),
    LogChangeOfBase(LogChangeOfBaseBuiltinRuleProof),
    ZeroMod(ZeroModBuiltinRuleProof),
    ModOne(ModOneBuiltinRuleProof),
    OneModAtLeastTwo(OneModAtLeastTwoBuiltinRuleProof),
    NestedSameModAbsorption(NestedSameModAbsorptionBuiltinRuleProof),
    MinIdempotent(MinIdempotentBuiltinRuleProof),
    MaxIdempotent(MaxIdempotentBuiltinRuleProof),
    MinCommutative(MinCommutativeBuiltinRuleProof),
    MaxCommutative(MaxCommutativeBuiltinRuleProof),
    AbsAbsAbsorption(AbsAbsAbsorptionBuiltinRuleProof),
    ExpOfLn(ExpOfLnBuiltinRuleProof),
    LnOfExp(LnOfExpBuiltinRuleProof),
    FloorOfInteger(FloorOfIntegerBuiltinRuleProof),
    CeilOfInteger(CeilOfIntegerBuiltinRuleProof),
    ModSelfZero(ModSelfZeroBuiltinRuleProof),
    FloorOfCeilOfInteger(FloorOfCeilOfIntegerBuiltinRuleProof),
    CeilOfFloorOfInteger(CeilOfFloorOfIntegerBuiltinRuleProof),
    SqrtOfSquareEqualsAbs(SqrtOfSquareEqualsAbsBuiltinRuleProof),
    QuotByOne(QuotByOneBuiltinRuleProof),
    QuotSelfOne(QuotSelfOneBuiltinRuleProof),
    LcmCommutative(LcmCommutativeBuiltinRuleProof),
    LcmIdempotentAbs(LcmIdempotentAbsBuiltinRuleProof),
    GcdCommutative(GcdCommutativeBuiltinRuleProof),
    GcdIdempotentAbs(GcdIdempotentAbsBuiltinRuleProof),
    GcdRightZeroAbs(GcdRightZeroAbsBuiltinRuleProof),
    GcdLeftZeroAbs(GcdLeftZeroAbsBuiltinRuleProof),
    FactorialSuccessor(FactorialSuccessorBuiltinRuleProof),
    AbsNonnegEqualsSelf(AbsNonnegEqualsSelfBuiltinRuleProof),
    AbsNonposEqualsNegation(AbsNonposEqualsNegationBuiltinRuleProof),
    SignOfPositive(SignOfPositiveBuiltinRuleProof),
    SignOfNegative(SignOfNegativeBuiltinRuleProof),
    MaxRightWhenLessEqual(MaxRightWhenLessEqualBuiltinRuleProof),
    MaxLeftWhenLessEqual(MaxLeftWhenLessEqualBuiltinRuleProof),
    MinLeftWhenLessEqual(MinLeftWhenLessEqualBuiltinRuleProof),
    MinRightWhenLessEqual(MinRightWhenLessEqualBuiltinRuleProof),
    GcdDividesArgument(GcdDividesArgumentBuiltinRuleProof),
    ProductModFactorZero(ProductModFactorZeroBuiltinRuleProof),
    EqualityFromTwoSidedWeakOrder(EqualityFromTwoSidedWeakOrderBuiltinRuleProof),
    DiffZeroFromEqualOperands(DiffZeroFromEqualOperandsBuiltinRuleProof),
    ZeroProductCancel(ZeroProductCancelBuiltinRuleProof),
    SignOfNegation(SignOfNegationBuiltinRuleProof),
    SignTimesAbsEqualsArg(SignTimesAbsEqualsArgBuiltinRuleProof),
    AbsEqualsSignTimesArg(AbsEqualsSignTimesArgBuiltinRuleProof),
    SignOfProduct(SignOfProductBuiltinRuleProof),
    SubtractionFromKnownAddition(SubtractionFromKnownAdditionBuiltinRuleProof),
    QuotEuclideanDecomposition(QuotEuclideanDecompositionBuiltinRuleProof),
    ModDividendMinusRemainderZero(ModDividendMinusRemainderZeroBuiltinRuleProof),
    SquareSumComponentZero(SquareSumComponentZeroBuiltinRuleProof),
    MinusOneOddNaturalPower(MinusOneOddNaturalPowerBuiltinRuleProof),
    LcmGcdProductAbs(LcmGcdProductAbsBuiltinRuleProof),
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
