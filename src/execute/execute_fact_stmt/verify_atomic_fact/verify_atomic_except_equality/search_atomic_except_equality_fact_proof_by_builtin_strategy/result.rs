use crate::ast::fact::Fact;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;

pub enum AtomicExceptEqualityFactSearchProofByBuiltinStrategy {
    PosAddPosIsPos(PosAddPosIsPosStrategySingleStep),
    NonnegativeSumIsNonnegative(NonnegativeSumIsNonnegativeStrategySingleStep),
    StrictAdditiveLeftStrict(StrictAdditiveLeftStrictStrategySingleStep),
    StrictAdditiveRightStrict(StrictAdditiveRightStrictStrategySingleStep),
    NonzeroProduct(NonzeroProductStrategySingleStep),
    FiniteSetMaxListMembersLessEqual(FiniteSetMaxListMembersLessEqualStrategySingleStep),
    FiniteSetMaxConstructorPartsLessEqual(FiniteSetMaxConstructorPartsLessEqualStrategySingleStep),
    FiniteSetMinListMembersLessEqual(FiniteSetMinListMembersLessEqualStrategySingleStep),
    FiniteSetMinConstructorPartsLessEqual(FiniteSetMinConstructorPartsLessEqualStrategySingleStep),
    ProductNonnegativeBothNonneg(ProductNonnegativeBothNonnegStrategySingleStep),
    ProductNonnegativeBothNonpos(ProductNonnegativeBothNonposStrategySingleStep),
    AddComponentwiseLessEqual(AddComponentwiseLessEqualStrategySingleStep),
    AddCrossedLessEqual(AddCrossedLessEqualStrategySingleStep),
    SubSharedSubtrahendLessEqual(SubSharedSubtrahendLessEqualStrategySingleStep),
    SubSharedMinuendLessEqual(SubSharedMinuendLessEqualStrategySingleStep),
    DivSharedPositiveDenomLessEqual(DivSharedPositiveDenomLessEqualStrategySingleStep),
    DivSharedNegativeDenomLessEqual(DivSharedNegativeDenomLessEqualStrategySingleStep),
    PowSharedExponentLessEqual(PowSharedExponentLessEqualStrategySingleStep),
    AbsVsSquareLessEqual(AbsVsSquareLessEqualStrategySingleStep),
    AddRightNonnegativeShiftLeft(AddRightNonnegativeShiftLeftStrategySingleStep),
    AddRightNonnegativeShiftRight(AddRightNonnegativeShiftRightStrategySingleStep),
    AddLeftNonpositiveShiftLeft(AddLeftNonpositiveShiftLeftStrategySingleStep),
    AddLeftNonpositiveShiftRight(AddLeftNonpositiveShiftRightStrategySingleStep),
    SubNonpositiveToZero(SubNonpositiveToZeroStrategySingleStep),
    SubNonnegativeFromZero(SubNonnegativeFromZeroStrategySingleStep),
    MulScaleFactorOneOrMoreRight(MulScaleFactorOneOrMoreRightStrategySingleStep),
    MulScaleFactorOneOrLessLeft(MulScaleFactorOneOrLessLeftStrategySingleStep),
    MulComponentwiseLessEqualAligned(MulComponentwiseLessEqualAlignedStrategySingleStep),
    MulComponentwiseLessEqualCrossed(MulComponentwiseLessEqualCrossedStrategySingleStep),
    CommonNonnegativeFactorLessEqual(CommonNonnegativeFactorLessEqualStrategySingleStep),
    ProductPositiveBothPos(ProductPositiveBothPosStrategySingleStep),
    ProductPositiveBothNeg(ProductPositiveBothNegStrategySingleStep),
    QuotientPositiveSameSignPos(QuotientPositiveSameSignPosStrategySingleStep),
    QuotientPositiveSameSignNeg(QuotientPositiveSameSignNegStrategySingleStep),
    AddComponentwiseStrictLeft(AddComponentwiseStrictLeftStrategySingleStep),
    AddComponentwiseStrictRight(AddComponentwiseStrictRightStrategySingleStep),
    SubSharedSubtrahendLess(SubSharedSubtrahendLessStrategySingleStep),
    SubSharedMinuendLess(SubSharedMinuendLessStrategySingleStep),
    DivSharedPositiveDenomLess(DivSharedPositiveDenomLessStrategySingleStep),
    DivSharedNegativeDenomLess(DivSharedNegativeDenomLessStrategySingleStep),
    PowSharedExponentLess(PowSharedExponentLessStrategySingleStep),
    AbsVsSquareLess(AbsVsSquareLessStrategySingleStep),
    AddRightStrictShiftLeftStrict(AddRightStrictShiftLeftStrictStrategySingleStep),
    AddRightStrictShiftLeftWeak(AddRightStrictShiftLeftWeakStrategySingleStep),
    AddRightStrictShiftRightStrict(AddRightStrictShiftRightStrictStrategySingleStep),
    AddRightStrictShiftRightWeak(AddRightStrictShiftRightWeakStrategySingleStep),
    SubPositiveToZero(SubPositiveToZeroStrategySingleStep),
    SubPositiveFromZero(SubPositiveFromZeroStrategySingleStep),
    CommonPositiveFactorLess(CommonPositiveFactorLessStrategySingleStep),
    FiniteSetSizeInNumericCarrier(FiniteSetSizeInNumericCarrierStrategySingleStep),
    FiniteExtremumSourceInCarrier(FiniteExtremumSourceInCarrierStrategySingleStep),
    RefinedNumericCarrier(RefinedNumericCarrierStrategySingleStep),
    RealArithmeticCarrierClosureAdd(RealArithmeticCarrierClosureAddStrategySingleStep),
    RealArithmeticCarrierClosureSub(RealArithmeticCarrierClosureSubStrategySingleStep),
    RealArithmeticCarrierClosureMul(RealArithmeticCarrierClosureMulStrategySingleStep),
    RealArithmeticCarrierClosureDiv(RealArithmeticCarrierClosureDivStrategySingleStep),
    RealArithmeticCarrierClosurePow(RealArithmeticCarrierClosurePowStrategySingleStep),
    RationalArithmeticCarrierClosureAdd(RationalArithmeticCarrierClosureAddStrategySingleStep),
    RationalArithmeticCarrierClosureSub(RationalArithmeticCarrierClosureSubStrategySingleStep),
    RationalArithmeticCarrierClosureMul(RationalArithmeticCarrierClosureMulStrategySingleStep),
    RationalArithmeticCarrierClosureDiv(RationalArithmeticCarrierClosureDivStrategySingleStep),
    RationalArithmeticCarrierClosurePow(RationalArithmeticCarrierClosurePowStrategySingleStep),
    RationalArithmeticCarrierClosureAbs(RationalArithmeticCarrierClosureAbsStrategySingleStep),
    IntegerArithmeticCarrierClosureAdd(IntegerArithmeticCarrierClosureAddStrategySingleStep),
    IntegerArithmeticCarrierClosureSub(IntegerArithmeticCarrierClosureSubStrategySingleStep),
    IntegerArithmeticCarrierClosureMul(IntegerArithmeticCarrierClosureMulStrategySingleStep),
    IntegerArithmeticCarrierClosureMod(IntegerArithmeticCarrierClosureModStrategySingleStep),
    IntegerArithmeticCarrierClosurePowNat(IntegerArithmeticCarrierClosurePowNatStrategySingleStep),
    IntegerArithmeticCarrierClosureAbs(IntegerArithmeticCarrierClosureAbsStrategySingleStep),
    NaturalArithmeticCarrierClosureAdd(NaturalArithmeticCarrierClosureAddStrategySingleStep),
    NaturalArithmeticCarrierClosureMul(NaturalArithmeticCarrierClosureMulStrategySingleStep),
    NaturalArithmeticCarrierClosureSub(NaturalArithmeticCarrierClosureSubStrategySingleStep),
    NaturalArithmeticCarrierClosurePow(NaturalArithmeticCarrierClosurePowStrategySingleStep),
    NaturalArithmeticCarrierClosureAbs(NaturalArithmeticCarrierClosureAbsStrategySingleStep),
    PositiveNaturalCarrierAddLeftPos(PositiveNaturalCarrierAddLeftPosStrategySingleStep),
    PositiveNaturalCarrierAddRightPos(PositiveNaturalCarrierAddRightPosStrategySingleStep),
    PositiveNaturalCarrierMul(PositiveNaturalCarrierMulStrategySingleStep),
    PositiveNaturalCarrierPow(PositiveNaturalCarrierPowStrategySingleStep),
    PositiveNaturalCarrierAbs(PositiveNaturalCarrierAbsStrategySingleStep),
    PositiveNaturalCarrierFiniteSetSize(PositiveNaturalCarrierFiniteSetSizeStrategySingleStep),
    CartMembership(CartMembershipStrategySingleStep),
    UnionMembershipFromLeft(UnionMembershipFromLeftStrategySingleStep),
    UnionMembershipFromRight(UnionMembershipFromRightStrategySingleStep),
    IntersectMembership(IntersectMembershipStrategySingleStep),
    SetMinusMembership(SetMinusMembershipStrategySingleStep),
    PowerSetMembership(PowerSetMembershipStrategySingleStep),
    RangeMembership(RangeMembershipStrategySingleStep),
    ClosedRangeMembership(ClosedRangeMembershipStrategySingleStep),
    IntervalMembership(IntervalMembershipStrategySingleStep),
    SetBuilderMembership(SetBuilderMembershipStrategySingleStep),
    StandardSetSubsetMembership(StandardSetSubsetMembershipStrategySingleStep),
    FnApplicationInCodomain(FnApplicationInCodomainStrategySingleStep),
    ListSetSubsetFromMembers(ListSetSubsetFromMembersStrategySingleStep),
    UnionSubsetFromBothOperands(UnionSubsetFromBothOperandsStrategySingleStep),
    IntersectSubsetFromLeftOperand(IntersectSubsetFromLeftOperandStrategySingleStep),
    IntersectSubsetFromRightOperand(IntersectSubsetFromRightOperandStrategySingleStep),
    SetMinusSubsetFromLeft(SetMinusSubsetFromLeftStrategySingleStep),
    SubsetOfIntersectFromBothBounds(SubsetOfIntersectFromBothBoundsStrategySingleStep),
    FnRangeFiniteFromDomain(FnRangeFiniteFromDomainStrategySingleStep),
    PowerSetFiniteFromBase(PowerSetFiniteFromBaseStrategySingleStep),
    SetBuilderFiniteFromParamSet(SetBuilderFiniteFromParamSetStrategySingleStep),
    UnionFiniteFromBoth(UnionFiniteFromBothStrategySingleStep),
    IntersectFiniteFromBoth(IntersectFiniteFromBothStrategySingleStep),
    SetMinusFiniteFromLeft(SetMinusFiniteFromLeftStrategySingleStep),
    CartFiniteFromFactors(CartFiniteFromFactorsStrategySingleStep),
    SubsetOfFiniteSet(SubsetOfFiniteSetStrategySingleStep),
    ClosedRangeNonemptyFromEndpointOrder(ClosedRangeNonemptyFromEndpointOrderStrategySingleStep),
    RangeNonemptyFromEndpointOrder(RangeNonemptyFromEndpointOrderStrategySingleStep),
    IntervalNonemptyFromEndpointOrder(IntervalNonemptyFromEndpointOrderStrategySingleStep),
    UnionNonemptyFromLeft(UnionNonemptyFromLeftStrategySingleStep),
    UnionNonemptyFromRight(UnionNonemptyFromRightStrategySingleStep),
    CartNonemptyFromAllFactors(CartNonemptyFromAllFactorsStrategySingleStep),
    FnSetNonemptyFromCodomain(FnSetNonemptyFromCodomainStrategySingleStep),
    AnonymousFnNonemptyFromCodomain(AnonymousFnNonemptyFromCodomainStrategySingleStep),
    FiniteSeqSetNonemptyFromCodomain(FiniteSeqSetNonemptyFromCodomainStrategySingleStep),
    SeqSetNonemptyFromCodomain(SeqSetNonemptyFromCodomainStrategySingleStep),
}

// Strategy: strict positive sum
// Mathematical property: a>0,b>0 => a+b>0
//
// Example:
//   a + b > 0
pub struct PosAddPosIsPosStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: nonnegative sum
// Mathematical property: 0<=a,0<=b => 0<=a+b
//
// Example:
//   0 <= a + b
pub struct NonnegativeSumIsNonnegativeStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: left-strict additive
// Mathematical property: 0<a,0<=b => 0<a+b
//
// Example:
//   0 < a + b
pub struct StrictAdditiveLeftStrictStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: right-strict additive
// Mathematical property: 0<=a,0<b => 0<a+b
//
// Example:
//   0 < a + b
pub struct StrictAdditiveRightStrictStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: nonzero product
// Mathematical property: a!=0,b!=0 => a*b!=0
//
// Example:
//   a * b != 0
pub struct NonzeroProductStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: max list bound
// Mathematical property: each a_i<=R => max<=R
//
// Example:
//   finite_set_max({1,2}) <= 3
pub struct FiniteSetMaxListMembersLessEqualStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: max constructor parts
// Mathematical property: parts max <= R
//
// Example:
//   max(union(A,B)) <= R
pub struct FiniteSetMaxConstructorPartsLessEqualStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: min list bound
// Mathematical property: L<=each => L<=min
//
// Example:
//   0 <= finite_set_min({1,2})
pub struct FiniteSetMinListMembersLessEqualStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: min constructor parts
// Mathematical property: L <= parts min
//
// Example:
//   L <= min(union(A,B))
pub struct FiniteSetMinConstructorPartsLessEqualStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: product nonnegative
// Mathematical property: 0<=a,0<=b => 0<=a*b
//
// Example:
//   0 <= a * b
pub struct ProductNonnegativeBothNonnegStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: product of nonpos
// Mathematical property: a<=0,b<=0 => 0<=a*b
//
// Example:
//   0 <= a * b
pub struct ProductNonnegativeBothNonposStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: add componentwise
// Mathematical property: a<=c,b<=d => a+b<=c+d
//
// Example:
//   a + b <= c + d
pub struct AddComponentwiseLessEqualStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: add crossed
// Mathematical property: a<=d,b<=c => a+b<=c+d
//
// Example:
//   a + b <= c + d
pub struct AddCrossedLessEqualStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: sub shared subtrahend
// Mathematical property: a<=b => a-c<=b-c
//
// Example:
//   a - c <= b - c
pub struct SubSharedSubtrahendLessEqualStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: sub shared minuend
// Mathematical property: c<=d => a-d<=a-c
//
// Example:
//   a - d <= a - c
pub struct SubSharedMinuendLessEqualStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: div pos denom
// Mathematical property: 0<c,a<=b => a/c<=b/c
//
// Example:
//   a / c <= b / c
pub struct DivSharedPositiveDenomLessEqualStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: div neg denom
// Mathematical property: c<0,b<=a => a/c<=b/c
//
// Example:
//   a / c <= b / c
pub struct DivSharedNegativeDenomLessEqualStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: pow shared exp weak
// Mathematical property: n in N+,0<=a<=b => a^n<=b^n
//
// Example:
//   a^n <= b^n
pub struct PowSharedExponentLessEqualStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: abs vs square weak
// Mathematical property: x^2<=y^2 => abs(x)<=abs(y)
//
// Example:
//   abs(x) <= abs(y)
pub struct AbsVsSquareLessEqualStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: add right shift left
// Mathematical property: L<=a,0<=b => L<=a+b
//
// Example:
//   L <= a + b
pub struct AddRightNonnegativeShiftLeftStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: add right shift right
// Mathematical property: L<=b,0<=a => L<=a+b
//
// Example:
//   L <= a + b
pub struct AddRightNonnegativeShiftRightStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: add left shift left
// Mathematical property: a<=R,b<=0 => a+b<=R
//
// Example:
//   a + b <= R
pub struct AddLeftNonpositiveShiftLeftStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: add left shift right
// Mathematical property: b<=R,a<=0 => a+b<=R
//
// Example:
//   a + b <= R
pub struct AddLeftNonpositiveShiftRightStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: sub to zero weak
// Mathematical property: a<=b => a-b<=0
//
// Example:
//   a - b <= 0
pub struct SubNonpositiveToZeroStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: sub from zero weak
// Mathematical property: b<=a => 0<=a-b
//
// Example:
//   0 <= a - b
pub struct SubNonnegativeFromZeroStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: mul scale grow
// Mathematical property: 0<=b,1<=a => b<=a*b
//
// Example:
//   b <= a * b
pub struct MulScaleFactorOneOrMoreRightStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: mul scale shrink
// Mathematical property: 0<=b,a<=1 => a*b<=b
//
// Example:
//   a * b <= b
pub struct MulScaleFactorOneOrLessLeftStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: mul componentwise aligned
// Mathematical property: 0<=a,b,a<=c,b<=d => a*b<=c*d
//
// Example:
//   a * b <= c * d
pub struct MulComponentwiseLessEqualAlignedStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: mul componentwise crossed
// Mathematical property: 0<=a,b,a<=d,b<=c => a*b<=c*d
//
// Example:
//   a * b <= c * d
pub struct MulComponentwiseLessEqualCrossedStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: common nonnegative factor
// Mathematical property: 0<=c,a<=b => a*c<=b*c
//
// Example:
//   a * c <= b * c
pub struct CommonNonnegativeFactorLessEqualStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: product positive
// Mathematical property: 0<a,0<b => 0<a*b
//
// Example:
//   0 < a * b
pub struct ProductPositiveBothPosStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: product of negatives
// Mathematical property: a<0,b<0 => 0<a*b
//
// Example:
//   0 < a * b
pub struct ProductPositiveBothNegStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: quotient positive
// Mathematical property: 0<a,0<b => 0<a/b
//
// Example:
//   0 < a / b
pub struct QuotientPositiveSameSignPosStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: quotient of negatives
// Mathematical property: a<0,b<0 => 0<a/b
//
// Example:
//   0 < a / b
pub struct QuotientPositiveSameSignNegStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: add strict left
// Mathematical property: a<c,b<=d => a+b<c+d
//
// Example:
//   a + b < c + d
pub struct AddComponentwiseStrictLeftStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: add strict right
// Mathematical property: a<=c,b<d => a+b<c+d
//
// Example:
//   a + b < c + d
pub struct AddComponentwiseStrictRightStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: sub shared subtrahend strict
// Mathematical property: a<b => a-c<b-c
//
// Example:
//   a - c < b - c
pub struct SubSharedSubtrahendLessStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: sub shared minuend strict
// Mathematical property: c<d => a-d<a-c
//
// Example:
//   a - d < a - c
pub struct SubSharedMinuendLessStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: div pos denom strict
// Mathematical property: 0<c,a<b => a/c<b/c
//
// Example:
//   a / c < b / c
pub struct DivSharedPositiveDenomLessStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: div neg denom strict
// Mathematical property: c<0,b<a => a/c<b/c
//
// Example:
//   a / c < b / c
pub struct DivSharedNegativeDenomLessStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: pow shared exp strict
// Mathematical property: n in N+,0<=a<b => a^n<b^n
//
// Example:
//   a^n < b^n
pub struct PowSharedExponentLessStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: abs vs square strict
// Mathematical property: x^2<y^2 => abs(x)<abs(y)
//
// Example:
//   abs(x) < abs(y)
pub struct AbsVsSquareLessStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: add right strict L
// Mathematical property: L<a,0<=b => L<a+b
//
// Example:
//   L < a + b
pub struct AddRightStrictShiftLeftStrictStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: add right weak L
// Mathematical property: L<=a,0<b => L<a+b
//
// Example:
//   L < a + b
pub struct AddRightStrictShiftLeftWeakStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: add right strict R
// Mathematical property: L<b,0<=a => L<a+b
//
// Example:
//   L < a + b
pub struct AddRightStrictShiftRightStrictStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: add right weak R
// Mathematical property: L<=b,0<a => L<a+b
//
// Example:
//   L < a + b
pub struct AddRightStrictShiftRightWeakStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: sub to zero strict
// Mathematical property: a<b => a-b<0
//
// Example:
//   a - b < 0
pub struct SubPositiveToZeroStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: sub from zero strict
// Mathematical property: b<a => 0<a-b
//
// Example:
//   0 < a - b
pub struct SubPositiveFromZeroStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: common positive factor
// Mathematical property: 0<c,a<b => a*c<b*c
//
// Example:
//   a * c < b * c
pub struct CommonPositiveFactorLessStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: finite size carrier
// Mathematical property: finite S => size in N
//
// Example:
//   finite_set_size(S) $in N
pub struct FiniteSetSizeInNumericCarrierStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: extremum carrier
// Mathematical property: elements in R => max in R
//
// Example:
//   finite_set_max(S) $in R
pub struct FiniteExtremumSourceInCarrierStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: refined carrier
// Mathematical property: base + sign => R+
//
// Example:
//   x $in R+
pub struct RefinedNumericCarrierStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: R add closure
// Mathematical property: a,b in R => a+b in R
//
// Example:
//   a + b $in R
pub struct RealArithmeticCarrierClosureAddStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: R sub closure
// Mathematical property: a,b in R => a-b in R
//
// Example:
//   a - b $in R
pub struct RealArithmeticCarrierClosureSubStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: R mul closure
// Mathematical property: a,b in R => a*b in R
//
// Example:
//   a * b $in R
pub struct RealArithmeticCarrierClosureMulStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: R div closure
// Mathematical property: a,b in R => a/b in R
//
// Example:
//   a / b $in R
pub struct RealArithmeticCarrierClosureDivStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: R pow closure
// Mathematical property: a in R => a^n in R
//
// Example:
//   a^2 $in R
pub struct RealArithmeticCarrierClosurePowStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: Q add
// Mathematical property: a,b in Q => a+b in Q
//
// Example:
//   a + b $in Q
pub struct RationalArithmeticCarrierClosureAddStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: Q sub
// Mathematical property: a,b in Q => a-b in Q
//
// Example:
//   a - b $in Q
pub struct RationalArithmeticCarrierClosureSubStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: Q mul
// Mathematical property: a,b in Q => a*b in Q
//
// Example:
//   a * b $in Q
pub struct RationalArithmeticCarrierClosureMulStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: Q div
// Mathematical property: a,b in Q => a/b in Q
//
// Example:
//   a / b $in Q
pub struct RationalArithmeticCarrierClosureDivStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: Q pow
// Mathematical property: a in Q,n in Z => a^n in Q
//
// Example:
//   a^n $in Q
pub struct RationalArithmeticCarrierClosurePowStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: Q abs
// Mathematical property: a in Q => abs(a) in Q
//
// Example:
//   abs(a) $in Q
pub struct RationalArithmeticCarrierClosureAbsStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: Z add
// Mathematical property: a,b in Z => a+b in Z
//
// Example:
//   a + b $in Z
pub struct IntegerArithmeticCarrierClosureAddStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: Z sub
// Mathematical property: a,b in Z => a-b in Z
//
// Example:
//   a - b $in Z
pub struct IntegerArithmeticCarrierClosureSubStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: Z mul
// Mathematical property: a,b in Z => a*b in Z
//
// Example:
//   a * b $in Z
pub struct IntegerArithmeticCarrierClosureMulStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: Z mod
// Mathematical property: a,b in Z => a%b in Z
//
// Example:
//   a % b $in Z
pub struct IntegerArithmeticCarrierClosureModStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: Z pow nat
// Mathematical property: a in Z,n in N => a^n in Z
//
// Example:
//   a^n $in Z
pub struct IntegerArithmeticCarrierClosurePowNatStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: Z abs
// Mathematical property: a in Z => abs(a) in Z
//
// Example:
//   abs(a) $in Z
pub struct IntegerArithmeticCarrierClosureAbsStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: N add
// Mathematical property: a,b in N => a+b in N
//
// Example:
//   a + b $in N
pub struct NaturalArithmeticCarrierClosureAddStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: N mul
// Mathematical property: a,b in N => a*b in N
//
// Example:
//   a * b $in N
pub struct NaturalArithmeticCarrierClosureMulStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: N sub
// Mathematical property: b<=a => a-b in N
//
// Example:
//   a - b $in N
pub struct NaturalArithmeticCarrierClosureSubStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: N pow
// Mathematical property: a,b in N => a^b in N
//
// Example:
//   a^b $in N
pub struct NaturalArithmeticCarrierClosurePowStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: N abs
// Mathematical property: a in Z => abs(a) in N
//
// Example:
//   abs(a) $in N
pub struct NaturalArithmeticCarrierClosureAbsStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: N+ add left
// Mathematical property: a in N+,b in N => a+b in N+
//
// Example:
//   a + b $in N+
pub struct PositiveNaturalCarrierAddLeftPosStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: N+ add right
// Mathematical property: a in N,b in N+ => a+b in N+
//
// Example:
//   a + b $in N+
pub struct PositiveNaturalCarrierAddRightPosStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: N+ mul
// Mathematical property: a,b in N+ => a*b in N+
//
// Example:
//   a * b $in N+
pub struct PositiveNaturalCarrierMulStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: N+ pow
// Mathematical property: a in N+,n in N => a^n in N+
//
// Example:
//   a^n $in N+
pub struct PositiveNaturalCarrierPowStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: N+ abs
// Mathematical property: 0<abs(a) => abs(a) in N+
//
// Example:
//   abs(a) $in N+
pub struct PositiveNaturalCarrierAbsStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: N+ size
// Mathematical property: 1<=size => size in N+
//
// Example:
//   size $in N+
pub struct PositiveNaturalCarrierFiniteSetSizeStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: cart membership
// Mathematical property: coords in factors
//
// Example:
//   (1,2) $in cart(R,Z)
pub struct CartMembershipStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: union from left
// Mathematical property: x in A => x in union(A,B)
//
// Example:
//   1 $in union({1},{2})
pub struct UnionMembershipFromLeftStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: union from right
// Mathematical property: x in B => x in union(A,B)
//
// Example:
//   2 $in union({1},{2})
pub struct UnionMembershipFromRightStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: intersect membership
// Mathematical property: x in A and B
//
// Example:
//   2 $in intersect({1,2},{2,3})
pub struct IntersectMembershipStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: set minus membership
// Mathematical property: x in A not in B
//
// Example:
//   2 $in set_minus({1,2},{1})
pub struct SetMinusMembershipStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: power set membership
// Mathematical property: A subset B => A in power_set(B)
//
// Example:
//   {1} $in power_set({1,2})
pub struct PowerSetMembershipStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: range membership
// Mathematical property: start<=x<end
//
// Example:
//   1 $in range(1,3)
pub struct RangeMembershipStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: closed range membership
// Mathematical property: start<=x<=end
//
// Example:
//   2 $in closed_range(1,2)
pub struct ClosedRangeMembershipStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: interval membership
// Mathematical property: x in R and bounds
//
// Example:
//   c $in '(a,b)
pub struct IntervalMembershipStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: set builder membership
// Mathematical property: x in T and P(x)
//
// Example:
//   a $in {x R: x > 0}
pub struct SetBuilderMembershipStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: lift along N⊆Z⊆Q⊆R⊆C (one source membership per layer)
// Mathematical property: x $in S and S ⊂ T ⇒ x $in T among standard sets
//
// Example:
//   dot(vec(a,b), vec(a,c)) $in C  via proving  … $in R then ⊂-lift
pub struct StandardSetSubsetMembershipStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: well-typed fn application lands in declared return set
// Mathematical property: f $in fn(params) Ret and args in domain ⇒ f(args) $in Ret
//
// Example:
//   dot(u, v) $in R after domain memberships of u,v under strategy depth
pub struct FnApplicationInCodomainStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: list subset
// Mathematical property: members in B
//
// Example:
//   {1,2} $subset N
pub struct ListSetSubsetFromMembersStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: union subset
// Mathematical property: A,B subset C
//
// Example:
//   union(A,B) $subset C
pub struct UnionSubsetFromBothOperandsStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: intersect subset left
// Mathematical property: A subset C
//
// Example:
//   intersect(A,B) $subset C
pub struct IntersectSubsetFromLeftOperandStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: intersect subset right
// Mathematical property: B subset C
//
// Example:
//   intersect(A,B) $subset C
pub struct IntersectSubsetFromRightOperandStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: set minus subset
// Mathematical property: A subset C
//
// Example:
//   set_minus(A,B) $subset C
pub struct SetMinusSubsetFromLeftStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: subset of intersect
// Mathematical property: A subset B and C
//
// Example:
//   A $subset intersect(B,C)
pub struct SubsetOfIntersectFromBothBoundsStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: fn range finite
// Mathematical property: finite domain => finite range
//
// Example:
//   $is_finite_set(fn_range(f))
pub struct FnRangeFiniteFromDomainStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: power set finite
// Mathematical property: finite S => finite power_set(S)
//
// Example:
//   $is_finite_set(power_set({1}))
pub struct PowerSetFiniteFromBaseStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: set builder finite
// Mathematical property: finite T => finite builder
//
// Example:
//   $is_finite_set({x T: P})
pub struct SetBuilderFiniteFromParamSetStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: union finite
// Mathematical property: both finite
//
// Example:
//   $is_finite_set(union(A,B))
pub struct UnionFiniteFromBothStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: intersect finite
// Mathematical property: both finite
//
// Example:
//   $is_finite_set(intersect(A,B))
pub struct IntersectFiniteFromBothStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: set minus finite
// Mathematical property: left finite
//
// Example:
//   $is_finite_set(set_minus(A,B))
pub struct SetMinusFiniteFromLeftStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: cart finite
// Mathematical property: factors finite
//
// Example:
//   $is_finite_set(cart(A,B))
pub struct CartFiniteFromFactorsStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// A checked finite upper-set witness makes its subset finite.
pub struct SubsetOfFiniteSetStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: closed range nonempty
// Mathematical property: start<=end
//
// Example:
//   $is_nonempty_set(closed_range(1,2))
pub struct ClosedRangeNonemptyFromEndpointOrderStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: range nonempty
// Mathematical property: start<end
//
// Example:
//   $is_nonempty_set(range(1,3))
pub struct RangeNonemptyFromEndpointOrderStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: interval nonempty
// Mathematical property: endpoint order
//
// Example:
//   $is_nonempty_set('[1,2])
pub struct IntervalNonemptyFromEndpointOrderStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: union nonempty left
// Mathematical property: A nonempty
//
// Example:
//   $is_nonempty_set(union(A,B))
pub struct UnionNonemptyFromLeftStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: union nonempty right
// Mathematical property: B nonempty
//
// Example:
//   $is_nonempty_set(union(A,B))
pub struct UnionNonemptyFromRightStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: cart nonempty
// Mathematical property: all factors nonempty
//
// Example:
//   $is_nonempty_set(cart(A,B))
pub struct CartNonemptyFromAllFactorsStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: fn set nonempty
// Mathematical property: codomain nonempty
//
// Example:
//   $is_nonempty_set(fn(x R) R)
pub struct FnSetNonemptyFromCodomainStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: anon fn nonempty
// Mathematical property: codomain nonempty
//
// Example:
//   $is_nonempty_set(fn(x R) R {x})
pub struct AnonymousFnNonemptyFromCodomainStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: finite seq nonempty
// Mathematical property: S nonempty
//
// Example:
//   $is_nonempty_set(finite_seq(R,2))
pub struct FiniteSeqSetNonemptyFromCodomainStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Strategy: seq nonempty
// Mathematical property: S nonempty
//
// Example:
//   $is_nonempty_set(seq(R))
pub struct SeqSetNonemptyFromCodomainStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
