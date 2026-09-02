//! Top-level builtin-rule evidence sum type.

use super::*;
use std::fmt;

#[derive(Clone)]
pub enum BuiltinRuleEvidence {
    /// A typed verifier-owned rule that deliberately has no reviewed ToLean
    /// mapping yet. The exact enum variant, rather than a diagnostic string,
    /// is the rule identity.
    Uncatalogued(UncataloguedBuiltinRule),
    DefinitionProjection(DefinitionProjectionBuiltinRuleEvidence),
    SetBuilderMembership(SetBuilderMembershipBuiltinRuleEvidence),
    FunctionSetMembership(FunctionSetMembershipBuiltinRuleEvidence),
    FunctionApplicationInRange(FunctionApplicationInRangeBuiltinRuleEvidence),
    FunctionRangeSubset(FunctionRangeSubsetBuiltinRuleEvidence),
    RealIntervalSubsetReal(RealIntervalSubsetRealBuiltinRuleEvidence),
    TupleCartesianMembership(TupleCartesianMembershipBuiltinRuleEvidence),
    IntegerRangeSumPointwiseOrder(IntegerRangeSumPointwiseOrderBuiltinRuleEvidence),
    RefinedNumericMembership(RefinedNumericMembershipBuiltinRuleEvidence),
    ClosedNumericMembership(ClosedNumericMembershipBuiltinRuleEvidence),
    ClosedNumericNonmembership(ClosedNumericNonmembershipBuiltinRuleEvidence),
    ClosedNumericComparison(ClosedNumericComparisonBuiltinRuleEvidence),
    OrderReflexivity(OrderReflexivityBuiltinRuleEvidence),
    RuntimeResolvedNumericComparison(RuntimeResolvedNumericComparisonBuiltinRuleEvidence),
    RegisteredReflexivePredicate(RegisteredReflexivePredicateBuiltinRuleEvidence),
    RegisteredSymmetricPredicate(RegisteredSymmetricPredicateBuiltinRuleEvidence),
    RegisteredAntisymmetricPredicate(RegisteredAntisymmetricPredicateBuiltinRuleEvidence),
    ObjectReflexivity(ObjectReflexivityBuiltinRuleEvidence),
    RationalNormalization(RationalNormalizationBuiltinRuleEvidence),
    RationalAlgebraicNormalization(RationalAlgebraicNormalizationBuiltinRuleEvidence),
    ComplexAlgebraicNormalization(ComplexAlgebraicNormalizationBuiltinRuleEvidence),
    StructuralDefinitionCongruence(StructuralDefinitionCongruenceBuiltinRuleEvidence),
    StructuralKnownEqualityCongruence(StructuralKnownEqualityCongruenceBuiltinRuleEvidence),
    IntegralPolynomialNormalization(IntegralPolynomialNormalizationBuiltinRuleEvidence),
    StandardSetNonempty(StandardSetNonemptyBuiltinRuleEvidence),
    /// A nonempty finite set literal is inhabited by the first singleton
    /// carrier in its exact coproduct encoding.
    LiteralSetNonempty,
    /// A predicate-defined set is contained in its exact base carrier.
    SetBuilderSubsetBase,
    /// A predicate-defined subset of `S` belongs to `power_set(T)` after one
    /// checked child proves `S subset T`.
    SetBuilderInPowerSetViaParamSubset,
    DisjunctionIntroduction(DisjunctionIntroductionBuiltinRuleEvidence),
    FunctionApplicationReturnMembership(FunctionApplicationReturnMembershipBuiltinRuleEvidence),
    MatrixExpressionMembership(MatrixExpressionMembershipBuiltinRuleEvidence),
    KnownEqualityPath(KnownEqualityBuiltinRuleEvidence),
    DivNotEqualZero(DivNotEqualZeroBuiltinRuleEvidence),
    Arithmetic(ArithmeticBuiltinRule),
    IntegerMembershipClosure(IntegerMembershipClosureBuiltinRule),
    /// An inclusive integer-range sum whose checked iterand returns exactly
    /// `Z` belongs to the exact `Z` carrier.
    IntegerRangeSumMembership,
    NaturalMembershipClosure(NaturalMembershipClosureBuiltinRule),
    PositiveNaturalMembershipClosure(PositiveNaturalMembershipClosureBuiltinRule),
    RationalMembershipClosure(RationalMembershipClosureBuiltinRule),
    ComplexArithmeticMembershipClosure(ComplexArithmeticMembershipClosureBuiltinRule),
    RealArithmeticMembershipClosure(RealArithmeticMembershipClosureBuiltinRule),
    NativeConstantMembership(NativeConstantMembershipBuiltinRule),
    /// One checked equality with reversed operands proves the target equality.
    EqualitySymmetry,
    NotEqualSymmetry,
    /// Two checked real-carrier premises followed by one strict comparison
    /// between the target operands prove their inequality.
    NotEqualFromStrictOrder,
    SetRelationDuality(SetRelationDualityBuiltinRule),
    Set(SetBuiltinRule),
    FiniteSet(FiniteSetBuiltinRule),
    ListSetMembership(ListSetMembershipBuiltinRuleEvidence),
    TupleLiteralShape,
    AbsoluteValue(AbsoluteValueBuiltinRule),
    Extrema(ExtremaBuiltinRule),
    Aggregate(AggregateBuiltinRule),
    Nonzero(NonzeroBuiltinRule),
    PrimeU64Reflection,
    CoprimeNaturalReflection,
    /// Membership in one standard numeric set is projected through Litex's
    /// centralized standard-set hierarchy. The enclosing result has exactly
    /// one child: the checked source membership fact.
    StandardSetMembershipProjection,
    /// One fixed inclusion in Litex's standard numeric-set hierarchy. The
    /// target subset fact itself retains the exact source and target sets.
    StandardSetSubset,
    /// A literal finite-set inclusion whose ordered subgoals prove membership
    /// of every literal item in the retained target set.
    LiteralSetSubset,
}

impl BuiltinRuleEvidence {
    /// Stable verifier-owned identity for every builtin proof certificate.
    /// Diagnostics are presentation only and never select compiler behavior.
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::Uncatalogued(rule) => rule.rule_id(),
            Self::DefinitionProjection(_) => "definition.projection",
            Self::SetBuilderMembership(_) => "set.set_builder_membership",
            Self::FunctionSetMembership(_) => "function.set_membership",
            Self::FunctionApplicationInRange(_) => "function.application_in_range",
            Self::FunctionRangeSubset(_) => "function.range_subset",
            Self::RealIntervalSubsetReal(_) => "set.real_interval_subset_real",
            Self::TupleCartesianMembership(_) => "tuple.cartesian_membership",
            Self::IntegerRangeSumPointwiseOrder(_) => "aggregate.integer_range_sum_pointwise_order",
            Self::RefinedNumericMembership(_) => "numeric.refined_membership",
            Self::ClosedNumericMembership(_) => "numeric.closed_membership",
            Self::ClosedNumericNonmembership(_) => "numeric.closed_nonmembership",
            Self::ClosedNumericComparison(_) => "numeric.closed_comparison",
            Self::OrderReflexivity(_) => "order.reflexivity",
            Self::RuntimeResolvedNumericComparison(_) => {
                "order.runtime_resolved_numeric_comparison"
            }
            Self::RegisteredReflexivePredicate(_) => "predicate.registered_reflexive",
            Self::RegisteredSymmetricPredicate(_) => "predicate.registered_symmetric",
            Self::RegisteredAntisymmetricPredicate(_) => "predicate.registered_antisymmetric",
            Self::ObjectReflexivity(_) => "equality.object_reflexivity",
            Self::RationalNormalization(_) => "equality.rational_normalization",
            Self::RationalAlgebraicNormalization(_) => "equality.rational_algebraic_normalization",
            Self::ComplexAlgebraicNormalization(_) => "equality.complex_algebraic_normalization",
            Self::StructuralDefinitionCongruence(_) => "equality.structural_definition_congruence",
            Self::StructuralKnownEqualityCongruence(_) => {
                "equality.structural_known_equality_congruence"
            }
            Self::IntegralPolynomialNormalization(_) => {
                "equality.integral_polynomial_normalization"
            }
            Self::StandardSetNonempty(_) => "set.standard_nonempty",
            Self::LiteralSetNonempty => "set.literal_nonempty",
            Self::SetBuilderSubsetBase => "set.set_builder_subset_base",
            Self::SetBuilderInPowerSetViaParamSubset => {
                "set.set_builder_in_power_set_via_param_subset"
            }
            Self::DisjunctionIntroduction(_) => "logic.disjunction_introduction",
            Self::FunctionApplicationReturnMembership(_) => {
                "function.application_return_membership"
            }
            Self::MatrixExpressionMembership(_) => "matrix.expression_membership",
            Self::KnownEqualityPath(_) => "equality.known_path",
            Self::DivNotEqualZero(evidence) => evidence.rule_id(),
            Self::Arithmetic(rule) => rule.rule_id(),
            Self::IntegerMembershipClosure(rule) => rule.rule_id(),
            Self::IntegerRangeSumMembership => "aggregate.integer_range_sum_membership",
            Self::NaturalMembershipClosure(rule) => rule.rule_id(),
            Self::PositiveNaturalMembershipClosure(rule) => rule.rule_id(),
            Self::RationalMembershipClosure(rule) => rule.rule_id(),
            Self::ComplexArithmeticMembershipClosure(rule) => rule.rule_id(),
            Self::RealArithmeticMembershipClosure(rule) => rule.rule_id(),
            Self::NativeConstantMembership(rule) => rule.rule_id(),
            Self::EqualitySymmetry => "equality.symmetry",
            Self::NotEqualSymmetry => "not_equal.symmetry",
            Self::NotEqualFromStrictOrder => "not_equal.from_strict_order",
            Self::SetRelationDuality(rule) => rule.rule_id(),
            Self::Set(rule) => rule.rule_id(),
            Self::FiniteSet(rule) => rule.rule_id(),
            Self::ListSetMembership(_) => "set.literal_membership",
            Self::TupleLiteralShape => "tuple.literal_shape",
            Self::AbsoluteValue(rule) => rule.rule_id(),
            Self::Extrema(rule) => rule.rule_id(),
            Self::Aggregate(rule) => rule.rule_id(),
            Self::Nonzero(rule) => rule.rule_id(),
            Self::PrimeU64Reflection => "number_theory.prime_u64_reflection",
            Self::CoprimeNaturalReflection => "number_theory.coprime_natural_reflection",
            Self::StandardSetMembershipProjection => "numeric.standard_set_membership_projection",
            Self::StandardSetSubset => "numeric.standard_set_subset",
            Self::LiteralSetSubset => "set.literal_subset",
        }
    }
}

impl fmt::Debug for BuiltinRuleEvidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            BuiltinRuleEvidence::Uncatalogued(rule) => {
                f.debug_tuple("Uncatalogued").field(rule).finish()
            }
            BuiltinRuleEvidence::DefinitionProjection(evidence) => f
                .debug_tuple("DefinitionProjection")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::SetBuilderMembership(evidence) => f
                .debug_tuple("SetBuilderMembership")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::FunctionSetMembership(evidence) => f
                .debug_tuple("FunctionSetMembership")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::FunctionApplicationInRange(evidence) => f
                .debug_tuple("FunctionApplicationInRange")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::FunctionRangeSubset(evidence) => f
                .debug_tuple("FunctionRangeSubset")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::RealIntervalSubsetReal(evidence) => f
                .debug_tuple("RealIntervalSubsetReal")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::TupleCartesianMembership(evidence) => f
                .debug_tuple("TupleCartesianMembership")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::IntegerRangeSumPointwiseOrder(evidence) => f
                .debug_tuple("IntegerRangeSumPointwiseOrder")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::RefinedNumericMembership(evidence) => f
                .debug_tuple("RefinedNumericMembership")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::ClosedNumericMembership(evidence) => f
                .debug_tuple("ClosedNumericMembership")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::ClosedNumericNonmembership(evidence) => f
                .debug_tuple("ClosedNumericNonmembership")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::ClosedNumericComparison(evidence) => f
                .debug_tuple("ClosedNumericComparison")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::OrderReflexivity(evidence) => {
                f.debug_tuple("OrderReflexivity").field(evidence).finish()
            }
            BuiltinRuleEvidence::RuntimeResolvedNumericComparison(evidence) => f
                .debug_tuple("RuntimeResolvedNumericComparison")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::RegisteredReflexivePredicate(evidence) => f
                .debug_tuple("RegisteredReflexivePredicate")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::RegisteredSymmetricPredicate(evidence) => f
                .debug_tuple("RegisteredSymmetricPredicate")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::RegisteredAntisymmetricPredicate(evidence) => f
                .debug_tuple("RegisteredAntisymmetricPredicate")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::ObjectReflexivity(evidence) => {
                f.debug_tuple("ObjectReflexivity").field(evidence).finish()
            }
            BuiltinRuleEvidence::RationalNormalization(evidence) => f
                .debug_tuple("RationalNormalization")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::RationalAlgebraicNormalization(evidence) => f
                .debug_tuple("RationalAlgebraicNormalization")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::ComplexAlgebraicNormalization(evidence) => f
                .debug_tuple("ComplexAlgebraicNormalization")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::StructuralDefinitionCongruence(evidence) => f
                .debug_tuple("StructuralDefinitionCongruence")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::StructuralKnownEqualityCongruence(evidence) => f
                .debug_tuple("StructuralKnownEqualityCongruence")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::IntegralPolynomialNormalization(evidence) => f
                .debug_tuple("IntegralPolynomialNormalization")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::StandardSetNonempty(evidence) => f
                .debug_tuple("StandardSetNonempty")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::LiteralSetNonempty => f.write_str("LiteralSetNonempty"),
            BuiltinRuleEvidence::SetBuilderSubsetBase => f.write_str("SetBuilderSubsetBase"),
            BuiltinRuleEvidence::SetBuilderInPowerSetViaParamSubset => {
                f.write_str("SetBuilderInPowerSetViaParamSubset")
            }
            BuiltinRuleEvidence::DisjunctionIntroduction(evidence) => f
                .debug_tuple("DisjunctionIntroduction")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::FunctionApplicationReturnMembership(evidence) => f
                .debug_tuple("FunctionApplicationReturnMembership")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::MatrixExpressionMembership(evidence) => f
                .debug_tuple("MatrixExpressionMembership")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::KnownEqualityPath(evidence) => {
                f.debug_tuple("KnownEqualityPath").field(evidence).finish()
            }
            BuiltinRuleEvidence::DivNotEqualZero(evidence) => {
                f.debug_tuple("DivNotEqualZero").field(evidence).finish()
            }
            BuiltinRuleEvidence::Arithmetic(rule) => {
                f.debug_tuple("Arithmetic").field(rule).finish()
            }
            BuiltinRuleEvidence::IntegerMembershipClosure(rule) => f
                .debug_tuple("IntegerMembershipClosure")
                .field(rule)
                .finish(),
            BuiltinRuleEvidence::IntegerRangeSumMembership => {
                f.write_str("IntegerRangeSumMembership")
            }
            BuiltinRuleEvidence::NaturalMembershipClosure(rule) => f
                .debug_tuple("NaturalMembershipClosure")
                .field(rule)
                .finish(),
            BuiltinRuleEvidence::PositiveNaturalMembershipClosure(rule) => f
                .debug_tuple("PositiveNaturalMembershipClosure")
                .field(rule)
                .finish(),
            BuiltinRuleEvidence::RationalMembershipClosure(rule) => f
                .debug_tuple("RationalMembershipClosure")
                .field(rule)
                .finish(),
            BuiltinRuleEvidence::ComplexArithmeticMembershipClosure(rule) => f
                .debug_tuple("ComplexArithmeticMembershipClosure")
                .field(rule)
                .finish(),
            BuiltinRuleEvidence::RealArithmeticMembershipClosure(rule) => f
                .debug_tuple("RealArithmeticMembershipClosure")
                .field(rule)
                .finish(),
            BuiltinRuleEvidence::NativeConstantMembership(rule) => f
                .debug_tuple("NativeConstantMembership")
                .field(rule)
                .finish(),
            BuiltinRuleEvidence::EqualitySymmetry => f.write_str("EqualitySymmetry"),
            BuiltinRuleEvidence::NotEqualSymmetry => f.write_str("NotEqualSymmetry"),
            BuiltinRuleEvidence::NotEqualFromStrictOrder => f.write_str("NotEqualFromStrictOrder"),
            BuiltinRuleEvidence::SetRelationDuality(rule) => {
                f.debug_tuple("SetRelationDuality").field(rule).finish()
            }
            BuiltinRuleEvidence::Set(rule) => f.debug_tuple("Set").field(rule).finish(),
            BuiltinRuleEvidence::FiniteSet(rule) => f.debug_tuple("FiniteSet").field(rule).finish(),
            BuiltinRuleEvidence::ListSetMembership(evidence) => {
                f.debug_tuple("ListSetMembership").field(evidence).finish()
            }
            BuiltinRuleEvidence::TupleLiteralShape => f.write_str("TupleLiteralShape"),
            BuiltinRuleEvidence::AbsoluteValue(rule) => {
                f.debug_tuple("AbsoluteValue").field(rule).finish()
            }
            BuiltinRuleEvidence::Extrema(rule) => f.debug_tuple("Extrema").field(rule).finish(),
            BuiltinRuleEvidence::Aggregate(rule) => f.debug_tuple("Aggregate").field(rule).finish(),
            BuiltinRuleEvidence::Nonzero(rule) => f.debug_tuple("Nonzero").field(rule).finish(),
            BuiltinRuleEvidence::PrimeU64Reflection => f.write_str("PrimeU64Reflection"),
            BuiltinRuleEvidence::CoprimeNaturalReflection => {
                f.write_str("CoprimeNaturalReflection")
            }
            BuiltinRuleEvidence::StandardSetMembershipProjection => {
                f.write_str("StandardSetMembershipProjection")
            }
            BuiltinRuleEvidence::StandardSetSubset => f.write_str("StandardSetSubset"),
            BuiltinRuleEvidence::LiteralSetSubset => f.write_str("LiteralSetSubset"),
        }
    }
}
