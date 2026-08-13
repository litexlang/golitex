use crate::prelude::*;
use crate::verify::rule_schema::{RuleFingerprint, RuleId};
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NonzeroExpressionOrientation {
    ExpressionOnLeft,
    ExpressionOnRight,
}

#[derive(Clone)]
pub struct DivNotEqualZeroBuiltinRuleEvidence {
    pub numerator: Obj,
    pub denominator: Obj,
    pub orientation: NonzeroExpressionOrientation,
}

impl DivNotEqualZeroBuiltinRuleEvidence {
    pub fn new(
        numerator: Obj,
        denominator: Obj,
        orientation: NonzeroExpressionOrientation,
    ) -> Self {
        Self {
            numerator,
            denominator,
            orientation,
        }
    }
}

impl fmt::Debug for DivNotEqualZeroBuiltinRuleEvidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("DivNotEqualZeroBuiltinRuleEvidence")
            .field("numerator", &self.numerator.to_string())
            .field("denominator", &self.denominator.to_string())
            .field("orientation", &self.orientation)
            .finish()
    }
}

/// Stable identities for arithmetic/order rules whose complete certificate is
/// the target fact plus the recursively checked ordered premise list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArithmeticBuiltinRule {
    LessEqualFromStrictOrder,
    GreaterEqualFromStrictOrder,
    SubNonnegativeFromLessEqual,
    SubPositiveFromLess,
    AddNonnegative,
    AddPositive,
    AddPositiveLeftStrict,
    AddPositiveRightStrict,
    MulNonnegative,
    MulPositive,
    DivNonnegative,
    DivPositive,
    AddCommonLeftLessEqual,
    SubRightNonnegativeLessEqual,
    AddRightNonnegativeLessEqual,
    AddComponentwiseLessEqual,
    AddCommonLeftLess,
    AddComponentwiseLess,
    AddComponentwiseLessLessEqual,
    AddComponentwiseLessEqualLess,
}

/// Stable identities for closure of the integer carrier under binary
/// arithmetic. The enclosing result contains the checked left- and
/// right-operand memberships in that exact order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntegerMembershipClosureBuiltinRule {
    Add,
    Sub,
    Mul,
    Mod,
}

/// Stable identities for closure of the complex carrier under the migrated
/// proof-carrying binary arithmetic constructors.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ComplexArithmeticMembershipClosureBuiltinRule {
    Add,
    Sub,
    Mul,
}

/// Stable identities for closure of the real carrier under arithmetic. The
/// enclosing result retains the checked operand memberships in source order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RealArithmeticMembershipClosureBuiltinRule {
    Add,
    Sub,
    Mul,
    Div,
    Pow,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SetRelationDualityBuiltinRule {
    SubsetFromSuperset,
    SupersetFromSubset,
    NotSubsetFromNotSuperset,
    NotSupersetFromNotSubset,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SetBuiltinRule {
    UnionCommutative,
    UnionAssociative,
    UnionIdempotent,
    UnionEmptyIdentity,
    IntersectCommutative,
    IntersectAssociative,
    UnionMembershipLeft,
    UnionMembershipRight,
    IntersectMembershipBoth,
    IntersectNonMembershipLeft,
    IntersectNonMembershipRight,
    SetMinusMembership,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AbsoluteValueBuiltinRule {
    NonnegativeIdentity,
    NonpositiveNegation,
    Product,
    PositiveFromNonzero,
}

/// Generic certificate payload for a paired, registry-owned local builtin.
/// Child results are stored in the enclosing result in this exact order:
/// parameter requirements first, followed by semantic premises.
#[derive(Clone)]
pub struct RegisteredLocalBuiltinRuleEvidence {
    pub rule_id: RuleId,
    pub semantic_fingerprint: RuleFingerprint,
    pub bindings: Vec<Obj>,
    pub parameter_requirement_count: usize,
}

impl fmt::Debug for RegisteredLocalBuiltinRuleEvidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("RegisteredLocalBuiltinRuleEvidence")
            .field("rule_id", &self.rule_id)
            .field("semantic_fingerprint", &self.semantic_fingerprint)
            .field("binding_count", &self.bindings.len())
            .field(
                "parameter_requirement_count",
                &self.parameter_requirement_count,
            )
            .finish()
    }
}

/// Checked definition-elimination certificate for an existential hidden
/// behind one concrete proposition call. The enclosing result is the
/// instantiated existential and has exactly one child: a proof of `source`.
#[derive(Clone)]
pub struct DefinitionProjectionBuiltinRuleEvidence {
    pub fact: NormalAtomicFact,
    pub definition: DefPropStmt,
}

/// Exact constructor certificate for membership in a literal set builder.
/// Child results are ordered as base membership followed by the instantiated
/// defining facts in source order. The builder is recovered from
/// `expected_target`.
#[derive(Clone)]
pub struct SetBuilderMembershipBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub expected_premises: Vec<Fact>,
}

/// Exact extensional certificate for membership in a Litex function space.
/// The enclosing result has exactly one child: the checked pointwise `forall`
/// proposition retained in `expected_pointwise`. The element and function
/// space are recovered from `expected_target`.
#[derive(Clone)]
pub struct FunctionSetMembershipBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub expected_pointwise: Fact,
}

/// Exact constructor certificate for a refined standard numeric set. Children
/// are ordered as the native base-carrier membership followed by the defining
/// sign/nonzero predicate. The numeric set is recovered from `expected_target`.
#[derive(Clone)]
pub struct RefinedNumericMembershipBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub expected_premises: Vec<Fact>,
}

/// A closed literal numeric comparison checked by the verifier's evaluator.
/// The Lean carrier remains contextual (for example `0 < 1` may be needed in
/// an `ℝ` proof), so the certificate freezes the proposition without choosing a
/// different source-level numeric set.
#[derive(Clone)]
pub struct ClosedNumericComparisonBuiltinRuleEvidence {
    pub expected_target: Fact,
}

/// Exact dependent-elimination certificate for membership of a checked
/// function application in its instantiated declared return set. The sole
/// child proves that the application head belongs to the function space frozen
/// in `expected_head_membership`.
#[derive(Clone)]
pub struct FunctionApplicationReturnMembershipBuiltinRuleEvidence {
    pub typed_return_set: Obj,
    pub expected_target: Fact,
    pub expected_head_membership: Fact,
}

/// Exact direct-equality path selected while checking one equality-class
/// result. Every step cites the environment-stored fact that justified it.
#[derive(Clone)]
pub struct KnownEqualityBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub steps: Vec<KnownEqualityBuiltinRuleStep>,
}

impl KnownEqualityBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, steps: Vec<KnownEqualityBuiltinRuleStep>) -> Self {
        Self {
            expected_target,
            steps,
        }
    }
}

impl fmt::Debug for KnownEqualityBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("KnownEqualityBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("steps", &self.steps)
            .finish()
    }
}

#[derive(Clone)]
pub struct KnownEqualityBuiltinRuleStep {
    pub from: Obj,
    pub to: Obj,
    pub equality: EqualFact,
    pub source_fact_id: FactId,
}

impl KnownEqualityBuiltinRuleStep {
    pub fn new(from: Obj, to: Obj, equality: EqualFact, source_fact_id: FactId) -> Self {
        Self {
            from,
            to,
            equality,
            source_fact_id,
        }
    }
}

impl fmt::Debug for KnownEqualityBuiltinRuleStep {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("KnownEqualityBuiltinRuleStep")
            .field("from", &self.from.to_string())
            .field("to", &self.to.to_string())
            .field("equality", &self.equality.to_string())
            .field("source_fact_id", &self.source_fact_id)
            .finish()
    }
}

impl FunctionApplicationReturnMembershipBuiltinRuleEvidence {
    pub fn new(
        typed_return_set: Obj,
        expected_target: Fact,
        expected_head_membership: Fact,
    ) -> Self {
        Self {
            typed_return_set,
            expected_target,
            expected_head_membership,
        }
    }
}

impl fmt::Debug for FunctionApplicationReturnMembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("FunctionApplicationReturnMembershipBuiltinRuleEvidence")
            .field("typed_return_set", &self.typed_return_set.to_string())
            .field("expected_target", &self.expected_target.to_string())
            .field(
                "expected_head_membership",
                &self.expected_head_membership.to_string(),
            )
            .finish()
    }
}

impl ClosedNumericComparisonBuiltinRuleEvidence {
    pub fn new(expected_target: Fact) -> Self {
        Self { expected_target }
    }
}

impl fmt::Debug for ClosedNumericComparisonBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("ClosedNumericComparisonBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .finish()
    }
}

impl RefinedNumericMembershipBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, expected_premises: Vec<Fact>) -> Self {
        Self {
            expected_target,
            expected_premises,
        }
    }
}

impl fmt::Debug for RefinedNumericMembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("RefinedNumericMembershipBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field(
                "expected_premises",
                &self
                    .expected_premises
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}

impl FunctionSetMembershipBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, expected_pointwise: Fact) -> Self {
        Self {
            expected_target,
            expected_pointwise,
        }
    }
}

impl fmt::Debug for FunctionSetMembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("FunctionSetMembershipBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("expected_pointwise", &self.expected_pointwise.to_string())
            .finish()
    }
}

impl SetBuilderMembershipBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, expected_premises: Vec<Fact>) -> Self {
        Self {
            expected_target,
            expected_premises,
        }
    }
}

impl fmt::Debug for SetBuilderMembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("SetBuilderMembershipBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field(
                "expected_premises",
                &self
                    .expected_premises
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}

impl DefinitionProjectionBuiltinRuleEvidence {
    pub fn new(fact: NormalAtomicFact, definition: DefPropStmt) -> Self {
        Self { fact, definition }
    }
}

impl fmt::Debug for DefinitionProjectionBuiltinRuleEvidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("DefinitionProjectionBuiltinRuleEvidence")
            .field("source", &self.fact.to_string())
            .field("definition", &self.definition.name)
            .finish()
    }
}

#[derive(Clone)]
pub enum BuiltinRuleEvidence {
    RegisteredLocal(RegisteredLocalBuiltinRuleEvidence),
    DefinitionProjection(DefinitionProjectionBuiltinRuleEvidence),
    SetBuilderMembership(SetBuilderMembershipBuiltinRuleEvidence),
    FunctionSetMembership(FunctionSetMembershipBuiltinRuleEvidence),
    RefinedNumericMembership(RefinedNumericMembershipBuiltinRuleEvidence),
    ClosedNumericComparison(ClosedNumericComparisonBuiltinRuleEvidence),
    FunctionApplicationReturnMembership(FunctionApplicationReturnMembershipBuiltinRuleEvidence),
    KnownEqualityPath(KnownEqualityBuiltinRuleEvidence),
    DivNotEqualZero(DivNotEqualZeroBuiltinRuleEvidence),
    Arithmetic(ArithmeticBuiltinRule),
    IntegerMembershipClosure(IntegerMembershipClosureBuiltinRule),
    ComplexArithmeticMembershipClosure(ComplexArithmeticMembershipClosureBuiltinRule),
    RealArithmeticMembershipClosure(RealArithmeticMembershipClosureBuiltinRule),
    NotEqualSymmetry,
    /// Two checked real-carrier premises followed by one strict comparison
    /// between the target operands prove their inequality.
    NotEqualFromStrictOrder,
    SetRelationDuality(SetRelationDualityBuiltinRule),
    Set(SetBuiltinRule),
    AbsoluteValue(AbsoluteValueBuiltinRule),
    PrimeU64Reflection,
    CoprimeNaturalReflection,
    /// Membership in one standard numeric set is projected through Litex's
    /// centralized standard-set hierarchy. The enclosing result has exactly
    /// one child: the checked source membership fact.
    StandardSetMembershipProjection,
}

impl fmt::Debug for BuiltinRuleEvidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            BuiltinRuleEvidence::RegisteredLocal(evidence) => {
                f.debug_tuple("RegisteredLocal").field(evidence).finish()
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
            BuiltinRuleEvidence::RefinedNumericMembership(evidence) => f
                .debug_tuple("RefinedNumericMembership")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::ClosedNumericComparison(evidence) => f
                .debug_tuple("ClosedNumericComparison")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::FunctionApplicationReturnMembership(evidence) => f
                .debug_tuple("FunctionApplicationReturnMembership")
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
            BuiltinRuleEvidence::ComplexArithmeticMembershipClosure(rule) => f
                .debug_tuple("ComplexArithmeticMembershipClosure")
                .field(rule)
                .finish(),
            BuiltinRuleEvidence::RealArithmeticMembershipClosure(rule) => f
                .debug_tuple("RealArithmeticMembershipClosure")
                .field(rule)
                .finish(),
            BuiltinRuleEvidence::NotEqualSymmetry => f.write_str("NotEqualSymmetry"),
            BuiltinRuleEvidence::NotEqualFromStrictOrder => f.write_str("NotEqualFromStrictOrder"),
            BuiltinRuleEvidence::SetRelationDuality(rule) => {
                f.debug_tuple("SetRelationDuality").field(rule).finish()
            }
            BuiltinRuleEvidence::Set(rule) => f.debug_tuple("Set").field(rule).finish(),
            BuiltinRuleEvidence::AbsoluteValue(rule) => {
                f.debug_tuple("AbsoluteValue").field(rule).finish()
            }
            BuiltinRuleEvidence::PrimeU64Reflection => f.write_str("PrimeU64Reflection"),
            BuiltinRuleEvidence::CoprimeNaturalReflection => {
                f.write_str("CoprimeNaturalReflection")
            }
            BuiltinRuleEvidence::StandardSetMembershipProjection => {
                f.write_str("StandardSetMembershipProjection")
            }
        }
    }
}
