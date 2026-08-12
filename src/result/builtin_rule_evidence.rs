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
/// defining facts in source order.
#[derive(Clone)]
pub struct SetBuilderMembershipBuiltinRuleEvidence {
    pub set_builder: SetBuilder,
    pub expected_target: Fact,
    pub expected_premises: Vec<Fact>,
}

/// Exact extensional certificate for membership in a Litex function space.
/// The enclosing result has exactly one child: the checked pointwise `forall`
/// proposition retained in `expected_pointwise`.
#[derive(Clone)]
pub struct FunctionSetMembershipBuiltinRuleEvidence {
    pub element: Obj,
    pub function_set: FnSet,
    pub expected_target: Fact,
    pub expected_pointwise: Fact,
}

/// Exact constructor certificate for a refined standard numeric set. Children
/// are ordered as the native base-carrier membership followed by the defining
/// sign/nonzero predicate.
#[derive(Clone)]
pub struct RefinedNumericMembershipBuiltinRuleEvidence {
    pub target_set: StandardSet,
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
/// child proves that the application head belongs to `function_set`.
#[derive(Clone)]
pub struct FunctionApplicationReturnMembershipBuiltinRuleEvidence {
    pub source_application: Obj,
    pub function_set: FnSet,
    pub typed_return_set: Obj,
    pub expected_target: Fact,
    pub expected_head_membership: Fact,
}

impl fmt::Debug for FunctionApplicationReturnMembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("FunctionApplicationReturnMembershipBuiltinRuleEvidence")
            .field("source_application", &self.source_application.to_string())
            .field("function_set", &self.function_set.to_string())
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
    pub fn new(
        target_set: StandardSet,
        expected_target: Fact,
        expected_premises: Vec<Fact>,
    ) -> Self {
        Self {
            target_set,
            expected_target,
            expected_premises,
        }
    }
}

impl fmt::Debug for RefinedNumericMembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("RefinedNumericMembershipBuiltinRuleEvidence")
            .field("target_set", &self.target_set.to_string())
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
    pub fn new(
        element: Obj,
        function_set: FnSet,
        expected_target: Fact,
        expected_pointwise: Fact,
    ) -> Self {
        Self {
            element,
            function_set,
            expected_target,
            expected_pointwise,
        }
    }
}

impl fmt::Debug for FunctionSetMembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("FunctionSetMembershipBuiltinRuleEvidence")
            .field("element", &self.element.to_string())
            .field("function_set", &self.function_set.to_string())
            .field("expected_target", &self.expected_target.to_string())
            .field("expected_pointwise", &self.expected_pointwise.to_string())
            .finish()
    }
}

impl SetBuilderMembershipBuiltinRuleEvidence {
    pub fn new(
        set_builder: SetBuilder,
        expected_target: Fact,
        expected_premises: Vec<Fact>,
    ) -> Self {
        Self {
            set_builder,
            expected_target,
            expected_premises,
        }
    }
}

impl fmt::Debug for SetBuilderMembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("SetBuilderMembershipBuiltinRuleEvidence")
            .field("set_builder", &self.set_builder.to_string())
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
    DivNotEqualZero(DivNotEqualZeroBuiltinRuleEvidence),
    Arithmetic(ArithmeticBuiltinRule),
    IntegerMembershipClosure(IntegerMembershipClosureBuiltinRule),
    NotEqualSymmetry,
    /// Two checked real-carrier premises followed by one strict comparison
    /// between the target operands prove their inequality.
    NotEqualFromStrictOrder,
    SetRelationDuality(SetRelationDualityBuiltinRule),
    Set(SetBuiltinRule),
    AbsoluteValue(AbsoluteValueBuiltinRule),
    PrimeU64Reflection,
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
            BuiltinRuleEvidence::StandardSetMembershipProjection => {
                f.write_str("StandardSetMembershipProjection")
            }
        }
    }
}
