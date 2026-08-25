//! Typed evidence emitted by builtin verification rules.

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

/// Exact introduction certificate for one selected branch of an `or` fact.
/// The enclosing result retains exactly one child proving
/// `expected_selected`; `selected_index` fixes its position in
/// `expected_target`.
#[derive(Clone)]
pub struct DisjunctionIntroductionBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub expected_selected: Fact,
    pub selected_index: usize,
}

impl DisjunctionIntroductionBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, expected_selected: Fact, selected_index: usize) -> Self {
        Self {
            expected_target,
            expected_selected,
            selected_index,
        }
    }
}

impl fmt::Debug for DisjunctionIntroductionBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("DisjunctionIntroductionBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("expected_selected", &self.expected_selected.to_string())
            .field("selected_index", &self.selected_index)
            .finish()
    }
}

/// A checked equality with one exact source position introduces membership in
/// a finite list-set literal. The enclosing result retains that equality as
/// its sole child; the index fixes the coproduct injection path.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ListSetMembershipBuiltinRuleEvidence {
    pub selected_index: usize,
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
    /// Ordered numeric transitivity. The enclosing result retains the
    /// verifier-owned carrier checks followed by the two ordered premises.
    OrderTransitivity,
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

/// Stable identities for closure of the natural carrier under binary
/// arithmetic. The enclosing result contains the checked left- and
/// right-operand memberships in that exact order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NaturalMembershipClosureBuiltinRule {
    Add,
    Mul,
}

/// Stable identities for closure of the rational carrier under binary
/// arithmetic. The enclosing result contains the checked left- and
/// right-operand memberships in that exact order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RationalMembershipClosureBuiltinRule {
    Add,
    Sub,
    Mul,
    Div,
    Pow,
}

/// Stable identities for closure of the complex carrier under the migrated
/// proof-carrying binary arithmetic constructors.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ComplexArithmeticMembershipClosureBuiltinRule {
    Add,
    Sub,
    Mul,
    Div,
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

/// Stable identities for primitive mathematical-constant memberships that
/// need no premises.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NativeConstantMembershipBuiltinRule {
    ImaginaryUnitInComplex,
    EulerNumberInReal,
    PiInReal,
    EulerNumberInPositiveReal,
    PiInPositiveReal,
    EulerNumberInComplex,
    PiInComplex,
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
    SubsetReflexivity,
    SupersetReflexivity,
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
pub enum FiniteSetBuiltinRule {
    ListSet,
    Range,
    ClosedRange,
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

/// A closed numeric expression was recursively evaluated and the resulting
/// number was checked against one standard numeric set.  The source expression
/// remains part of `expected_target`; `evaluation` records how it reached the
/// normalized value used by the membership decision.
#[derive(Clone)]
pub struct ClosedNumericMembershipBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub target_set: StandardSet,
    pub evaluation: SuccessEvaluateObjResult,
}

/// Zero-premise equality certificate whose two source objects are exactly the
/// same object after parser-owned binding identity is taken into account.
#[derive(Clone)]
pub struct ObjectReflexivityBuiltinRuleEvidence {
    pub expected_target: Fact,
}

/// Zero-premise equality certificate for two closed numeric expressions. Both
/// recursive evaluation trees are retained so a backend never has to infer
/// the normal form from a diagnostic label.
#[derive(Clone)]
pub struct RationalNormalizationBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub left_evaluation: SuccessEvaluateObjResult,
    pub right_evaluation: SuccessEvaluateObjResult,
}

/// Equality certificate selected only after exact bounded polynomial/rational
/// normalization with the relation `i * i = -1`. Every denominator or
/// negative-power base needed by that normalization is retained as an exact
/// nonzero premise; an empty list records a genuinely zero-premise identity.
#[derive(Clone)]
pub struct ComplexAlgebraicNormalizationBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub expected_nonzero_premises: Vec<Fact>,
}

/// A standard carrier is inhabited by its reviewed canonical witness. The
/// target is retained explicitly so consumers never recover this rule from a
/// diagnostic label.
#[derive(Clone)]
pub struct StandardSetNonemptyBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub target_set: StandardSet,
}

impl fmt::Debug for StandardSetNonemptyBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("StandardSetNonemptyBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("target_set", &self.target_set)
            .finish()
    }
}

/// The negative counterpart of `ClosedNumericMembershipBuiltinRuleEvidence`.
#[derive(Clone)]
pub struct ClosedNumericNonmembershipBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub target_set: StandardSet,
    pub evaluation: SuccessEvaluateObjResult,
}

/// A closed literal numeric comparison checked by the verifier's evaluator.
/// The Lean carrier remains contextual (for example `0 < 1` may be needed in
/// an `ℝ` proof), so the certificate freezes the proposition without choosing a
/// different source-level numeric set.
#[derive(Clone)]
pub struct ClosedNumericComparisonBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub left_evaluation: SuccessEvaluateObjResult,
    pub right_evaluation: SuccessEvaluateObjResult,
}

/// A weak order on one object, or the negation of a strict order on that same
/// object, discharged by reflexivity/irreflexivity rather than calculation.
///
/// Keeping this separate from `ClosedNumericComparisonBuiltinRuleEvidence`
/// matters for compositional consumers: `x <= x` is valid in a local binder
/// environment even though `x` is not a closed numeric expression.
#[derive(Clone)]
pub struct OrderReflexivityBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub repeated_object: Obj,
}

/// Compatibility evidence for a comparison decided only after `Runtime`
/// substituted known object values. The resolved operands are retained so the
/// execution Result says what was compared, but a standalone compiler must
/// reject this route until the substitutions themselves carry cited FactIds.
#[derive(Clone)]
pub struct RuntimeResolvedNumericComparisonBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub normalized_left: Obj,
    pub normalized_right: Obj,
}

/// Exact use of a previously proved and registered reflexivity theorem for a
/// user-defined binary predicate.
#[derive(Clone)]
pub struct RegisteredReflexivePredicateBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub predicate_name: String,
}

/// Exact use of a previously proved and registered permutation theorem for a
/// user-defined predicate. The enclosing builtin proof owns exactly one child
/// Result proving `expected_alternate`; `gather` records how the target's
/// arguments were reordered to obtain that premise.
#[derive(Clone)]
pub struct RegisteredSymmetricPredicateBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub predicate_name: String,
    pub gather: Vec<usize>,
    pub expected_alternate: Fact,
}

/// Exact use of a previously proved and registered antisymmetry theorem for a
/// user-defined binary predicate. The enclosing builtin proof owns the two
/// ordered predicate-premise child Results.
#[derive(Clone)]
pub struct RegisteredAntisymmetricPredicateBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub predicate_name: String,
}

/// Exact dependent-elimination certificate for membership of a checked
/// function application in its instantiated defined return set. The sole
/// child proves that the application head belongs to the function space frozen
/// in `expected_head_membership`.
#[derive(Clone)]
pub struct FunctionApplicationReturnMembershipBuiltinRuleEvidence {
    pub typed_return_set: Obj,
    pub expected_target: Fact,
    pub expected_head_membership: Fact,
}

/// Exact carrier certificate for a native matrix expression. The enclosing
/// fact's recursive well-definedness result owns the operand carrier and
/// dimension checks; this payload records the matrix type computed by that
/// checked constructor and the membership proposition it discharges.
#[derive(Clone)]
pub struct MatrixExpressionMembershipBuiltinRuleEvidence {
    pub inferred_matrix_set: MatrixSet,
    pub expected_target: Fact,
}

impl fmt::Debug for MatrixExpressionMembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("MatrixExpressionMembershipBuiltinRuleEvidence")
            .field(
                "inferred_matrix_set",
                &Obj::from(self.inferred_matrix_set.clone()).to_string(),
            )
            .field("expected_target", &self.expected_target.to_string())
            .finish()
    }
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
    pub fn new(
        expected_target: Fact,
        left_evaluation: SuccessEvaluateObjResult,
        right_evaluation: SuccessEvaluateObjResult,
    ) -> Self {
        Self {
            expected_target,
            left_evaluation,
            right_evaluation,
        }
    }
}

impl OrderReflexivityBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, repeated_object: Obj) -> Self {
        Self {
            expected_target,
            repeated_object,
        }
    }
}

impl RuntimeResolvedNumericComparisonBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, normalized_left: Obj, normalized_right: Obj) -> Self {
        Self {
            expected_target,
            normalized_left,
            normalized_right,
        }
    }
}

impl RegisteredReflexivePredicateBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, predicate_name: String) -> Self {
        Self {
            expected_target,
            predicate_name,
        }
    }
}

impl RegisteredSymmetricPredicateBuiltinRuleEvidence {
    pub fn new(
        expected_target: Fact,
        predicate_name: String,
        gather: Vec<usize>,
        expected_alternate: Fact,
    ) -> Self {
        Self {
            expected_target,
            predicate_name,
            gather,
            expected_alternate,
        }
    }
}

impl RegisteredAntisymmetricPredicateBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, predicate_name: String) -> Self {
        Self {
            expected_target,
            predicate_name,
        }
    }
}

impl ClosedNumericMembershipBuiltinRuleEvidence {
    pub fn new(
        expected_target: Fact,
        target_set: StandardSet,
        evaluation: SuccessEvaluateObjResult,
    ) -> Self {
        Self {
            expected_target,
            target_set,
            evaluation,
        }
    }
}

impl ObjectReflexivityBuiltinRuleEvidence {
    pub fn new(expected_target: Fact) -> Self {
        Self { expected_target }
    }
}

impl RationalNormalizationBuiltinRuleEvidence {
    pub fn new(
        expected_target: Fact,
        left_evaluation: SuccessEvaluateObjResult,
        right_evaluation: SuccessEvaluateObjResult,
    ) -> Self {
        Self {
            expected_target,
            left_evaluation,
            right_evaluation,
        }
    }
}

impl ComplexAlgebraicNormalizationBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, expected_nonzero_premises: Vec<Fact>) -> Self {
        Self {
            expected_target,
            expected_nonzero_premises,
        }
    }
}

impl fmt::Debug for ClosedNumericMembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("ClosedNumericMembershipBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("target_set", &self.target_set.to_string())
            .field("evaluation", &self.evaluation)
            .finish()
    }
}

impl fmt::Debug for ObjectReflexivityBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("ObjectReflexivityBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .finish()
    }
}

impl fmt::Debug for RationalNormalizationBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("RationalNormalizationBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("left_evaluation", &self.left_evaluation)
            .field("right_evaluation", &self.right_evaluation)
            .finish()
    }
}

impl fmt::Debug for ComplexAlgebraicNormalizationBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("ComplexAlgebraicNormalizationBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field(
                "expected_nonzero_premises",
                &self
                    .expected_nonzero_premises
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}

impl ClosedNumericNonmembershipBuiltinRuleEvidence {
    pub fn new(
        expected_target: Fact,
        target_set: StandardSet,
        evaluation: SuccessEvaluateObjResult,
    ) -> Self {
        Self {
            expected_target,
            target_set,
            evaluation,
        }
    }
}

impl fmt::Debug for ClosedNumericNonmembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("ClosedNumericNonmembershipBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("target_set", &self.target_set.to_string())
            .field("evaluation", &self.evaluation)
            .finish()
    }
}

impl fmt::Debug for ClosedNumericComparisonBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("ClosedNumericComparisonBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("left_evaluation", &self.left_evaluation)
            .field("right_evaluation", &self.right_evaluation)
            .finish()
    }
}

impl fmt::Debug for OrderReflexivityBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("OrderReflexivityBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("repeated_object", &self.repeated_object.to_string())
            .finish()
    }
}

impl fmt::Debug for RuntimeResolvedNumericComparisonBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("RuntimeResolvedNumericComparisonBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("normalized_left", &self.normalized_left.to_string())
            .field("normalized_right", &self.normalized_right.to_string())
            .finish()
    }
}

impl fmt::Debug for RegisteredReflexivePredicateBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("RegisteredReflexivePredicateBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("predicate_name", &self.predicate_name)
            .finish()
    }
}

impl fmt::Debug for RegisteredSymmetricPredicateBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("RegisteredSymmetricPredicateBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("predicate_name", &self.predicate_name)
            .field("gather", &self.gather)
            .field("expected_alternate", &self.expected_alternate.to_string())
            .finish()
    }
}

impl fmt::Debug for RegisteredAntisymmetricPredicateBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("RegisteredAntisymmetricPredicateBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("predicate_name", &self.predicate_name)
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
    ComplexAlgebraicNormalization(ComplexAlgebraicNormalizationBuiltinRuleEvidence),
    StandardSetNonempty(StandardSetNonemptyBuiltinRuleEvidence),
    DisjunctionIntroduction(DisjunctionIntroductionBuiltinRuleEvidence),
    FunctionApplicationReturnMembership(FunctionApplicationReturnMembershipBuiltinRuleEvidence),
    MatrixExpressionMembership(MatrixExpressionMembershipBuiltinRuleEvidence),
    KnownEqualityPath(KnownEqualityBuiltinRuleEvidence),
    DivNotEqualZero(DivNotEqualZeroBuiltinRuleEvidence),
    Arithmetic(ArithmeticBuiltinRule),
    IntegerMembershipClosure(IntegerMembershipClosureBuiltinRule),
    NaturalMembershipClosure(NaturalMembershipClosureBuiltinRule),
    RationalMembershipClosure(RationalMembershipClosureBuiltinRule),
    ComplexArithmeticMembershipClosure(ComplexArithmeticMembershipClosureBuiltinRule),
    RealArithmeticMembershipClosure(RealArithmeticMembershipClosureBuiltinRule),
    NativeConstantMembership(NativeConstantMembershipBuiltinRule),
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
    PrimeU64Reflection,
    CoprimeNaturalReflection,
    /// Membership in one standard numeric set is projected through Litex's
    /// centralized standard-set hierarchy. The enclosing result has exactly
    /// one child: the checked source membership fact.
    StandardSetMembershipProjection,
    /// One fixed inclusion in Litex's standard numeric-set hierarchy. The
    /// target subset fact itself retains the exact source and target sets.
    StandardSetSubset,
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
            BuiltinRuleEvidence::ComplexAlgebraicNormalization(evidence) => f
                .debug_tuple("ComplexAlgebraicNormalization")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::StandardSetNonempty(evidence) => f
                .debug_tuple("StandardSetNonempty")
                .field(evidence)
                .finish(),
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
            BuiltinRuleEvidence::NaturalMembershipClosure(rule) => f
                .debug_tuple("NaturalMembershipClosure")
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
            BuiltinRuleEvidence::PrimeU64Reflection => f.write_str("PrimeU64Reflection"),
            BuiltinRuleEvidence::CoprimeNaturalReflection => {
                f.write_str("CoprimeNaturalReflection")
            }
            BuiltinRuleEvidence::StandardSetMembershipProjection => {
                f.write_str("StandardSetMembershipProjection")
            }
            BuiltinRuleEvidence::StandardSetSubset => f.write_str("StandardSetSubset"),
        }
    }
}
