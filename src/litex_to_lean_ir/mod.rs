//! Checked, backend-facing evidence produced only by `Runtime::litex_to_lean_ir_mode`.
//!
//! This IR records the verifier route that succeeded. Lean emission consumes
//! these values and must not re-run Litex proof search or guess a proof from a
//! raw source statement.

use crate::common::fact_id::FactId;
use crate::fact::{AtomicFact, Fact};
use crate::obj::{Obj, SourceObjectOccurrenceId, StandardSet};
use crate::rational_expression::objs_equal_by_rational_expression_evaluation;
use crate::result::{
    WellDefinedBinderPremiseRole, WellDefinedBinderScopeId, WellDefinedFactId,
    WellDefinedFunctionContract, WellDefinedObjChildUse, WellDefinedObjId,
    WellDefinednessRequirementRole, WellDefinednessRootObjectProofUse,
    WellDefinednessSourceObjectUse, WellDefinednessTargetRequirementPhase,
};
use crate::symbol::SymbolId;
use std::fmt;

mod builtin_rule;
mod def_thm_stmt;
mod function;
mod object;
mod registered_rule;
mod statement;
mod well_definedness;

pub use builtin_rule::{
    LitexToLeanAbsoluteValueBuiltinRuleIr, LitexToLeanArithmeticBuiltinRuleIr,
    LitexToLeanBuiltinRuleIr, LitexToLeanComplexArithmeticMembershipClosureBuiltinRuleIr,
    LitexToLeanDivNotEqualZeroIr, LitexToLeanIntegerMembershipClosureBuiltinRuleIr,
    LitexToLeanNativeConstantMembershipBuiltinRuleIr, LitexToLeanNonzeroExpressionOrientationIr,
    LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr, LitexToLeanSetBuiltinRuleIr,
    LitexToLeanSetRelationDualityBuiltinRuleIr,
};
pub use def_thm_stmt::{LitexToLeanDefThmStmtIr, LitexToLeanDefThmStmtProofStepIr};
pub use function::{
    LitexToLeanFunctionApplicationIr, LitexToLeanFunctionParameterIr, LitexToLeanFunctionTypeIr,
};
pub use object::{
    LitexToLeanAggregateObjectIr, LitexToLeanAnonymousFunctionIr,
    LitexToLeanBuiltinObjectOperatorIr, LitexToLeanCollectionObjectIr, LitexToLeanConstantObjectIr,
    LitexToLeanObjectIr, LitexToLeanSetBuilderIr, LitexToLeanStandardSetIr,
};
pub use registered_rule::{LitexToLeanRegisteredRuleApplicationIr, LitexToLeanTypedBoundObjectIr};
pub use statement::*;
pub(crate) use well_definedness::validate_litex_to_lean_well_definedness_certificate;

#[derive(Clone, Debug)]
pub struct LitexToLeanStoredFunctionFactIr {
    pub fact_id: FactId,
    /// Kept separately from `expected_proposition` so malformed IR cannot
    /// silently retarget a stored environment effect.
    pub proposition: Fact,
    pub expected_proposition: Fact,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanStoredTupleFactIr {
    pub fact_id: FactId,
    pub proposition: Fact,
    pub role: LitexToLeanStoredTupleFactRoleIr,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LitexToLeanStoredTupleFactRoleIr {
    IsTuple,
    Dimension,
    Coordinate,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanExistentialWitnessIr {
    pub symbol_id: crate::symbol::SymbolId,
    pub name: String,
    /// Instantiated type after substituting any earlier witnesses.
    pub param_type: LitexToLeanParameterTypeIr,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LitexToLeanExistentialProjectionRoleIr {
    ParameterType { witness_index: usize },
    BodyFact { body_index: usize },
}

#[derive(Clone, Debug)]
pub struct LitexToLeanObjectChoiceIr {
    pub symbol_id: crate::symbol::SymbolId,
    pub name: String,
    pub carrier: LitexToLeanObjectIr,
    /// Checked proof of `litexIsNonemptySet carrier`; this proposition is the
    /// target ABI's existential witness package.
    pub nonempty_proof: LitexToLeanFactIr,
    /// Exact environment-stored `name ∈ carrier` fact and its stable identity.
    pub membership: LitexToLeanFactIr,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanObjectDefinitionIr {
    pub symbol_id: crate::symbol::SymbolId,
    pub name: String,
    pub param_type: LitexToLeanParameterTypeIr,
    pub value: LitexToLeanObjectIr,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanParameterGroupIr {
    pub symbol_ids: Vec<crate::symbol::SymbolId>,
    pub names: Vec<String>,
    pub param_type: LitexToLeanParameterTypeIr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LitexToLeanParameterTypeIr {
    /// A binder constrained by Litex's set predicate.
    Set,
    /// A binder plus the exact source membership proposition that constrains it.
    MemberOf {
        set: LitexToLeanObjectIr,
    },
    NonemptySet,
    FiniteSet,
    Unsupported(String),
}

#[derive(Clone, Debug, Default)]
pub struct LitexToLeanWellDefinednessCertificateIr {
    pub root_obj_ids: Vec<WellDefinedObjId>,
    pub root_proof_uses: Vec<WellDefinednessRootObjectProofUse>,
    pub source_object_uses: Vec<WellDefinednessSourceObjectUse>,
    pub facts: Vec<LitexToLeanWellDefinednessFactIr>,
    pub objects: Vec<LitexToLeanWellDefinednessObjectIr>,
    pub target_requirements: Vec<LitexToLeanWellDefinednessTargetRequirementIr>,
    pub parameter_facts: Vec<LitexToLeanWellDefinednessParameterFactIr>,
    pub binder_scopes: Vec<LitexToLeanWellDefinednessBinderScopeIr>,
}

#[derive(Clone)]
pub struct LitexToLeanWellDefinednessBinderScopeIr {
    pub scope_id: WellDefinedBinderScopeId,
    pub owner_object: Obj,
    pub ambient_scope_ids: Vec<WellDefinedBinderScopeId>,
    pub premises: Vec<LitexToLeanWellDefinednessBinderPremiseIr>,
    pub inferred_premises: Vec<LitexToLeanFactIr>,
}

impl fmt::Debug for LitexToLeanWellDefinednessBinderScopeIr {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("LitexToLeanWellDefinednessBinderScopeIr")
            .field("scope_id", &self.scope_id)
            .field("owner_object", &self.owner_object.to_string())
            .field("ambient_scope_ids", &self.ambient_scope_ids)
            .field("premises", &self.premises)
            .field("inferred_premises", &self.inferred_premises)
            .finish()
    }
}

#[derive(Clone, Debug)]
pub struct LitexToLeanWellDefinednessBinderPremiseIr {
    pub role: WellDefinedBinderPremiseRole,
    pub symbol_id: Option<SymbolId>,
    pub fact_id: FactId,
    pub proposition: Fact,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanWellDefinednessParameterFactIr {
    pub symbol_id: SymbolId,
    pub fact_id: FactId,
    pub proposition: Fact,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanWellDefinednessFactIr {
    pub well_defined_fact_id: WellDefinedFactId,
    /// Frozen separately from the recursive proof node so malformed IR cannot
    /// retarget a verifier certificate to another proposition.
    pub expected_proposition: Fact,
    pub fact: LitexToLeanFactIr,
    pub ambient_binder_scope_ids: Vec<WellDefinedBinderScopeId>,
}

#[derive(Clone)]
pub struct LitexToLeanWellDefinednessObjectIr {
    pub well_defined_obj_id: WellDefinedObjId,
    pub source_object: Obj,
    pub function_contracts: Vec<WellDefinedFunctionContract>,
    /// A source builtin may establish membership in this exact result set.
    /// This is a set object, never a Lean type or native carrier.
    pub intrinsic_result_set: Option<LitexToLeanObjectIr>,
    pub child_uses: Vec<WellDefinedObjChildUse>,
    pub well_defined_fact_ids: Vec<WellDefinedFactId>,
    pub target_requirements: Vec<LitexToLeanWellDefinednessObjectRequirementIr>,
    pub ambient_binder_scope_ids: Vec<WellDefinedBinderScopeId>,
    pub owned_binder_scope_id: Option<WellDefinedBinderScopeId>,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanWellDefinednessObjectRequirementIr {
    pub role: WellDefinednessRequirementRole,
    pub well_defined_fact_id: WellDefinedFactId,
    pub expected_proposition: Fact,
}

impl fmt::Debug for LitexToLeanWellDefinednessObjectIr {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("LitexToLeanWellDefinednessObjectIr")
            .field("well_defined_obj_id", &self.well_defined_obj_id)
            .field("source_object", &self.source_object.to_string())
            .field("function_contracts", &self.function_contracts)
            .field("intrinsic_result_set", &self.intrinsic_result_set)
            .field("child_uses", &self.child_uses)
            .field("well_defined_fact_ids", &self.well_defined_fact_ids)
            .field("target_requirements", &self.target_requirements)
            .field("ambient_binder_scope_ids", &self.ambient_binder_scope_ids)
            .field("owned_binder_scope_id", &self.owned_binder_scope_id)
            .finish()
    }
}

#[derive(Clone)]
pub struct LitexToLeanWellDefinednessTargetRequirementIr {
    pub source_occurrence_id: SourceObjectOccurrenceId,
    pub well_defined_obj_id: WellDefinedObjId,
    pub phase: WellDefinednessTargetRequirementPhase,
    pub role: WellDefinednessRequirementRole,
    pub well_defined_fact_id: WellDefinedFactId,
    pub expected_proposition: Fact,
}

impl fmt::Debug for LitexToLeanWellDefinednessTargetRequirementIr {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("LitexToLeanWellDefinednessTargetRequirementIr")
            .field("source_occurrence_id", &self.source_occurrence_id)
            .field("well_defined_obj_id", &self.well_defined_obj_id)
            .field("phase", &self.phase)
            .field("role", &self.role)
            .field("well_defined_fact_id", &self.well_defined_fact_id)
            .field(
                "expected_proposition",
                &self.expected_proposition.to_string(),
            )
            .finish()
    }
}

#[derive(Clone, Debug)]
pub struct LitexToLeanFactIr {
    /// `Some` exactly when this proof node corresponds to an environment-stored
    /// fact. Pure verification subgoals may be anonymous (`None`).
    pub fact_id: Option<FactId>,
    pub proposition: Fact,
    pub proof: LitexToLeanFactProofIr,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanLocalPremiseIr {
    pub fact_id: FactId,
    pub fact: Fact,
}

impl LitexToLeanLocalPremiseIr {
    pub fn new(fact_id: FactId, fact: Fact) -> Self {
        LitexToLeanLocalPremiseIr { fact_id, fact }
    }
}

#[derive(Clone, Debug)]
pub enum LitexToLeanFactProofIr {
    Trusted,
    KnownFactCitation {
        source_fact_id: FactId,
    },
    /// Citation of a positive existential whose binders were alpha-renamed by
    /// parsing or witness extraction.  Runtime lowering admits this node only
    /// after the verifier's canonical existential comparison succeeds.
    ExistentialAlphaRenameCitation {
        source_fact_id: FactId,
        source_proposition: Fact,
    },
    /// A goal derived by applying one explicit proof rule to recursively
    /// checked premise nodes. This is the extensible compiler-facing proof
    /// shape; adding a transport rule does not require another tree variant.
    RuleApplication {
        rule: LitexToLeanProofRuleIr,
        /// Verifier-side typing checks retained as evidence. Lean usually
        /// discharges these through elaboration rather than proof arguments.
        parameter_requirements: Vec<LitexToLeanFactIr>,
        premises: Vec<LitexToLeanFactIr>,
    },
    UserStrategy {
        name: String,
    },
    Composite {
        steps: Vec<LitexToLeanFactIr>,
    },
    ForallIntroduction {
        /// Temporary parameter-typing facts. Lean's typed binders discharge
        /// these, but the IR retains their Litex identities and provenance.
        parameter_premises: Vec<LitexToLeanLocalPremiseIr>,
        premises: Vec<LitexToLeanLocalPremiseIr>,
        /// Typed consequences derived while installing parameters and domain
        /// premises. These must be reconstructed inside the same proof scope.
        inferred_premises: Vec<LitexToLeanFactIr>,
        conclusions: Vec<LitexToLeanFactIr>,
    },
    /// A fact released by `have x T = value`. The declaration itself is a
    /// sibling statement-IR node. Membership/type facts replay the verifier's
    /// check for `value`; the defining equality reduces by reflexivity.
    ObjectDefinition {
        definition: String,
        value: LitexToLeanObjectIr,
        value_check: Option<Box<LitexToLeanFactIr>>,
    },
    /// Membership released by a sibling `LitexToLeanObjectChoiceIr`. The sibling
    /// carries the nonemptiness proof used by both `Exists.choose` and
    /// `Exists.choose_spec` during emission.
    ObjectChoice {
        definition: String,
        carrier: LitexToLeanObjectIr,
    },
    /// A type or body fact projected by a sibling existential-elimination
    /// statement.  The copied expected proposition makes malformed IR fail
    /// before a projection term is emitted.
    ExistentialElimination {
        source_proposition: Fact,
        role: LitexToLeanExistentialProjectionRoleIr,
        expected_proposition: Fact,
    },
    CaseSplit {
        coverage: Box<LitexToLeanFactIr>,
        branches: Vec<LitexToLeanCaseBranchIr>,
    },
    ByContradiction {
        reverse_assumption: LitexToLeanReverseAssumptionIr,
        block: LitexToLeanLocalProofBlockIr,
        contradiction: LitexToLeanContradictionIr,
    },
    Inference {
        source_fact_id: Option<FactId>,
        reason: String,
    },
    Memo {
        proof: Box<LitexToLeanFactProofIr>,
    },
    Unsupported {
        reason: String,
    },
}

#[derive(Clone, Debug)]
pub struct LitexToLeanCaseBranchIr {
    pub assumption: LitexToLeanLocalPremiseIr,
    pub block: LitexToLeanLocalProofBlockIr,
    pub exit: LitexToLeanCaseBranchExitIr,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LitexToLeanReverseAssumptionIntroductionIr {
    DirectNegation,
    ClassicalDoubleNegation,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanReverseAssumptionIr {
    pub premise: LitexToLeanLocalPremiseIr,
    pub introduction: LitexToLeanReverseAssumptionIntroductionIr,
}

#[derive(Clone, Debug)]
pub enum LitexToLeanCaseBranchExitIr {
    Conclusion(LitexToLeanFactIr),
    Contradiction(LitexToLeanContradictionIr),
}

#[derive(Clone, Debug)]
pub struct LitexToLeanContradictionIr {
    pub fact: Box<LitexToLeanFactIr>,
    pub negated_fact: Box<LitexToLeanFactIr>,
}

#[derive(Clone)]
pub enum LitexToLeanProofRuleIr {
    Builtin(LitexToLeanBuiltinRuleIr),
    RegisteredRule(LitexToLeanRegisteredRuleApplicationIr),
    ObjectReflexivity,
    TupleLiteralIsTuple {
        tuple: LitexToLeanObjectIr,
        expected_target: Fact,
    },
    TupleLiteralDimension {
        tuple: LitexToLeanObjectIr,
        expected_target: Fact,
    },
    ClosedRealMembership,
    ClosedStandardMembership,
    ClosedNumericReflection {
        target_set: LitexToLeanStandardSetIr,
    },
    RealSetNonempty,
    StandardSetNonempty,
    /// Litex's explicit verifier rule "Every object is a set."
    ObjectIsSet,
    /// Literal set-builder membership from the base membership and each
    /// instantiated defining fact, in source order.
    SetBuilderMembership {
        set_builder: LitexToLeanObjectIr,
        expected_target: Fact,
        expected_premises: Vec<Fact>,
    },
    /// Extensional function-space membership. The sole semantic premise is
    /// the verifier-checked pointwise `forall` in `expected_pointwise`.
    FunctionSetMembership {
        element: LitexToLeanObjectIr,
        function_set: LitexToLeanObjectIr,
        expected_target: Fact,
        expected_pointwise: Fact,
    },
    /// Membership in a refined standard numeric set, reconstructed from the
    /// native base carrier and its defining sign/nonzero predicate.
    RefinedNumericMembership {
        target_set: StandardSet,
        expected_target: Fact,
        expected_premises: Vec<Fact>,
    },
    ClosedNumericComparison {
        expected_target: Fact,
    },
    FunctionApplicationReturnMembership {
        source_application: LitexToLeanObjectIr,
        function_set: LitexToLeanObjectIr,
        typed_return_set: LitexToLeanObjectIr,
        expected_target: Fact,
        expected_head_membership: Fact,
    },
    EqualityRewrite(LitexToLeanEqualityRewriteIr),
    KnownEqualityPath(LitexToLeanKnownEqualityPathIr),
    IffRewrite {
        direction: LitexToLeanIffDirectionIr,
    },
    /// The verifier cited the same ordered relation through Litex's dual
    /// surface notation, for example `0 < b` while checking `b > 0`.
    ComparisonNotationDuality {
        expected_source: Fact,
        expected_target: Fact,
    },
    DefinitionReduction {
        definition: String,
        expected_parameter_requirements: Vec<Fact>,
        expected_clauses: Vec<Fact>,
    },
    /// Equality obtained by unfolding one verifier-selected named function
    /// whose defining equality was already stored. The exact source and
    /// reduction payload prevent the emitter from guessing from target syntax.
    CheckedFunctionDefinitionReplay {
        definition: LitexToLeanObjectIr,
        defining_equality_fact_id: FactId,
        defining_equality: Fact,
        expected_target: Fact,
        application_side: Obj,
        reduced: Obj,
        other_side: Obj,
        application_is_left: bool,
        reduced_matches_other_by_alpha: bool,
    },
    /// Checked unfolding of one concrete proposition definition. In the
    /// enclosing application, the sole premise proves `expected_source`, and
    /// unfolding `definition` must produce `expected_target`.
    DefinitionProjection {
        definition: String,
        expected_source: Fact,
        expected_target: Fact,
    },
    /// Checked folding of one concrete proposition definition. In the
    /// enclosing application, the sole premise proves `expected_source`, and
    /// folding `definition` must produce `expected_target`.
    DefinitionIntroduction {
        definition: String,
        expected_source: Fact,
        expected_target: Fact,
    },
    Normalization {
        kind: LitexToLeanNormalizationKindIr,
    },
    KnownForallInstantiation {
        source_fact_id: FactId,
        arguments: Vec<LitexToLeanKnownForallArgumentIr>,
    },
    ModusPonens,
    AndIntroduction,
    DisjunctionIntroduction {
        expected_target: Fact,
        expected_selected: Fact,
        selected_index: usize,
    },
    ConjunctionProjection {
        expected_source: Fact,
        expected_target: Fact,
        index: usize,
        count: usize,
    },
    ExistIntroduction {
        witnesses: Vec<Obj>,
        /// User proof statements executed in the temporary witness scope.
        /// Body verification may cite their retained FactIds.
        steps: Vec<LitexToLeanStatementIr>,
        /// Exact propositions associated with the two generic premise lists.
        /// Keeping these copies in the rule metadata makes malformed evidence
        /// fail before Lean source is emitted.
        expected_parameter_requirements: Vec<Fact>,
        expected_body_facts: Vec<Fact>,
    },
    ClassicalExcludedMiddle,
    CaseSplit,
    OtherUnsupported {
        name: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LitexToLeanNormalizationKindIr {
    RationalExpressionSimplification,
    IntegerExpressionSimplification,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LitexToLeanIffDirectionIr {
    Forward,
    Backward,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LitexToLeanEqualityRewriteDirectionIr {
    Forward,
    Backward,
}

/// Equality rewrite metadata. In its enclosing `RuleApplication`, premise 0
/// is the fact being transported and premise `n + 1` proves `steps[n]`.
#[derive(Clone, Debug)]
pub struct LitexToLeanEqualityRewriteIr {
    pub steps: Vec<LitexToLeanEqualityRewriteStepIr>,
}

#[derive(Clone)]
pub struct LitexToLeanEqualityRewriteStepIr {
    pub from: Obj,
    pub to: Obj,
    pub direction: LitexToLeanEqualityRewriteDirectionIr,
}

/// A direct equality proof path. In its enclosing `RuleApplication`, premise
/// `n` is the exact stored equality cited by `steps[n].source_fact_id`.
#[derive(Clone, Debug)]
pub struct LitexToLeanKnownEqualityPathIr {
    pub steps: Vec<LitexToLeanKnownEqualityStepIr>,
}

#[derive(Clone)]
pub struct LitexToLeanKnownEqualityStepIr {
    pub from: Obj,
    pub to: Obj,
    pub source_fact_id: FactId,
    pub direction: LitexToLeanEqualityRewriteDirectionIr,
}

impl fmt::Debug for LitexToLeanKnownEqualityStepIr {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("LitexToLeanKnownEqualityStepIr")
            .field("from", &self.from.to_string())
            .field("to", &self.to.to_string())
            .field("source_fact_id", &self.source_fact_id)
            .field("direction", &self.direction)
            .finish()
    }
}

impl fmt::Debug for LitexToLeanEqualityRewriteStepIr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("LitexToLeanEqualityRewriteStepIr")
            .field("from", &self.from.to_string())
            .field("to", &self.to.to_string())
            .field("direction", &self.direction)
            .finish()
    }
}

impl fmt::Debug for LitexToLeanProofRuleIr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LitexToLeanProofRuleIr::Builtin(rule) => f.debug_tuple("Builtin").field(rule).finish(),
            LitexToLeanProofRuleIr::RegisteredRule(application) => {
                f.debug_tuple("RegisteredRule").field(application).finish()
            }
            LitexToLeanProofRuleIr::ObjectReflexivity => f.write_str("ObjectReflexivity"),
            LitexToLeanProofRuleIr::TupleLiteralIsTuple {
                tuple,
                expected_target,
            } => f
                .debug_struct("TupleLiteralIsTuple")
                .field("tuple", tuple)
                .field("expected_target", &expected_target.to_string())
                .finish(),
            LitexToLeanProofRuleIr::TupleLiteralDimension {
                tuple,
                expected_target,
            } => f
                .debug_struct("TupleLiteralDimension")
                .field("tuple", tuple)
                .field("expected_target", &expected_target.to_string())
                .finish(),
            LitexToLeanProofRuleIr::ClosedRealMembership => f.write_str("ClosedRealMembership"),
            LitexToLeanProofRuleIr::ClosedStandardMembership => {
                f.write_str("ClosedStandardMembership")
            }
            LitexToLeanProofRuleIr::ClosedNumericReflection { target_set } => f
                .debug_struct("ClosedNumericReflection")
                .field("target_set", target_set)
                .finish(),
            LitexToLeanProofRuleIr::RealSetNonempty => f.write_str("RealSetNonempty"),
            LitexToLeanProofRuleIr::StandardSetNonempty => f.write_str("StandardSetNonempty"),
            LitexToLeanProofRuleIr::ObjectIsSet => f.write_str("ObjectIsSet"),
            LitexToLeanProofRuleIr::SetBuilderMembership {
                set_builder,
                expected_target,
                expected_premises,
            } => f
                .debug_struct("SetBuilderMembership")
                .field("set_builder", set_builder)
                .field("expected_target", &expected_target.to_string())
                .field(
                    "expected_premises",
                    &expected_premises
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>(),
                )
                .finish(),
            LitexToLeanProofRuleIr::FunctionSetMembership {
                element,
                function_set,
                expected_target,
                expected_pointwise,
            } => f
                .debug_struct("FunctionSetMembership")
                .field("element", element)
                .field("function_set", function_set)
                .field("expected_target", &expected_target.to_string())
                .field("expected_pointwise", &expected_pointwise.to_string())
                .finish(),
            LitexToLeanProofRuleIr::RefinedNumericMembership {
                target_set,
                expected_target,
                expected_premises,
            } => f
                .debug_struct("RefinedNumericMembership")
                .field("target_set", &target_set.to_string())
                .field("expected_target", &expected_target.to_string())
                .field(
                    "expected_premises",
                    &expected_premises
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>(),
                )
                .finish(),
            LitexToLeanProofRuleIr::ClosedNumericComparison { expected_target } => f
                .debug_struct("ClosedNumericComparison")
                .field("expected_target", &expected_target.to_string())
                .finish(),
            LitexToLeanProofRuleIr::FunctionApplicationReturnMembership {
                source_application,
                function_set,
                typed_return_set,
                expected_target,
                expected_head_membership,
            } => f
                .debug_struct("FunctionApplicationReturnMembership")
                .field("source_application", source_application)
                .field("function_set", function_set)
                .field("typed_return_set", typed_return_set)
                .field("expected_target", &expected_target.to_string())
                .field(
                    "expected_head_membership",
                    &expected_head_membership.to_string(),
                )
                .finish(),
            LitexToLeanProofRuleIr::EqualityRewrite(rewrite) => {
                f.debug_tuple("EqualityRewrite").field(rewrite).finish()
            }
            LitexToLeanProofRuleIr::KnownEqualityPath(path) => {
                f.debug_tuple("KnownEqualityPath").field(path).finish()
            }
            LitexToLeanProofRuleIr::IffRewrite { direction } => f
                .debug_struct("IffRewrite")
                .field("direction", direction)
                .finish(),
            LitexToLeanProofRuleIr::ComparisonNotationDuality {
                expected_source,
                expected_target,
            } => f
                .debug_struct("ComparisonNotationDuality")
                .field("expected_source", &expected_source.to_string())
                .field("expected_target", &expected_target.to_string())
                .finish(),
            LitexToLeanProofRuleIr::DefinitionReduction { definition, .. } => f
                .debug_struct("DefinitionReduction")
                .field("definition", definition)
                .finish(),
            LitexToLeanProofRuleIr::CheckedFunctionDefinitionReplay {
                definition,
                defining_equality_fact_id,
                defining_equality,
                expected_target,
                application_side,
                reduced,
                other_side,
                application_is_left,
                reduced_matches_other_by_alpha,
            } => f
                .debug_struct("CheckedFunctionDefinitionReplay")
                .field("definition", definition)
                .field("defining_equality_fact_id", defining_equality_fact_id)
                .field("defining_equality", &defining_equality.to_string())
                .field("expected_target", &expected_target.to_string())
                .field("application_side", &application_side.to_string())
                .field("reduced", &reduced.to_string())
                .field("other_side", &other_side.to_string())
                .field("application_is_left", application_is_left)
                .field(
                    "reduced_matches_other_by_alpha",
                    reduced_matches_other_by_alpha,
                )
                .finish(),
            LitexToLeanProofRuleIr::DefinitionProjection {
                definition,
                expected_source,
                expected_target,
            } => f
                .debug_struct("DefinitionProjection")
                .field("definition", definition)
                .field("expected_source", &expected_source.to_string())
                .field("expected_target", &expected_target.to_string())
                .finish(),
            LitexToLeanProofRuleIr::DefinitionIntroduction {
                definition,
                expected_source,
                expected_target,
            } => f
                .debug_struct("DefinitionIntroduction")
                .field("definition", definition)
                .field("expected_source", &expected_source.to_string())
                .field("expected_target", &expected_target.to_string())
                .finish(),
            LitexToLeanProofRuleIr::Normalization { kind } => {
                f.debug_struct("Normalization").field("kind", kind).finish()
            }
            LitexToLeanProofRuleIr::KnownForallInstantiation {
                source_fact_id,
                arguments,
            } => f
                .debug_struct("KnownForallInstantiation")
                .field("source_fact_id", source_fact_id)
                .field("arguments", arguments)
                .finish(),
            LitexToLeanProofRuleIr::ModusPonens => f.write_str("ModusPonens"),
            LitexToLeanProofRuleIr::AndIntroduction => f.write_str("AndIntroduction"),
            LitexToLeanProofRuleIr::ConjunctionProjection {
                expected_source,
                expected_target,
                index,
                count,
            } => f
                .debug_struct("ConjunctionProjection")
                .field("expected_source", &expected_source.to_string())
                .field("expected_target", &expected_target.to_string())
                .field("index", index)
                .field("count", count)
                .finish(),
            LitexToLeanProofRuleIr::DisjunctionIntroduction {
                expected_target,
                expected_selected,
                selected_index,
            } => f
                .debug_struct("DisjunctionIntroduction")
                .field("expected_target", &expected_target.to_string())
                .field("expected_selected", &expected_selected.to_string())
                .field("selected_index", selected_index)
                .finish(),
            LitexToLeanProofRuleIr::ExistIntroduction {
                witnesses,
                steps,
                expected_parameter_requirements,
                expected_body_facts,
            } => f
                .debug_struct("ExistIntroduction")
                .field(
                    "witnesses",
                    &witnesses
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>(),
                )
                .field("steps", steps)
                .field(
                    "expected_parameter_requirements",
                    &expected_parameter_requirements
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>(),
                )
                .field(
                    "expected_body_facts",
                    &expected_body_facts
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>(),
                )
                .finish(),
            LitexToLeanProofRuleIr::ClassicalExcludedMiddle => {
                f.write_str("ClassicalExcludedMiddle")
            }
            LitexToLeanProofRuleIr::CaseSplit => f.write_str("CaseSplit"),
            LitexToLeanProofRuleIr::OtherUnsupported { name } => f
                .debug_struct("OtherUnsupported")
                .field("name", name)
                .finish(),
        }
    }
}

/// Litex stores both comparison spellings (`a < b` and `b > a`) even though
/// they denote one ordered relation. This predicate is intentionally narrow:
/// it accepts only an exact operator-dual pair with swapped object identities.
pub fn facts_are_comparison_notation_duals(source: &Fact, target: &Fact) -> bool {
    let (Fact::AtomicFact(source), Fact::AtomicFact(target)) = (source, target) else {
        return false;
    };
    let swapped = |source_left: &Obj, source_right: &Obj, target_left: &Obj, target_right: &Obj| {
        crate::obj::obj_equality_key(source_left) == crate::obj::obj_equality_key(target_right)
            && crate::obj::obj_equality_key(source_right)
                == crate::obj::obj_equality_key(target_left)
    };
    match (source, target) {
        (AtomicFact::LessFact(source), AtomicFact::GreaterFact(target)) => {
            swapped(&source.left, &source.right, &target.left, &target.right)
        }
        (AtomicFact::GreaterFact(source), AtomicFact::LessFact(target)) => {
            swapped(&source.left, &source.right, &target.left, &target.right)
        }
        (AtomicFact::LessEqualFact(source), AtomicFact::GreaterEqualFact(target)) => {
            swapped(&source.left, &source.right, &target.left, &target.right)
        }
        (AtomicFact::GreaterEqualFact(source), AtomicFact::LessEqualFact(target)) => {
            swapped(&source.left, &source.right, &target.left, &target.right)
        }
        (AtomicFact::NotLessFact(source), AtomicFact::NotGreaterFact(target)) => {
            swapped(&source.left, &source.right, &target.left, &target.right)
        }
        (AtomicFact::NotGreaterFact(source), AtomicFact::NotLessFact(target)) => {
            swapped(&source.left, &source.right, &target.left, &target.right)
        }
        (AtomicFact::NotLessEqualFact(source), AtomicFact::NotGreaterEqualFact(target)) => {
            swapped(&source.left, &source.right, &target.left, &target.right)
        }
        (AtomicFact::NotGreaterEqualFact(source), AtomicFact::NotLessEqualFact(target)) => {
            swapped(&source.left, &source.right, &target.left, &target.right)
        }
        _ => false,
    }
}

#[derive(Clone)]
pub struct LitexToLeanKnownForallArgumentIr {
    pub param: String,
    pub argument: Obj,
    /// Records the exact membership or set-property requirement retained from
    /// Litex. The object argument itself always lowers to `Litex.Object`.
    pub param_type: LitexToLeanParameterTypeIr,
}

impl fmt::Debug for LitexToLeanKnownForallArgumentIr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("LitexToLeanKnownForallArgumentIr")
            .field("param", &self.param)
            .field("argument", &self.argument.to_string())
            .field("param_type", &self.param_type)
            .finish()
    }
}

impl LitexToLeanProofRuleIr {
    pub fn from_verified_builtin_label(label: &str, goal: &Fact) -> Self {
        if let Some(target_set) = closed_compact_numeric_set_fact(goal) {
            return LitexToLeanProofRuleIr::ClosedNumericReflection { target_set };
        }
        if is_closed_standard_membership(goal) {
            return LitexToLeanProofRuleIr::ClosedStandardMembership;
        }
        if is_checked_closed_integer_remainder_equality(goal) {
            return LitexToLeanProofRuleIr::Normalization {
                kind: LitexToLeanNormalizationKindIr::IntegerExpressionSimplification,
            };
        }
        if matches!(
            goal,
            Fact::AtomicFact(crate::fact::AtomicFact::EqualFact(equality))
                if crate::obj::obj_equality_key(&equality.left)
                    == crate::obj::obj_equality_key(&equality.right)
        ) {
            return LitexToLeanProofRuleIr::ObjectReflexivity;
        }
        if label == "injectivity of native exp"
            && matches!(
            goal,
            Fact::AtomicFact(crate::fact::AtomicFact::EqualFact(equality))
                if is_closed_rational_obj(&equality.left)
                    && is_closed_rational_obj(&equality.right)
                    && objs_equal_by_rational_expression_evaluation(
                        &equality.left,
                        &equality.right,
                    )
            )
        {
            return LitexToLeanProofRuleIr::Normalization {
                kind: LitexToLeanNormalizationKindIr::RationalExpressionSimplification,
            };
        }
        match label {
            "they are the same" | "known-only equality: they are the same"
                if matches!(
                    goal,
                    Fact::AtomicFact(crate::fact::AtomicFact::EqualFact(equality))
                        if crate::obj::obj_equality_key(&equality.left)
                            == crate::obj::obj_equality_key(&equality.right)
                ) =>
            {
                LitexToLeanProofRuleIr::ObjectReflexivity
            }
            "calculation and rational expression simplification" => {
                LitexToLeanProofRuleIr::Normalization {
                    kind: LitexToLeanNormalizationKindIr::RationalExpressionSimplification,
                }
            }
            "bounded symbolic normalization"
                if matches!(
                    goal,
                    Fact::AtomicFact(crate::fact::AtomicFact::EqualFact(equality))
                        if objs_equal_by_rational_expression_evaluation(
                            &equality.left,
                            &equality.right,
                        )
                ) =>
            {
                LitexToLeanProofRuleIr::Normalization {
                    kind: LitexToLeanNormalizationKindIr::RationalExpressionSimplification,
                }
            }
            "or: complementary atomic facts" if is_binary_complementary_or(goal) => {
                LitexToLeanProofRuleIr::ClassicalExcludedMiddle
            }
            "standard_nonempty_set" if is_real_set_nonempty(goal) => {
                LitexToLeanProofRuleIr::RealSetNonempty
            }
            "standard_nonempty_set" if is_supported_standard_set_nonempty(goal) => {
                LitexToLeanProofRuleIr::StandardSetNonempty
            }
            "Every object is a set."
                if matches!(
                    goal,
                    Fact::AtomicFact(crate::fact::AtomicFact::IsSetFact(_))
                ) =>
            {
                LitexToLeanProofRuleIr::ObjectIsSet
            }
            _ if is_closed_real_membership(goal) => LitexToLeanProofRuleIr::ClosedRealMembership,
            other => LitexToLeanProofRuleIr::OtherUnsupported {
                name: other.to_string(),
            },
        }
    }
}

fn is_real_set_nonempty(goal: &Fact) -> bool {
    matches!(
        goal,
        Fact::AtomicFact(crate::fact::AtomicFact::IsNonemptySetFact(fact))
            if matches!(fact.set, Obj::StandardSet(crate::obj::StandardSet::R))
    )
}

fn is_supported_standard_set_nonempty(goal: &Fact) -> bool {
    matches!(
        goal,
        Fact::AtomicFact(crate::fact::AtomicFact::IsNonemptySetFact(fact))
            if matches!(
                fact.set,
                Obj::StandardSet(
                    crate::obj::StandardSet::N
                        | crate::obj::StandardSet::Z
                        | crate::obj::StandardSet::Q
                        | crate::obj::StandardSet::C
                        | crate::obj::StandardSet::NPos
                        | crate::obj::StandardSet::QPos
                        | crate::obj::StandardSet::RPos
                        | crate::obj::StandardSet::QNeg
                        | crate::obj::StandardSet::ZNeg
                        | crate::obj::StandardSet::RNeg
                        | crate::obj::StandardSet::QStar
                        | crate::obj::StandardSet::ZStar
                        | crate::obj::StandardSet::RStar
                        | crate::obj::StandardSet::CStar
                )
            )
    )
}

fn is_binary_complementary_or(goal: &Fact) -> bool {
    let Fact::OrFact(or_fact) = goal else {
        return false;
    };
    if or_fact.facts.len() != 2 {
        return false;
    }
    let (
        crate::fact::AndChainAtomicFact::AtomicFact(first),
        crate::fact::AndChainAtomicFact::AtomicFact(second),
    ) = (&or_fact.facts[0], &or_fact.facts[1])
    else {
        return false;
    };
    first
        .logical_negation()
        .is_ok_and(|negated| negated.to_string() == second.to_string())
}

pub(crate) fn is_closed_real_membership(goal: &Fact) -> bool {
    matches!(
        goal,
        Fact::AtomicFact(crate::fact::AtomicFact::InFact(membership))
            if matches!(membership.set, Obj::StandardSet(crate::obj::StandardSet::R))
                && is_closed_rational_obj(&membership.element)
    )
}

pub(crate) fn is_closed_standard_membership(goal: &Fact) -> bool {
    matches!(
        goal,
        Fact::AtomicFact(crate::fact::AtomicFact::InFact(membership))
            if matches!(
                membership.set,
                Obj::StandardSet(
                    crate::obj::StandardSet::N
                        | crate::obj::StandardSet::Z
                        | crate::obj::StandardSet::Q
                        | crate::obj::StandardSet::R
                        | crate::obj::StandardSet::C
                )
            ) && is_closed_rational_obj(&membership.element)
    )
}

pub(crate) fn closed_compact_numeric_set_fact(goal: &Fact) -> Option<LitexToLeanStandardSetIr> {
    let Fact::AtomicFact(atomic) = goal else {
        return None;
    };
    let (element, set) = match atomic {
        crate::fact::AtomicFact::InFact(fact) => (&fact.element, &fact.set),
        crate::fact::AtomicFact::NotInFact(fact) => (&fact.element, &fact.set),
        _ => return None,
    };
    if !is_closed_rational_obj(element) {
        return None;
    }
    let Obj::StandardSet(standard) = set else {
        return None;
    };
    if !matches!(
        standard,
        crate::obj::StandardSet::NPos
            | crate::obj::StandardSet::QPos
            | crate::obj::StandardSet::RPos
            | crate::obj::StandardSet::ZNeg
            | crate::obj::StandardSet::QNeg
            | crate::obj::StandardSet::RNeg
            | crate::obj::StandardSet::ZStar
            | crate::obj::StandardSet::QStar
            | crate::obj::StandardSet::RStar
            | crate::obj::StandardSet::CStar
    ) {
        return None;
    }
    Some(LitexToLeanStandardSetIr::from(standard))
}

pub(crate) fn is_closed_numeric_relation(goal: &Fact) -> bool {
    let Fact::AtomicFact(atomic) = goal else {
        return false;
    };
    match atomic {
        crate::fact::AtomicFact::EqualFact(fact) => {
            is_closed_rational_obj(&fact.left) && is_closed_rational_obj(&fact.right)
        }
        crate::fact::AtomicFact::NotEqualFact(fact) => {
            is_closed_rational_obj(&fact.left) && is_closed_rational_obj(&fact.right)
        }
        crate::fact::AtomicFact::LessFact(fact) => {
            is_closed_rational_obj(&fact.left) && is_closed_rational_obj(&fact.right)
        }
        crate::fact::AtomicFact::GreaterFact(fact) => {
            is_closed_rational_obj(&fact.left) && is_closed_rational_obj(&fact.right)
        }
        crate::fact::AtomicFact::LessEqualFact(fact) => {
            is_closed_rational_obj(&fact.left) && is_closed_rational_obj(&fact.right)
        }
        crate::fact::AtomicFact::GreaterEqualFact(fact) => {
            is_closed_rational_obj(&fact.left) && is_closed_rational_obj(&fact.right)
        }
        crate::fact::AtomicFact::NotLessFact(fact) => {
            is_closed_rational_obj(&fact.left) && is_closed_rational_obj(&fact.right)
        }
        crate::fact::AtomicFact::NotGreaterFact(fact) => {
            is_closed_rational_obj(&fact.left) && is_closed_rational_obj(&fact.right)
        }
        crate::fact::AtomicFact::NotLessEqualFact(fact) => {
            is_closed_rational_obj(&fact.left) && is_closed_rational_obj(&fact.right)
        }
        crate::fact::AtomicFact::NotGreaterEqualFact(fact) => {
            is_closed_rational_obj(&fact.left) && is_closed_rational_obj(&fact.right)
        }
        _ => false,
    }
}

/// Validate the small closed-integer fragment used for checked `%`
/// computation. At least one remainder node must occur, every literal is an
/// integer, every divisor evaluates to a nonzero integer, and Litex's own
/// evaluator must produce equal normalized results on both sides.
pub(crate) fn is_checked_closed_integer_remainder_equality(goal: &Fact) -> bool {
    let Fact::AtomicFact(crate::fact::AtomicFact::EqualFact(equality)) = goal else {
        return false;
    };
    let mut contains_remainder = false;
    if !is_closed_integer_obj_with_remainder(&equality.left, &mut contains_remainder)
        || !is_closed_integer_obj_with_remainder(&equality.right, &mut contains_remainder)
        || !contains_remainder
    {
        return false;
    }
    match (
        equality.left.evaluate_to_normalized_decimal_number(),
        equality.right.evaluate_to_normalized_decimal_number(),
    ) {
        (Some(left), Some(right)) => left.normalized_value == right.normalized_value,
        _ => false,
    }
}

fn is_closed_integer_obj_with_remainder(obj: &Obj, contains_remainder: &mut bool) -> bool {
    match obj {
        Obj::Number(number) => !number.normalized_value.contains('.'),
        Obj::Add(value) => {
            is_closed_integer_obj_with_remainder(value.left.as_ref(), contains_remainder)
                && is_closed_integer_obj_with_remainder(value.right.as_ref(), contains_remainder)
        }
        Obj::Sub(value) => {
            is_closed_integer_obj_with_remainder(value.left.as_ref(), contains_remainder)
                && is_closed_integer_obj_with_remainder(value.right.as_ref(), contains_remainder)
        }
        Obj::Mul(value) => {
            is_closed_integer_obj_with_remainder(value.left.as_ref(), contains_remainder)
                && is_closed_integer_obj_with_remainder(value.right.as_ref(), contains_remainder)
        }
        Obj::Mod(value) => {
            *contains_remainder = true;
            let divisor_is_nonzero = value
                .right
                .evaluate_to_normalized_decimal_number()
                .is_some_and(|number| number.normalized_value != "0");
            divisor_is_nonzero
                && is_closed_integer_obj_with_remainder(value.left.as_ref(), contains_remainder)
                && is_closed_integer_obj_with_remainder(value.right.as_ref(), contains_remainder)
        }
        _ => false,
    }
}

fn is_closed_rational_obj(obj: &Obj) -> bool {
    match obj {
        Obj::Number(_) => true,
        Obj::Add(value) => {
            is_closed_rational_obj(value.left.as_ref())
                && is_closed_rational_obj(value.right.as_ref())
        }
        Obj::Sub(value) => {
            is_closed_rational_obj(value.left.as_ref())
                && is_closed_rational_obj(value.right.as_ref())
        }
        Obj::Mul(value) => {
            is_closed_rational_obj(value.left.as_ref())
                && is_closed_rational_obj(value.right.as_ref())
        }
        Obj::Div(value) => {
            is_closed_rational_obj(value.left.as_ref())
                && is_closed_rational_obj(value.right.as_ref())
        }
        _ => false,
    }
}
