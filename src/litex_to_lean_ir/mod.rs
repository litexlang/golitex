//! Checked, backend-facing evidence built by `LitexToLeanIrBuilder` from verifier results.
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
    WellDefinednessSourceObjectUse,
};
use crate::symbol::SymbolId;
use std::fmt;

mod builder;
mod builtin_rule;
mod capture;
mod def_thm_stmt;
mod function;
mod object;
mod registered_rule;
mod statement;
mod well_definedness;

pub use builder::LitexToLeanIrBuilder;
pub use builtin_rule::{LitexToLeanArithmeticBuiltinRuleIr, LitexToLeanBuiltinRuleIr};
pub use capture::capture_litex_to_lean_ir_from_source;
pub use def_thm_stmt::{LitexToLeanDefThmStmtIr, LitexToLeanDefThmStmtProofStepIr};
pub use function::{
    LitexToLeanFunctionApplicationIr, LitexToLeanFunctionParameterIr, LitexToLeanFunctionTypeIr,
};
pub use object::{
    LitexToLeanAggregateObjectIr, LitexToLeanAnonymousFunctionIr,
    LitexToLeanBuiltinObjectOperatorIr, LitexToLeanCollectionObjectIr, LitexToLeanConstantObjectIr,
    LitexToLeanObjectIr, LitexToLeanSetBuilderIr, LitexToLeanStandardSetIr,
};
pub(crate) use registered_rule::{
    registered_rule_has_lean_adapter, ADD_NONNEGATIVE_FINGERPRINT, ADD_NONNEGATIVE_RULE_ID,
    ADD_POSITIVE_OF_NONNEGATIVE_POSITIVE_FINGERPRINT, ADD_POSITIVE_OF_NONNEGATIVE_POSITIVE_RULE_ID,
    ADD_POSITIVE_OF_POSITIVE_NONNEGATIVE_FINGERPRINT, ADD_POSITIVE_OF_POSITIVE_NONNEGATIVE_RULE_ID,
    LESS_EQUAL_OF_LESS_FINGERPRINT, LESS_EQUAL_OF_LESS_RULE_ID,
};
pub use registered_rule::{LitexToLeanRegisteredRuleApplicationIr, LitexToLeanTypedBoundObjectIr};
pub use statement::*;
pub(crate) use well_definedness::validate_litex_to_lean_well_definedness_certificate;

#[derive(Clone, Debug)]
pub struct LitexToLeanStoredFunctionFactIr {
    pub fact_id: FactId,
    pub proposition: Fact,
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
}

#[derive(Clone, Debug, Default)]
pub struct LitexToLeanWellDefinednessCertificateIr {
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
    pub role: WellDefinednessRequirementRole,
    pub well_defined_fact_id: WellDefinedFactId,
}

impl fmt::Debug for LitexToLeanWellDefinednessTargetRequirementIr {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("LitexToLeanWellDefinednessTargetRequirementIr")
            .field("source_occurrence_id", &self.source_occurrence_id)
            .field("well_defined_obj_id", &self.well_defined_obj_id)
            .field("role", &self.role)
            .field("well_defined_fact_id", &self.well_defined_fact_id)
            .finish()
    }
}

#[derive(Clone, Debug)]
pub struct LitexToLeanFactIr {
    /// Storage identity is an explicit sum rather than an optional FactId:
    /// proof-only nodes are anonymous and environment effects are stored.
    pub storage: LitexToLeanFactStorageIr,
    pub proposition: Fact,
    pub proof: LitexToLeanFactProofIr,
}

impl LitexToLeanFactIr {
    pub fn stored_fact_id(&self) -> Option<FactId> {
        self.storage.fact_id()
    }

    pub fn make_anonymous(&mut self) {
        self.storage = LitexToLeanFactStorageIr::Anonymous;
    }

    pub fn store_as(&mut self, fact_id: FactId) {
        self.storage = LitexToLeanFactStorageIr::Stored(fact_id);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LitexToLeanFactStorageIr {
    Anonymous,
    Stored(FactId),
}

impl LitexToLeanFactStorageIr {
    pub fn fact_id(self) -> Option<FactId> {
        match self {
            Self::Anonymous => None,
            Self::Stored(fact_id) => Some(fact_id),
        }
    }
}

impl From<Option<FactId>> for LitexToLeanFactStorageIr {
    fn from(fact_id: Option<FactId>) -> Self {
        match fact_id {
            Some(fact_id) => Self::Stored(fact_id),
            None => Self::Anonymous,
        }
    }
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
    /// Marks that the verifier selected its builtin-strategy route. The
    /// recursively retained proof is the concrete rule/fact evidence that
    /// Lean replays; the compiler never re-runs strategy search.
    UseBuiltinStrategy {
        proof: Box<LitexToLeanFactProofIr>,
    },
    /// Citation of a positive existential whose binders were alpha-renamed by
    /// parsing or witness extraction.  Runtime lowering admits this node only
    /// after the verifier's canonical existential comparison succeeds.
    ExistentialAlphaRenameCitation {
        source_fact_id: FactId,
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
    /// A defining equality released by a sibling object declaration.
    ObjectDefinitionEquality,
    /// A membership/type fact released by a sibling object declaration. The
    /// retained premise is the verifier's check for the declaration value.
    ObjectDefinitionMembership {
        value_check: Box<LitexToLeanFactIr>,
    },
    /// Membership released by a sibling `LitexToLeanObjectChoiceIr`. The sibling
    /// carries the nonemptiness proof used by both `Exists.choose` and
    /// `Exists.choose_spec` during emission.
    ObjectChoice,
    /// A type or body fact projected by a sibling existential-elimination
    /// statement. The enclosing fact proposition is the projection target.
    ExistentialElimination {
        role: LitexToLeanExistentialProjectionRoleIr,
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
    ClosedStandardMembership,
    StandardSetNonempty,
    /// Literal set-builder membership from the base membership and each
    /// instantiated defining fact, in source order.
    SetBuilderMembership,
    /// Projection from membership in a literal set builder to membership in
    /// its retained base set.
    SetBuilderBaseMembershipProjection,
    /// Projection of one instantiated defining predicate from membership in
    /// the exact set-builder carrier.
    SetBuilderPredicateProjection {
        clause_index: usize,
    },
    ClosedNumericComparison,
    EqualityRewrite,
    KnownEqualityPath,
    /// The verifier cited the same ordered relation through Litex's dual
    /// surface notation, for example `0 < b` while checking `b > 0`.
    ComparisonNotationDuality,
    DefinitionReduction,
    /// Equality obtained by unfolding one verifier-selected named function.
    /// Its defining FactId resolves the function binding; target syntax fixes
    /// the application, result, and orientation.
    CheckedFunctionDefinitionReduction {
        defining_equality_fact_id: FactId,
        application_side: LitexToLeanEqualitySideIr,
    },
    /// Checked unfolding of one concrete proposition definition. The source
    /// and target are the enclosing application's premise and proposition.
    DefinitionProjection,
    /// Checked folding of one concrete proposition definition. The source and
    /// target are the enclosing application's premise and proposition.
    DefinitionIntroduction,
    RationalNormalization,
    KnownForallInstantiation {
        source_fact_id: FactId,
        arguments: Vec<Obj>,
    },
    AndIntroduction,
    DisjunctionIntroduction {
        selected_index: usize,
    },
    ConjunctionProjection {
        index: usize,
    },
    ExistIntroduction {
        witnesses: Vec<Obj>,
        /// User proof statements executed in the temporary witness scope.
        /// Body verification may cite their retained FactIds.
        steps: Vec<LitexToLeanStatementIr>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LitexToLeanEqualitySideIr {
    Left,
    Right,
}

impl fmt::Debug for LitexToLeanProofRuleIr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LitexToLeanProofRuleIr::Builtin(rule) => f.debug_tuple("Builtin").field(rule).finish(),
            LitexToLeanProofRuleIr::RegisteredRule(application) => {
                f.debug_tuple("RegisteredRule").field(application).finish()
            }
            LitexToLeanProofRuleIr::ObjectReflexivity => f.write_str("ObjectReflexivity"),
            LitexToLeanProofRuleIr::ClosedStandardMembership => {
                f.write_str("ClosedStandardMembership")
            }
            LitexToLeanProofRuleIr::StandardSetNonempty => f.write_str("StandardSetNonempty"),
            LitexToLeanProofRuleIr::SetBuilderMembership => f.write_str("SetBuilderMembership"),
            LitexToLeanProofRuleIr::SetBuilderBaseMembershipProjection => {
                f.write_str("SetBuilderBaseMembershipProjection")
            }
            LitexToLeanProofRuleIr::SetBuilderPredicateProjection { clause_index } => f
                .debug_struct("SetBuilderPredicateProjection")
                .field("clause_index", clause_index)
                .finish(),
            LitexToLeanProofRuleIr::ClosedNumericComparison => {
                f.write_str("ClosedNumericComparison")
            }
            LitexToLeanProofRuleIr::EqualityRewrite => f.write_str("EqualityRewrite"),
            LitexToLeanProofRuleIr::KnownEqualityPath => f.write_str("KnownEqualityPath"),
            LitexToLeanProofRuleIr::ComparisonNotationDuality => {
                f.write_str("ComparisonNotationDuality")
            }
            LitexToLeanProofRuleIr::DefinitionReduction => f.write_str("DefinitionReduction"),
            LitexToLeanProofRuleIr::CheckedFunctionDefinitionReduction {
                defining_equality_fact_id,
                application_side,
            } => f
                .debug_struct("CheckedFunctionDefinitionReduction")
                .field("defining_equality_fact_id", defining_equality_fact_id)
                .field("application_side", application_side)
                .finish(),
            LitexToLeanProofRuleIr::DefinitionProjection => f.write_str("DefinitionProjection"),
            LitexToLeanProofRuleIr::DefinitionIntroduction => f.write_str("DefinitionIntroduction"),
            LitexToLeanProofRuleIr::RationalNormalization => f.write_str("RationalNormalization"),
            LitexToLeanProofRuleIr::KnownForallInstantiation {
                source_fact_id,
                arguments,
            } => f
                .debug_struct("KnownForallInstantiation")
                .field("source_fact_id", source_fact_id)
                .field(
                    "arguments",
                    &arguments
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>(),
                )
                .finish(),
            LitexToLeanProofRuleIr::AndIntroduction => f.write_str("AndIntroduction"),
            LitexToLeanProofRuleIr::ConjunctionProjection { index } => f
                .debug_struct("ConjunctionProjection")
                .field("index", index)
                .finish(),
            LitexToLeanProofRuleIr::DisjunctionIntroduction { selected_index } => f
                .debug_struct("DisjunctionIntroduction")
                .field("selected_index", selected_index)
                .finish(),
            LitexToLeanProofRuleIr::ExistIntroduction { witnesses, steps } => f
                .debug_struct("ExistIntroduction")
                .field(
                    "witnesses",
                    &witnesses
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>(),
                )
                .field("steps", steps)
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

impl LitexToLeanProofRuleIr {
    pub fn try_from_verified_builtin_label(label: &str, goal: &Fact) -> Option<Self> {
        if is_closed_standard_membership(goal) {
            return Some(Self::ClosedStandardMembership);
        }
        if matches!(
            goal,
            Fact::AtomicFact(AtomicFact::EqualFact(equality))
                if crate::obj::obj_equality_key(&equality.left)
                    == crate::obj::obj_equality_key(&equality.right)
        ) {
            return Some(Self::ObjectReflexivity);
        }
        if label == "injectivity of native exp"
            && matches!(
                goal,
                Fact::AtomicFact(AtomicFact::EqualFact(equality))
                    if is_closed_rational_obj(&equality.left)
                        && is_closed_rational_obj(&equality.right)
                        && objs_equal_by_rational_expression_evaluation(
                            &equality.left,
                            &equality.right,
                        )
            )
        {
            return Some(Self::RationalNormalization);
        }
        if label == "numeric-carrier strategy: structural closure in R"
            && matches!(
                goal,
                Fact::AtomicFact(AtomicFact::InFact(fact))
                    if matches!(fact.element, Obj::Add(_))
                        && matches!(fact.set, Obj::StandardSet(StandardSet::R))
            )
        {
            return Some(Self::Builtin(
                LitexToLeanBuiltinRuleIr::RealAddMembershipClosure,
            ));
        }
        match label {
            "calculation and rational expression simplification" => {
                Some(Self::RationalNormalization)
            }
            "bounded symbolic normalization"
                if matches!(
                    goal,
                    Fact::AtomicFact(AtomicFact::EqualFact(equality))
                        if objs_equal_by_rational_expression_evaluation(
                            &equality.left,
                            &equality.right,
                        )
                ) =>
            {
                Some(Self::RationalNormalization)
            }
            "standard_nonempty_set" if is_real_set_nonempty(goal) => {
                Some(Self::StandardSetNonempty)
            }
            "standard_nonempty_set" if is_supported_standard_set_nonempty(goal) => {
                Some(Self::StandardSetNonempty)
            }
            _ if is_closed_real_membership(goal) => Some(Self::ClosedStandardMembership),
            _ => None,
        }
    }
}

fn is_real_set_nonempty(goal: &Fact) -> bool {
    matches!(
        goal,
        Fact::AtomicFact(AtomicFact::IsNonemptySetFact(fact))
            if matches!(fact.set, Obj::StandardSet(StandardSet::R))
    )
}

fn is_supported_standard_set_nonempty(goal: &Fact) -> bool {
    matches!(
        goal,
        Fact::AtomicFact(AtomicFact::IsNonemptySetFact(fact))
            if matches!(
                fact.set,
                Obj::StandardSet(
                    StandardSet::N
                        | StandardSet::Z
                        | StandardSet::Q
                        | StandardSet::C
                        | StandardSet::NPos
                        | StandardSet::QPos
                        | StandardSet::RPos
                        | StandardSet::QNeg
                        | StandardSet::ZNeg
                        | StandardSet::RNeg
                        | StandardSet::QStar
                        | StandardSet::ZStar
                        | StandardSet::RStar
                        | StandardSet::CStar
                )
            )
    )
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
