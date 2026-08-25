//! Successful verification and proof-route evidence records.

use crate::prelude::*;
use std::fmt;
use std::rc::Rc;

#[derive(Debug)]
pub struct SuccessVerifyArgsSatisfyParamDefResult {
    pub checks: Vec<StmtResult>,
    pub infers: SuccessInferResult,
}

#[derive(Debug)]
pub struct UnknownVerifyArgsSatisfyParamDefResult {
    pub cause: Box<StmtResult>,
}

#[derive(Debug)]
pub enum VerifyArgsSatisfyParamDefResult {
    Success(Box<SuccessVerifyArgsSatisfyParamDefResult>),
    Unknown(Box<UnknownVerifyArgsSatisfyParamDefResult>),
}

impl VerifyArgsSatisfyParamDefResult {
    pub fn success(checks: Vec<StmtResult>, infers: SuccessInferResult) -> Self {
        Self::Success(Box::new(SuccessVerifyArgsSatisfyParamDefResult {
            checks,
            infers,
        }))
    }

    pub fn unknown(cause: StmtResult) -> Self {
        Self::Unknown(Box::new(UnknownVerifyArgsSatisfyParamDefResult {
            cause: Box::new(cause),
        }))
    }

    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown(_))
    }

    pub fn success_result(&self) -> Option<&SuccessVerifyArgsSatisfyParamDefResult> {
        match self {
            Self::Success(result) => Some(result),
            Self::Unknown(_) => None,
        }
    }

    pub fn into_success(self) -> Option<SuccessVerifyArgsSatisfyParamDefResult> {
        match self {
            Self::Success(result) => Some(*result),
            Self::Unknown(_) => None,
        }
    }

    pub fn into_unknown_cause(self) -> Option<StmtResult> {
        match self {
            Self::Success(_) => None,
            Self::Unknown(result) => Some(*result.cause),
        }
    }
}

#[derive(Debug)]
pub struct SuccessVerifyFunctionDefinitionResult {
    pub return_check: Box<StmtResult>,
    /// Membership/domain facts installed while checking the return value,
    /// with their temporary FactIds frozen before that local scope closes.
    pub assumption_infers: SuccessInferResult,
    pub function_membership: Fact,
    pub defining_equality: Fact,
}

impl SuccessVerifyFunctionDefinitionResult {
    pub fn new(
        return_check: StmtResult,
        assumption_infers: SuccessInferResult,
        function_membership: Fact,
        defining_equality: Fact,
    ) -> Self {
        Self {
            return_check: Box::new(return_check),
            assumption_infers,
            function_membership,
            defining_equality,
        }
    }
}

pub struct SuccessVerifyTheoremResult {
    pub name: String,
    pub forall_fact: ForallFact,
    pub well_definedness: SuccessVerifyFactWellDefinedResult,
    pub proof_scope: SuccessVerifyLocalProofScopeResult,
    pub proof_steps: Vec<StmtResult>,
    pub conclusion_checks: Vec<StmtResult>,
}

pub enum SuccessVerifyClaimResult {
    Forall(Box<SuccessVerifyClaimForallResult>),
    Fact(Box<SuccessVerifyClaimFactResult>),
}

pub struct SuccessVerifyClaimForallResult {
    pub forall_fact: ForallFact,
    pub well_definedness: SuccessVerifyFactWellDefinedResult,
    pub proof_scope: SuccessVerifyLocalProofScopeResult,
    pub proof_steps: Vec<StmtResult>,
    pub conclusion_checks: Vec<StmtResult>,
}

pub struct SuccessVerifyClaimFactResult {
    pub fact: Fact,
    pub well_definedness: SuccessVerifyFactWellDefinedResult,
    pub proof_scope: SuccessVerifyLocalProofScopeResult,
    pub proof_steps: Vec<StmtResult>,
    pub conclusion_check: Box<StmtResult>,
}

pub struct SuccessVerifyByCasesResult {
    /// Well-definedness of each exported goal, checked before any case-local
    /// assumptions are installed. This is intentionally separate from the
    /// branch conclusion checks below: it is the evidence needed to form the
    /// statement's result outside every branch scope.
    pub goal_well_definedness: Vec<SuccessVerifyFactWellDefinedResult>,
    pub coverage_check: Box<StmtResult>,
    pub then_facts: Vec<Fact>,
    pub branches: Vec<SuccessVerifyByCaseBranchResult>,
}

pub struct SuccessVerifyByCaseBranchResult {
    pub assumption: AndChainAtomicFact,
    pub assumption_fact_id: FactId,
    pub proof_scope: SuccessVerifyLocalProofScopeResult,
    pub proof_steps: Vec<StmtResult>,
    pub exit: SuccessVerifyByCaseBranchExitResult,
}

pub enum SuccessVerifyByCaseBranchExitResult {
    Conclusions(Box<SuccessVerifyByCaseConclusionsResult>),
    Contradiction(Box<SuccessVerifyByCaseContradictionResult>),
}

pub struct SuccessVerifyByCaseConclusionsResult {
    pub checks: Vec<StmtResult>,
}

pub struct SuccessVerifyByCaseContradictionResult {
    pub impossible_fact: AtomicFact,
    pub contradiction: SuccessVerifyContradictionResult,
}

pub struct SuccessVerifyByContraResult {
    pub to_prove: Fact,
    pub reverse_assumption: Fact,
    /// Stable ID of the temporary reverse assumption while the contradiction
    /// proof environment was alive.
    pub reverse_assumption_fact_id: FactId,
    pub proof_scope: SuccessVerifyLocalProofScopeResult,
    pub proof_steps: Vec<StmtResult>,
    pub impossible_fact: AtomicFact,
    pub contradiction: SuccessVerifyContradictionResult,
}

#[derive(Debug)]
pub struct SuccessVerifyContradictionResult {
    pub impossible_check: Box<StmtResult>,
    pub negated_impossible_check: Box<StmtResult>,
}

#[derive(Clone, Debug)]
pub struct SuccessVerifyLocalProofScopeResult {
    pub assumption_infers: SuccessInferResult,
    pub assumption_components: Vec<(FactId, Fact)>,
}

impl SuccessVerifyLocalProofScopeResult {
    pub fn new(
        assumption_infers: SuccessInferResult,
        assumption_components: Vec<(FactId, Fact)>,
    ) -> Self {
        Self {
            assumption_infers,
            assumption_components,
        }
    }
}

#[derive(Debug)]
pub struct SuccessVerifyByAssignmentResult {
    pub assignment: Vec<(String, String)>,
    pub assumptions: Vec<SuccessVerifyByAssignmentAssumptionResult>,
    pub domain_checks: Vec<SuccessVerifyByAssignmentDomainResult>,
    pub proof_steps: Vec<StmtResult>,
    pub conclusion_checks: Vec<StmtResult>,
}

/// One exact fact introduced by a finite assignment branch. The complete
/// inference Result stays with the assumption because later proof children
/// may cite either its source FactId or one of its typed consequences.
#[derive(Debug)]
pub struct SuccessVerifyByAssignmentAssumptionResult {
    pub fact: Fact,
    pub fact_id: FactId,
    pub reason: String,
    pub infers: SuccessInferResult,
}

#[derive(Debug)]
pub struct SuccessVerifyByAssignmentDomainResult {
    pub fact: Fact,
    pub check: Box<StmtResult>,
    pub negated_check: Option<Box<StmtResult>>,
    pub satisfied: bool,
    /// Exact store/inference effects published only by a satisfied branch.
    /// A skipped assignment retains `None` and its checked negation instead.
    pub satisfied_infers: Option<SuccessInferResult>,
}

pub struct SuccessVerifyByEnumerateFiniteSetResult {
    pub parameters: Vec<String>,
    /// Exact list-set values selected by execution, including named source
    /// types that were resolved through equality before enumeration.
    pub parameter_sets: Vec<ListSet>,
    pub prove_goal: String,
    pub assignments: Vec<SuccessVerifyByAssignmentResult>,
    pub generated_forall: String,
}

impl fmt::Debug for SuccessVerifyByEnumerateFiniteSetResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByEnumerateFiniteSetResult")
            .field("parameters", &self.parameters)
            .field(
                "parameter_sets",
                &self
                    .parameter_sets
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>(),
            )
            .field("prove_goal", &self.prove_goal)
            .field("assignments", &self.assignments)
            .field("generated_forall", &self.generated_forall)
            .finish()
    }
}

pub struct SuccessVerifyByForRangesResult {
    pub parameters: Vec<SuccessVerifyByForRangeParameterResult>,
    pub prove_goal: String,
    pub assignments: Vec<SuccessVerifyByAssignmentResult>,
    pub generated_forall: String,
}

pub struct SuccessVerifyByForRangeParameterResult {
    pub parameter: String,
    pub range: ClosedRangeOrRange,
    pub evaluated_start: String,
    pub evaluated_end: String,
    pub enumerated_values: Vec<String>,
}

pub struct SuccessVerifyByForCartesianProductOfListSetsResult {
    pub parameter: String,
    pub factors: Vec<ListSet>,
    pub prove_goal: String,
    pub assignments: Vec<SuccessVerifyByAssignmentResult>,
    pub generated_forall: String,
}

pub enum SuccessVerifyByForResult {
    Ranges(Box<SuccessVerifyByForRangesResult>),
    CartesianProductOfListSets(Box<SuccessVerifyByForCartesianProductOfListSetsResult>),
}

impl fmt::Debug for SuccessVerifyByForRangesResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByForRangesResult")
            .field("parameters", &self.parameters)
            .field("prove_goal", &self.prove_goal)
            .field("assignments", &self.assignments)
            .field("generated_forall", &self.generated_forall)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyByForRangeParameterResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByForRangeParameterResult")
            .field("parameter", &self.parameter)
            .field("range", &self.range.to_string())
            .field("evaluated_start", &self.evaluated_start)
            .field("evaluated_end", &self.evaluated_end)
            .field("enumerated_values", &self.enumerated_values)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyByForCartesianProductOfListSetsResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByForCartesianProductOfListSetsResult")
            .field("parameter", &self.parameter)
            .field(
                "factors",
                &self
                    .factors
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>(),
            )
            .field("prove_goal", &self.prove_goal)
            .field("assignments", &self.assignments)
            .field("generated_forall", &self.generated_forall)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyByForResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::Ranges(result) => result.fmt(f),
            Self::CartesianProductOfListSets(result) => result.fmt(f),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SuccessVerifyByEnumerateRangeEndpointPosition {
    Start,
    End,
}

pub struct SuccessVerifyByEnumerateRangeEndpointResult {
    pub position: SuccessVerifyByEnumerateRangeEndpointPosition,
    pub endpoint: Obj,
    pub integer_membership_fact: Fact,
    pub verification: Box<StmtResult>,
}

pub struct SuccessVerifyByEnumerateRangeResult {
    pub element: Obj,
    pub range: ClosedRangeOrRange,
    pub membership_fact: Fact,
    pub generated_cases: Fact,
    pub membership_check: Box<StmtResult>,
    pub endpoint_checks: Vec<SuccessVerifyByEnumerateRangeEndpointResult>,
}

impl fmt::Debug for SuccessVerifyByEnumerateRangeEndpointResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByEnumerateRangeEndpointResult")
            .field("position", &self.position)
            .field("endpoint", &self.endpoint.to_string())
            .field(
                "integer_membership_fact",
                &self.integer_membership_fact.to_string(),
            )
            .field("verification", &self.verification)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyByEnumerateRangeResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByEnumerateRangeResult")
            .field("element", &self.element.to_string())
            .field("range", &self.range.to_string())
            .field("membership_fact", &self.membership_fact.to_string())
            .field("generated_cases", &self.generated_cases.to_string())
            .field("membership_check", &self.membership_check)
            .field("endpoint_checks", &self.endpoint_checks)
            .finish()
    }
}

pub struct SuccessVerifyByInducResult {
    pub parameter_binding: SymbolBinding,
    pub parameter: Obj,
    pub prove_goals: Vec<Fact>,
    pub generated_forall: ForallFact,
    pub proof: SuccessVerifyByInducProofResult,
}

#[derive(Debug)]
pub enum SuccessVerifyByInducProofResult {
    IntegerUnstructured(Box<SuccessVerifyByUnstructuredIntegerInducResult>),
    IntegerStructured(Box<SuccessVerifyByStructuredIntegerInducResult>),
    FiniteSet(Box<SuccessVerifyByFiniteSetInducResult>),
}

#[derive(Debug)]
pub struct SuccessVerifyByUnstructuredIntegerInducResult {
    pub strong: bool,
    pub start: String,
    pub base_assumptions: Vec<(String, String)>,
    pub step_assumptions: Vec<(String, String)>,
    pub proof_steps: Vec<StmtResult>,
    pub goals: Vec<SuccessVerifyByInducGoalResult>,
}

#[derive(Debug)]
pub struct SuccessVerifyByInducGoalResult {
    pub source_goal: Fact,
    pub base_check: Box<StmtResult>,
    pub start_in_z_check: Box<StmtResult>,
    pub step_check: Box<StmtResult>,
    pub infers: SuccessInferResult,
}

pub struct SuccessVerifyByStructuredIntegerInducResult {
    pub strong: bool,
    pub start: Obj,
    pub start_in_z_check: Box<StmtResult>,
    pub base: SuccessVerifyByStructuredIntegerInducCaseResult,
    pub step: SuccessVerifyByStructuredIntegerInducCaseResult,
}

impl fmt::Debug for SuccessVerifyByInducResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByInducResult")
            .field("parameter_binding", &self.parameter_binding)
            .field("parameter", &self.parameter.to_string())
            .field(
                "prove_goals",
                &self
                    .prove_goals
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>(),
            )
            .field("generated_forall", &self.generated_forall.to_string())
            .field("proof", &self.proof)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyByStructuredIntegerInducResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByStructuredIntegerInducResult")
            .field("strong", &self.strong)
            .field("start", &self.start.to_string())
            .field("start_in_z_check", &self.start_in_z_check)
            .field("base", &self.base)
            .field("step", &self.step)
            .finish()
    }
}

#[derive(Debug)]
pub struct SuccessVerifyByStructuredIntegerInducCaseResult {
    pub assumptions: Vec<SuccessVerifyByInducAssumptionResult>,
    pub assumption_infers: SuccessInferResult,
    pub proof_steps: Vec<StmtResult>,
    pub conclusions: Vec<SuccessVerifyByInducConclusionResult>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SuccessVerifyByInducAssumptionRole {
    ParameterType,
    BaseCaseEquality,
    DomainLowerBound,
    InductionHypothesis,
    StrongInductionHypothesis,
}

#[derive(Debug)]
pub struct SuccessVerifyByInducAssumptionResult {
    pub fact: Fact,
    pub fact_id: FactId,
    pub role: SuccessVerifyByInducAssumptionRole,
    pub goal_index: Option<usize>,
}

#[derive(Debug)]
pub struct SuccessVerifyByInducConclusionResult {
    pub goal: Fact,
    pub check: Box<StmtResult>,
}

#[derive(Debug)]
pub struct SuccessVerifyByFiniteSetInducResult {
    pub base: SuccessVerifyByInducCaseResult,
    pub step: SuccessVerifyByInducCaseResult,
}

#[derive(Debug)]
pub struct SuccessVerifyByInducCaseResult {
    pub assumptions: Vec<(String, String)>,
    pub proof_steps: Vec<StmtResult>,
    pub conclusion_checks: Vec<StmtResult>,
}

#[derive(Debug)]
pub struct SuccessVerifyByExtensionResult {
    pub left: String,
    pub right: String,
    pub prove_goal: String,
    pub left_to_right_subset: String,
    pub right_to_left_subset: String,
    pub proof_steps: Vec<StmtResult>,
    pub left_to_right_check: Box<StmtResult>,
    pub right_to_left_check: Box<StmtResult>,
}

pub struct SuccessVerifyByPropRegistrationResult {
    pub registration_type: String,
    pub prop_name: String,
    pub forall_fact: ForallFact,
    pub well_definedness: SuccessVerifyFactWellDefinedResult,
    pub assumption_infers: SuccessInferResult,
    pub proof_steps: Vec<StmtResult>,
    /// The complete recursive result returned by `verify_forall_fact`, not a
    /// flattened copy of its individual conclusions.
    pub forall_check: Box<StmtResult>,
}

#[derive(Debug)]
pub struct SuccessVerifyByChoiceResult {
    pub proof_type: String,
    pub target: String,
    pub proof_steps: Vec<StmtResult>,
    pub obligations: Vec<SuccessVerifyByChoiceObligationResult>,
    pub trusted_conclusion: String,
}

#[derive(Debug)]
pub struct SuccessVerifyByChoiceObligationResult {
    pub role: String,
    pub fact: String,
    pub check: Option<Box<StmtResult>>,
}

#[derive(Debug)]
pub struct SuccessVerifyByTheoremResult {
    pub theorem: String,
    pub theorem_source: String,
    /// Exact stored identity of the Litex theorem/axiom being instantiated.
    /// Builtin registered rules deliberately retain `None` and use their
    /// typed rule certificate instead.
    pub source_fact_id: Option<FactId>,
    pub mode: String,
    pub arguments: Vec<String>,
    pub domain_facts: Vec<String>,
    pub requirement_roles: Vec<String>,
    /// Exact instantiated direct conclusions returned by theorem execution.
    /// Consumers must use these structured facts rather than rediscovering a
    /// conclusion among inference outputs with string matching.
    pub direct_conclusions: Vec<Fact>,
    pub stored_then_facts: Vec<String>,
    pub temporary_then_facts: Vec<String>,
    pub selected_fact: Option<String>,
    pub parent_stored_facts: Vec<String>,
    pub provenance: Option<String>,
    pub argument_verification: Option<Box<SuccessVerifyArgsSatisfyParamDefResult>>,
    /// Checked premises for a registered builtin theorem, in the same order
    /// as `domain_facts` and `requirement_roles`.
    pub requirement_checks: Vec<StmtResult>,
    pub domain_checks: Vec<StmtResult>,
    pub selected_fact_check: Option<Box<StmtResult>>,
}

pub struct SuccessVerifyByDefinitionResult {
    pub prop: String,
    /// Exact concrete predicate definition selected by execution. Builtin
    /// definitions use `None` and are lowered by their own typed evidence.
    pub definition: Option<DefPropStmt>,
    pub arguments: Vec<String>,
    pub definition_clauses: Vec<String>,
    pub stored_fact: String,
    pub concrete_user_prop: bool,
    pub definition_clause_facts: Vec<Fact>,
    pub argument_verification: Option<Box<SuccessVerifyArgsSatisfyParamDefResult>>,
    pub clause_checks: Vec<StmtResult>,
}

impl fmt::Debug for SuccessVerifyByDefinitionResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByDefinitionResult")
            .field("prop", &self.prop)
            .field(
                "definition",
                &self.definition.as_ref().map(ToString::to_string),
            )
            .field("arguments", &self.arguments)
            .field("definition_clauses", &self.definition_clauses)
            .field("stored_fact", &self.stored_fact)
            .field("concrete_user_prop", &self.concrete_user_prop)
            .field("definition_clause_facts", &self.definition_clause_facts)
            .field("argument_verification", &self.argument_verification)
            .field("clause_checks", &self.clause_checks)
            .finish()
    }
}

#[derive(Clone, Debug)]
pub struct ObjectDefinitionItem {
    pub name: String,
    pub facts: Vec<Fact>,
}

#[derive(Debug)]
pub struct SuccessVerifyObjectChoiceResult {
    pub groups: Vec<SuccessVerifyObjectChoiceGroupResult>,
}

#[derive(Debug)]
pub struct SuccessVerifyObjectChoiceGroupResult {
    pub selected_type_facts: Vec<Fact>,
    pub nonempty_check: Option<Box<StmtResult>>,
}

impl SuccessVerifyObjectChoiceResult {
    pub fn new(groups: Vec<SuccessVerifyObjectChoiceGroupResult>) -> Self {
        SuccessVerifyObjectChoiceResult { groups }
    }
}

pub struct SuccessVerifyHaveObjEqualResult {
    pub type_checks: Vec<StmtResult>,
}

pub struct SuccessVerifyPreimageResult {
    pub source_membership_check: Box<StmtResult>,
}

pub struct SuccessVerifyTupleOrCartDimensionResult {
    pub positive_check: Box<StmtResult>,
    pub at_least_two_check: Box<StmtResult>,
}

/// Successful verification output shared by `have tuple` and `have cart`.
/// The value check is performed in the locally bound index environment, so
/// its recursive object result must be returned by that child layer before
/// the dimension checks are wrapped by the statement verifier.
pub struct SuccessVerifyTupleOrCartDefinitionResult {
    pub value_well_definedness: Rc<SuccessVerifyObjWellDefinedResult>,
    pub dimension: SuccessVerifyTupleOrCartDimensionResult,
}

pub struct SuccessVerifyIndexedFunctionDefinitionResult {
    pub well_definedness: SuccessVerifyIndexedFunctionDefinitionWellDefinedResult,
    pub bound_checks: Vec<StmtResult>,
    /// Parameter-membership and domain facts installed while checking the
    /// indexed body, with their temporary FactIds frozen before that local
    /// Runtime environment closes.
    pub assumption_infers: SuccessInferResult,
    pub return_check: Box<StmtResult>,
}

/// The three object checks performed by the shared sequence/finite-sequence/
/// matrix definition layer. Keeping them named prevents the statement result
/// from collapsing constructor-specific WD work into an untyped vector.
pub struct SuccessVerifyIndexedFunctionDefinitionWellDefinedResult {
    pub surface_set: Rc<SuccessVerifyObjWellDefinedResult>,
    pub anonymous_function: Rc<SuccessVerifyObjWellDefinedResult>,
    pub function_set: Rc<SuccessVerifyObjWellDefinedResult>,
}

pub struct SuccessVerifyCaseFunctionDefinitionResult {
    pub coverage_check: Box<StmtResult>,
    pub return_checks: Vec<StmtResult>,
}

pub struct SuccessVerifyFunctionFromUniqueExistenceResult {
    pub source_forall_check: Option<Box<StmtResult>>,
    pub proof_steps: Vec<StmtResult>,
    pub conclusion_checks: Vec<StmtResult>,
}

pub struct SuccessVerifyStrategyDefinitionResult {
    pub name: String,
    pub forall_fact: ForallFact,
    pub well_definedness: SuccessVerifyFactWellDefinedResult,
    pub proof_scope: SuccessVerifyLocalProofScopeResult,
    pub proof_steps: Vec<StmtResult>,
    pub conclusion_checks: Vec<StmtResult>,
}

impl SuccessVerifyStrategyDefinitionResult {
    pub fn new(
        name: String,
        forall_fact: ForallFact,
        well_definedness: SuccessVerifyFactWellDefinedResult,
        proof_scope: SuccessVerifyLocalProofScopeResult,
        proof_steps: Vec<StmtResult>,
        conclusion_checks: Vec<StmtResult>,
    ) -> Self {
        Self {
            name,
            forall_fact,
            well_definedness,
            proof_scope,
            proof_steps,
            conclusion_checks,
        }
    }
}

#[derive(Debug)]
pub struct SuccessVerifyWitnessExistResult {
    pub proof_steps: Vec<StmtResult>,
    /// One factual type-check result for every witness value that contributes
    /// a target-side existential requirement.  Plain `set` binders need no
    /// separate target proposition because every value already has type
    /// `LitexSet`.
    pub parameter_checks: Vec<Option<Box<StmtResult>>>,
    /// One factual result for every direct existential body fact.
    pub body_checks: Vec<StmtResult>,
    /// The final result for the uniqueness obligation, when the source form
    /// is `exist!`.
    pub uniqueness_check: Option<Box<StmtResult>>,
}

pub struct SuccessVerifyWitnessAtomicFactResult {
    pub definition: DefPropStmt,
    pub instantiated_existential: ExistFactEnum,
    pub definition_parameter_verification: Box<SuccessVerifyArgsSatisfyParamDefResult>,
    pub witness_verification: SuccessVerifyWitnessExistResult,
}

impl SuccessVerifyWitnessAtomicFactResult {
    pub fn new(
        definition: DefPropStmt,
        instantiated_existential: ExistFactEnum,
        definition_parameter_verification: SuccessVerifyArgsSatisfyParamDefResult,
        witness_verification: SuccessVerifyWitnessExistResult,
    ) -> Self {
        SuccessVerifyWitnessAtomicFactResult {
            definition,
            instantiated_existential,
            definition_parameter_verification: Box::new(definition_parameter_verification),
            witness_verification,
        }
    }
}

impl fmt::Debug for SuccessVerifyWitnessAtomicFactResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyWitnessAtomicFactResult")
            .field("definition", &self.definition.name)
            .field(
                "instantiated_existential",
                &self.instantiated_existential.to_string(),
            )
            .field(
                "definition_parameter_verification",
                &self.definition_parameter_verification,
            )
            .field("witness_verification", &self.witness_verification)
            .finish()
    }
}

impl SuccessVerifyWitnessExistResult {
    pub fn new(
        proof_steps: Vec<StmtResult>,
        parameter_checks: Vec<Option<Box<StmtResult>>>,
        body_checks: Vec<StmtResult>,
        uniqueness_check: Option<StmtResult>,
    ) -> Self {
        Self {
            proof_steps,
            parameter_checks,
            body_checks,
            uniqueness_check: uniqueness_check.map(Box::new),
        }
    }
}

pub struct SuccessVerifyExistentialEliminationResult {
    /// Checked existential/projection or scoped theorem application whose
    /// exact direct conclusion is retained recursively.
    pub source_result: Box<StmtResult>,
    /// Exact existential eliminated after any definition projection.
    pub source_exist_fact: ExistFactEnum,
    /// Exact instantiated type fact stored for every introduced witness.
    pub witness_type_facts: Vec<Fact>,
    /// Exact instantiated direct body facts stored by elimination.
    pub instantiated_body_facts: Vec<Fact>,
    /// `exist!` additionally stores a generated uniqueness theorem.  The
    /// current compiler tranche rejects that extra projection explicitly.
    pub includes_uniqueness: bool,
}

impl fmt::Debug for SuccessVerifyExistentialEliminationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyExistentialEliminationResult")
            .field("source_result", &self.source_result)
            .field("source_exist_fact", &self.source_exist_fact.to_string())
            .field("witness_type_facts", &self.witness_type_facts)
            .field("instantiated_body_facts", &self.instantiated_body_facts)
            .field("includes_uniqueness", &self.includes_uniqueness)
            .finish()
    }
}

impl SuccessVerifyExistentialEliminationResult {
    pub fn new(
        source_result: StmtResult,
        source_exist_fact: ExistFactEnum,
        witness_type_facts: Vec<Fact>,
        instantiated_body_facts: Vec<Fact>,
        includes_uniqueness: bool,
    ) -> Self {
        Self {
            source_result: Box::new(source_result),
            source_exist_fact,
            witness_type_facts,
            instantiated_body_facts,
            includes_uniqueness,
        }
    }
}

#[derive(Debug)]
pub struct SuccessBuiltinFactProofResult {
    pub msg: String,
    pub evidence: SuccessBuiltinFactProofEvidenceResult,
    pub subgoals: Vec<StmtResult>,
}

#[derive(Debug)]
pub enum SuccessBuiltinFactProofEvidenceResult {
    Typed(BuiltinRuleEvidence),
    DiagnosticOnly,
}

impl SuccessBuiltinFactProofEvidenceResult {
    pub fn typed(&self) -> Option<&BuiltinRuleEvidence> {
        match self {
            Self::Typed(evidence) => Some(evidence),
            Self::DiagnosticOnly => None,
        }
    }

    pub fn typed_mut(&mut self) -> Option<&mut BuiltinRuleEvidence> {
        match self {
            Self::Typed(evidence) => Some(evidence),
            Self::DiagnosticOnly => None,
        }
    }

    pub fn is_typed(&self) -> bool {
        matches!(self, Self::Typed(_))
    }
}

#[derive(Clone, Debug)]
pub struct EqualityTransportEvidence {
    pub steps: Vec<EqualityTransportStep>,
}

impl EqualityTransportEvidence {
    pub fn new(steps: Vec<EqualityTransportStep>) -> Self {
        Self { steps }
    }
}

#[derive(Clone)]
pub struct EqualityTransportStep {
    pub from: Obj,
    pub to: Obj,
    pub equality: EqualFact,
    pub equality_fact_id: FactId,
}

impl EqualityTransportStep {
    pub fn new(from: Obj, to: Obj, equality: EqualFact, equality_fact_id: FactId) -> Self {
        Self {
            from,
            to,
            equality,
            equality_fact_id,
        }
    }
}

#[derive(Clone, Debug)]
pub struct FactTransformationEvidence {
    /// Proposition proved before the first transformation step.
    pub source: Fact,
    /// Ordered in proof-construction direction: cited source toward the goal.
    pub steps: Vec<FactTransformationStep>,
}

impl FactTransformationEvidence {
    pub fn new(source: Fact, steps: Vec<FactTransformationStep>) -> Self {
        Self { source, steps }
    }
}

#[derive(Clone, Debug)]
pub struct FactTransformationStep {
    /// Proposition available after applying this step.
    pub result: Fact,
    pub rule: FactTransformationRule,
}

impl FactTransformationStep {
    pub fn new(result: Fact, rule: FactTransformationRule) -> Self {
        Self { result, rule }
    }
}

#[derive(Clone, Debug)]
pub enum FactTransformationRule {
    EqualityRewrite(EqualityTransportEvidence),
    RationalNormalization,
}

/// One target-directed fact transformation. The enclosing
/// `SuccessVerifyFactResult` owns the target proposition; this node owns the
/// immediately preceding successful fact result and the exact rule used for
/// the single transformation layer.
#[derive(Debug)]
pub struct SuccessTransformFactResult {
    pub rule: FactTransformationRule,
    pub source: Rc<SuccessVerifyFactResult>,
}

impl SuccessTransformFactResult {
    pub fn new(rule: FactTransformationRule, source: SuccessVerifyFactResult) -> Self {
        Self {
            rule,
            source: Rc::new(source),
        }
    }

    pub fn from_shared(rule: FactTransformationRule, source: Rc<SuccessVerifyFactResult>) -> Self {
        Self { rule, source }
    }
}

impl fmt::Debug for EqualityTransportStep {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("EqualityTransportStep")
            .field("from", &self.from.to_string())
            .field("to", &self.to.to_string())
            .field("equality", &self.equality.to_string())
            .field("equality_fact_id", &self.equality_fact_id)
            .finish()
    }
}

#[derive(Clone, Debug)]
pub struct SuccessStoredFactCitationProofResult {
    pub detail: Option<String>,
    pub source_fact: Fact,
    pub source_fact_id: FactId,
}

pub struct SuccessDefinitionReductionFactProofResult {
    pub detail: Option<String>,
    pub definition: DefPropStmt,
    pub verification: Rc<DefinitionReductionVerificationEvidence>,
}

impl fmt::Debug for SuccessDefinitionReductionFactProofResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("SuccessDefinitionReductionFactProofResult")
            .field("detail", &self.detail)
            .field("definition", &self.definition.to_string())
            .field("verification", &self.verification)
            .finish()
    }
}

#[derive(Clone, Debug)]
pub struct SuccessCheckedFunctionDefinitionReductionFactProofResult {
    pub detail: Option<String>,
    pub verification: CheckedFunctionDefinitionReductionEvidence,
}

#[derive(Clone, Debug)]
pub struct SuccessDiagnosticFactProofResult {
    pub detail: String,
}

#[derive(Debug)]
pub struct DefinitionReductionVerificationEvidence {
    pub argument_verification: SuccessVerifyArgsSatisfyParamDefResult,
    pub clause_facts: Vec<Fact>,
    pub clause_checks: Vec<StmtResult>,
}

#[derive(Clone)]
pub struct CheckedFunctionDefinitionReductionEvidence {
    pub definition_object: Obj,
    pub defining_equality: Fact,
    pub defining_equality_fact_id: FactId,
    pub application_side: Obj,
    pub reduced: Obj,
    pub other_side: Obj,
    pub application_is_left: bool,
    pub reduced_matches_other_by_alpha: bool,
}

impl fmt::Debug for CheckedFunctionDefinitionReductionEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("CheckedFunctionDefinitionReductionEvidence")
            .field("definition_object", &self.definition_object.to_string())
            .field("defining_equality", &self.defining_equality.to_string())
            .field("defining_equality_fact_id", &self.defining_equality_fact_id)
            .field("application_side", &self.application_side.to_string())
            .field("reduced", &self.reduced.to_string())
            .field("other_side", &self.other_side.to_string())
            .field("application_is_left", &self.application_is_left)
            .field(
                "reduced_matches_other_by_alpha",
                &self.reduced_matches_other_by_alpha,
            )
            .finish()
    }
}

pub struct KnownForallInstantiationItem {
    pub param: String,
    pub arg: String,
    /// Typed verifier output retained for compilers. `arg` remains the stable
    /// user-facing rendering used by existing diagnostics and JSON.
    pub arg_obj: Obj,
}

impl fmt::Debug for KnownForallInstantiationItem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("KnownForallInstantiationItem")
            .field("param", &self.param)
            .field("arg", &self.arg)
            .finish()
    }
}

#[derive(Debug)]
pub struct SuccessVerifyKnownForallRequirementResult {
    pub stmt: Fact,
    pub result: Box<StmtResult>,
    pub kind: KnownForallRequirementKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KnownForallRequirementKind {
    ParameterType,
    Domain,
}

#[derive(Debug)]
pub struct SuccessInstantiateKnownForallResult {
    pub source_fact: Fact,
    pub source_fact_id: FactId,
    pub source_conclusion_location: ForallConclusionLocation,
    pub instantiation: Vec<KnownForallInstantiationItem>,
    pub requirements: Vec<SuccessVerifyKnownForallRequirementResult>,
}

#[derive(Debug)]
pub struct SuccessCombinedFactProofResult {
    pub primary: Option<Rc<SuccessVerifyFactResult>>,
    pub steps: Vec<StmtResult>,
}

pub struct SuccessForallProofResult {
    pub forall_fact: ForallFact,
    /// Exact parameter facts visible in the proof-owned lexical environment.
    /// These are proof-scope identities, not the sibling WD check identities.
    pub parameter_assumptions: Vec<SuccessForallAssumptionFactResult>,
    /// Exact source-domain facts visible after the parameters. A repeated
    /// domain premise intentionally reuses the earlier parameter FactId.
    pub domain_assumptions: Vec<SuccessForallAssumptionFactResult>,
    pub assumption_infers: SuccessInferResult,
    pub proves: Vec<SuccessForallProvedFactResult>,
}

#[derive(Clone, Debug)]
pub struct SuccessForallAssumptionFactResult {
    pub fact: Fact,
    pub fact_id: FactId,
}

pub struct SuccessForallProvedFactResult {
    pub stmt: ExistOrAndChainAtomicFact,
    pub result: Box<StmtResult>,
}

#[derive(Debug)]
pub struct SuccessReuseFactProofResult {
    pub source: Rc<SuccessVerifyFactResult>,
}

#[derive(Debug)]
pub enum SuccessFactProofResult {
    BuiltinRule(SuccessBuiltinFactProofResult),
    BuiltinStrategy(SuccessBuiltinFactProofResult),
    StoredFactCitation(SuccessStoredFactCitationProofResult),
    KnownForallInstantiation(SuccessInstantiateKnownForallResult),
    DefinitionReduction(SuccessDefinitionReductionFactProofResult),
    CheckedFunctionDefinitionReduction(SuccessCheckedFunctionDefinitionReductionFactProofResult),
    DiagnosticOnly(SuccessDiagnosticFactProofResult),
    CombinedProofs(SuccessCombinedFactProofResult),
    ForallProof(SuccessForallProofResult),
    Transform(Box<SuccessTransformFactResult>),
    /// Internal proof sharing; this is not a user-visible verification method.
    Reuse(Box<SuccessReuseFactProofResult>),
}
