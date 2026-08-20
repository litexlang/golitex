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
    pub assumptions: Vec<(String, String)>,
    pub domain_checks: Vec<SuccessVerifyByAssignmentDomainResult>,
    pub proof_steps: Vec<StmtResult>,
    pub conclusion_checks: Vec<StmtResult>,
}

#[derive(Debug)]
pub struct SuccessVerifyByAssignmentDomainResult {
    pub fact: Fact,
    pub check: Box<StmtResult>,
    pub negated_check: Option<Box<StmtResult>>,
    pub satisfied: bool,
}

#[derive(Debug)]
pub struct SuccessVerifyByEnumerateFiniteSetResult {
    pub parameters: Vec<String>,
    pub parameter_sets: Vec<String>,
    pub prove_goal: String,
    pub assignments: Vec<SuccessVerifyByAssignmentResult>,
    pub generated_forall: String,
}

#[derive(Debug)]
pub struct SuccessVerifyByForResult {
    pub iteration_mode: String,
    pub parameters: Vec<String>,
    pub domains: Vec<String>,
    pub prove_goal: String,
    pub assignments: Vec<SuccessVerifyByAssignmentResult>,
    pub generated_forall: String,
}

#[derive(Debug)]
pub struct SuccessVerifyByEnumerateRangeResult {
    pub proof_type: String,
    pub element: String,
    pub range: String,
    pub membership_fact: String,
    pub endpoint_facts: Vec<String>,
    pub generated_cases: String,
    pub membership_check: Box<StmtResult>,
    pub endpoint_checks: Vec<StmtResult>,
}

#[derive(Debug)]
pub struct SuccessVerifyByInducResult {
    pub parameter: String,
    pub prove_goals: Vec<String>,
    pub generated_forall: String,
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

#[derive(Debug)]
pub struct SuccessVerifyByStructuredIntegerInducResult {
    pub strong: bool,
    pub start: String,
    pub start_in_z_check: Box<StmtResult>,
    pub base: SuccessVerifyByInducCaseResult,
    pub step: SuccessVerifyByInducCaseResult,
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
    pub assumption_infers: SuccessInferResult,
    pub proof_steps: Vec<StmtResult>,
    pub conclusion_check: Box<StmtResult>,
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
pub struct ObjectIntroductionItem {
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

pub struct SuccessVerifyIndexedFunctionDefinitionResult {
    pub bound_checks: Vec<StmtResult>,
    pub return_check: Box<StmtResult>,
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
    pub proof_steps: Vec<StmtResult>,
    pub conclusion_checks: Vec<StmtResult>,
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
    /// Structured verifier-side bindings retained for compiler backends.
    /// `None` means this rule still has only its diagnostic label.
    pub evidence: Option<BuiltinRuleEvidence>,
    pub subgoals: Vec<StmtResult>,
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
    /// `None` means verification used an equality whose compiler proof
    /// provenance is not represented yet.
    pub equality_fact_id: Option<FactId>,
}

impl EqualityTransportStep {
    pub fn new(from: Obj, to: Obj, equality: EqualFact, equality_fact_id: Option<FactId>) -> Self {
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
pub struct SuccessFactCitationProofResult {
    pub detail: Option<String>,
    pub cite_what: Box<Stmt>,
    /// Captured while the cited fact's environment is still alive.
    pub source_fact_id: Option<FactId>,
    /// `Some` means the verifier reached the goal by rewriting the cited fact
    /// along these checked equality edges. `None` means no structured
    /// transport evidence was recorded for this citation route.
    pub equality_transport: Option<EqualityTransportEvidence>,
    /// Additional checked transformations discovered while resolving the
    /// requested fact to the cited fact. These are stored source-to-goal even
    /// though the verifier searched goal-to-source.
    pub fact_transformation: Option<FactTransformationEvidence>,
    /// Exact source retained when equality verification unfolded one checked
    /// named function definition. This is distinct from an ordinary citation:
    /// the goal itself may only exist in a temporary forall scope.
    pub checked_function_definition_reduction: Option<CheckedFunctionDefinitionReductionEvidence>,
    /// Exact parameter and clause checks used when a concrete `prop` was
    /// folded. Keeping the successful child results here lets compiler
    /// backends replay the verifier-selected route instead of proving the
    /// definition body again in the target.
    pub definition_reduction: Option<Rc<DefinitionReductionVerificationEvidence>>,
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
    pub cite_what: Box<Stmt>,
    /// Captured while the source forall's environment is still alive.
    pub source_fact_id: Option<FactId>,
    pub instantiation: Vec<KnownForallInstantiationItem>,
    pub requirements: Vec<SuccessVerifyKnownForallRequirementResult>,
}

#[derive(Debug)]
pub struct SuccessCombinedFactProofResult {
    pub cite_what: Vec<SuccessCombinedFactProofItemResult>,
}

pub struct SuccessForallProofResult {
    pub forall_fact: ForallFact,
    pub assumption_infers: SuccessInferResult,
    pub proves: Vec<SuccessForallProvedFactResult>,
}

pub struct SuccessForallProvedFactResult {
    pub stmt: ExistOrAndChainAtomicFact,
    pub result: Box<StmtResult>,
}

#[derive(Debug)]
pub struct SuccessCombinedBuiltinFactProofResult {
    pub msg: String,
    pub verify_what: Fact,
    pub evidence: Option<BuiltinRuleEvidence>,
    pub subgoals: Vec<StmtResult>,
}

#[derive(Debug)]
pub struct SuccessCombinedFactCitationProofResult {
    pub detail: Option<String>,
    pub verify_what: Fact,
    pub cite_what: Box<Stmt>,
    pub source_fact_id: Option<FactId>,
    pub equality_transport: Option<EqualityTransportEvidence>,
    pub fact_transformation: Option<FactTransformationEvidence>,
    pub definition_reduction: Option<Rc<DefinitionReductionVerificationEvidence>>,
}

#[derive(Debug)]
pub struct SuccessCombinedKnownForallProofResult {
    pub verify_what: Fact,
    pub result: SuccessInstantiateKnownForallResult,
}

#[derive(Debug)]
pub struct SuccessCombinedReuseFactProofResult {
    pub statement: Fact,
    pub source: Rc<SuccessVerifyFactResult>,
}

#[derive(Debug)]
pub struct SuccessReuseFactProofResult {
    pub source: Rc<SuccessVerifyFactResult>,
}

#[derive(Debug)]
pub enum SuccessCombinedFactProofItemResult {
    ByBuiltinRule(SuccessCombinedBuiltinFactProofResult),
    ByBuiltinStrategy(SuccessCombinedBuiltinFactProofResult),
    ByFact(SuccessCombinedFactCitationProofResult),
    ByKnownForall(SuccessCombinedKnownForallProofResult),
    /// Internal proof sharing; output and dependency analysis expose the source proof.
    Reuse(Box<SuccessCombinedReuseFactProofResult>),
}

#[derive(Debug)]
pub enum SuccessFactProofResult {
    BuiltinRule(SuccessBuiltinFactProofResult),
    BuiltinStrategy(SuccessBuiltinFactProofResult),
    Fact(SuccessFactCitationProofResult),
    KnownForallInstantiation(SuccessInstantiateKnownForallResult),
    CombinedProofs(SuccessCombinedFactProofResult),
    ForallProof(SuccessForallProofResult),
    Transform(Box<SuccessTransformFactResult>),
    /// Internal proof sharing; this is not a user-visible verification method.
    Reuse(Box<SuccessReuseFactProofResult>),
}

impl SuccessFactStmtResult {
    pub fn new_with_verified_by_builtin_rules(
        stmt: Fact,
        infers: SuccessInferResult,
        verified_by: SuccessFactProofResult,
    ) -> Self {
        Self::new(stmt, infers, verified_by)
    }

    pub fn new_with_verified_by_builtin_rules_recording_stmt(
        stmt: Fact,
        builtin_rule_label: String,
        step_results: Vec<StmtResult>,
    ) -> Self {
        let infers = SuccessInferResult::new();
        let verified_by =
            SuccessFactProofResult::builtin_rule_with_subgoals(builtin_rule_label, step_results);
        Self::new_with_verified_by_builtin_rules(stmt, infers, verified_by)
    }

    pub fn new_with_verified_by_builtin_strategy_recording_stmt(
        stmt: Fact,
        strategy_label: String,
        step_results: Vec<StmtResult>,
    ) -> Self {
        let verified_by = SuccessFactProofResult::BuiltinStrategy(SuccessBuiltinFactProofResult {
            msg: strategy_label,
            evidence: None,
            subgoals: step_results,
        });
        Self::new_with_verified_by_builtin_rules(stmt, SuccessInferResult::new(), verified_by)
    }

    pub fn new_with_verified_by_builtin_strategy_evidence_recording_stmt(
        stmt: Fact,
        strategy_label: String,
        evidence: BuiltinRuleEvidence,
        step_results: Vec<StmtResult>,
    ) -> Self {
        let verified_by = SuccessFactProofResult::BuiltinStrategy(SuccessBuiltinFactProofResult {
            msg: strategy_label,
            evidence: Some(evidence),
            subgoals: step_results,
        });
        Self::new_with_verified_by_builtin_rules(stmt, SuccessInferResult::new(), verified_by)
    }

    pub fn new_with_verified_by_builtin_rules_label_and_steps(
        stmt: Fact,
        infers: SuccessInferResult,
        builtin_rule_label: String,
        step_results: Vec<StmtResult>,
    ) -> Self {
        let verified_by =
            SuccessFactProofResult::builtin_rule_with_subgoals(builtin_rule_label, step_results);
        Self::new_with_verified_by_builtin_rules(stmt, infers, verified_by)
    }

    pub fn new_with_verified_by_builtin_rule_evidence_and_steps(
        stmt: Fact,
        infers: SuccessInferResult,
        builtin_rule_label: String,
        evidence: BuiltinRuleEvidence,
        step_results: Vec<StmtResult>,
    ) -> Self {
        let verified_by = SuccessFactProofResult::builtin_rule_with_evidence(
            builtin_rule_label,
            evidence,
            step_results,
        );
        Self::new_with_verified_by_builtin_rules(stmt, infers, verified_by)
    }

    pub fn new_with_verified_by_builtin_rule_evidence_recording_stmt(
        stmt: Fact,
        builtin_rule_label: String,
        evidence: BuiltinRuleEvidence,
        step_results: Vec<StmtResult>,
    ) -> Self {
        Self::new_with_verified_by_builtin_rule_evidence_and_steps(
            stmt,
            SuccessInferResult::new(),
            builtin_rule_label,
            evidence,
            step_results,
        )
    }

    pub fn new_with_verified_by_known_fact_and_infer(
        stmt: Fact,
        infers: SuccessInferResult,
        verified_by: SuccessFactProofResult,
        step_results: Vec<StmtResult>,
    ) -> Self {
        let verified_by = merge_verified_by_with_steps(stmt.clone(), verified_by, step_results);
        Self::new(stmt, infers, verified_by)
    }

    pub fn new_with_verified_by_known_fact(
        stmt: Fact,
        verified_by: SuccessFactProofResult,
        step_results: Vec<StmtResult>,
    ) -> Self {
        Self::new_with_verified_by_known_fact_and_infer(
            stmt,
            SuccessInferResult::new(),
            verified_by,
            step_results,
        )
    }

    pub fn new_with_statement_memo(
        stmt: Fact,
        infers: SuccessInferResult,
        source: Rc<SuccessVerifyFactResult>,
    ) -> Self {
        Self::new_with_verified_by_builtin_rules(
            stmt,
            infers,
            SuccessFactProofResult::Reuse(Box::new(SuccessReuseFactProofResult { source })),
        )
    }

    pub fn is_verified_by_builtin_rules_only(&self) -> bool {
        self.proof().tree_is_builtin_rules_only()
    }

    pub(crate) fn underlying_verified_by(&self) -> &SuccessFactProofResult {
        let mut proof = self.proof();
        loop {
            match proof {
                SuccessFactProofResult::Reuse(result) => proof = result.source.proof(),
                verified_by => return verified_by,
            }
        }
    }
}

impl SuccessFactProofResult {
    pub fn builtin_rule(msg: impl Into<String>) -> Self {
        Self::builtin_rule_with_subgoals(msg, Vec::new())
    }

    pub fn builtin_rule_with_subgoals(msg: impl Into<String>, subgoals: Vec<StmtResult>) -> Self {
        Self::BuiltinRule(SuccessBuiltinFactProofResult {
            msg: msg.into(),
            evidence: None,
            subgoals,
        })
    }

    pub fn builtin_rule_with_evidence(
        msg: impl Into<String>,
        evidence: BuiltinRuleEvidence,
        subgoals: Vec<StmtResult>,
    ) -> Self {
        Self::BuiltinRule(SuccessBuiltinFactProofResult {
            msg: msg.into(),
            evidence: Some(evidence),
            subgoals,
        })
    }

    pub fn cited_fact(_goal: Fact, cite_what: Fact, detail: Option<String>) -> Self {
        Self::cited_stmt(_goal, cite_what.into_stmt(), detail)
    }

    pub fn cited_stmt(_goal: Fact, cite_what: Stmt, detail: Option<String>) -> Self {
        Self::Fact(SuccessFactCitationProofResult {
            detail,
            cite_what: Box::new(cite_what),
            source_fact_id: None,
            equality_transport: None,
            fact_transformation: None,
            checked_function_definition_reduction: None,
            definition_reduction: None,
        })
    }

    pub fn cited_definition(
        _goal: Fact,
        definition: DefPropStmt,
        argument_verification: SuccessVerifyArgsSatisfyParamDefResult,
        clause_checks: Vec<(Fact, StmtResult)>,
        detail: Option<String>,
    ) -> Self {
        let (clause_facts, clause_checks) = clause_checks.into_iter().unzip();
        Self::Fact(SuccessFactCitationProofResult {
            detail,
            cite_what: Box::new(definition.clone().into()),
            source_fact_id: None,
            equality_transport: None,
            fact_transformation: None,
            checked_function_definition_reduction: None,
            definition_reduction: Some(Rc::new(DefinitionReductionVerificationEvidence {
                argument_verification,
                clause_facts,
                clause_checks,
            })),
        })
    }

    pub fn cited_fact_with_provenance(
        _goal: Fact,
        cite_what: Fact,
        source_fact_id: Option<FactId>,
        equality_transport: Option<EqualityTransportEvidence>,
        fact_transformation: Option<FactTransformationEvidence>,
        detail: Option<String>,
    ) -> Self {
        Self::Fact(SuccessFactCitationProofResult {
            detail,
            cite_what: Box::new(cite_what.into_stmt()),
            source_fact_id,
            equality_transport,
            fact_transformation,
            checked_function_definition_reduction: None,
            definition_reduction: None,
        })
    }

    pub fn known_forall_instantiation(
        cite_what: Fact,
        source_fact_id: Option<FactId>,
        instantiation: Vec<KnownForallInstantiationItem>,
        requirements: Vec<SuccessVerifyKnownForallRequirementResult>,
    ) -> Self {
        Self::KnownForallInstantiation(SuccessInstantiateKnownForallResult::new(
            cite_what.into_stmt(),
            source_fact_id,
            instantiation,
            requirements,
        ))
    }

    /// Same statement as goal and citation; optional human note in `msg`.
    pub fn fact_with_note(goal: Fact, msg: Option<String>) -> Self {
        let cite_what = goal.clone();
        Self::cited_fact(goal, cite_what, msg)
    }

    pub fn fact_with_checked_function_definition_reduction(
        goal: Fact,
        evidence: CheckedFunctionDefinitionReductionEvidence,
        detail: Option<String>,
    ) -> Self {
        let cite_what = goal.clone().into_stmt();
        Self::Fact(SuccessFactCitationProofResult {
            detail,
            cite_what: Box::new(cite_what),
            source_fact_id: None,
            equality_transport: None,
            fact_transformation: None,
            checked_function_definition_reduction: Some(evidence),
            definition_reduction: None,
        })
    }

    pub fn cached_fact(fact: Fact, cite_fact_source: LineFile, source_fact_id: FactId) -> Self {
        let cite_what = fact.with_line_file(cite_fact_source);
        Self::Fact(SuccessFactCitationProofResult {
            detail: None,
            cite_what: Box::new(cite_what.into_stmt()),
            source_fact_id: Some(source_fact_id),
            equality_transport: None,
            fact_transformation: None,
            checked_function_definition_reduction: None,
            definition_reduction: None,
        })
    }

    pub fn wrap_bys(children: Vec<SuccessCombinedFactProofItemResult>) -> Self {
        Self::CombinedProofs(SuccessCombinedFactProofResult {
            cite_what: children,
        })
    }

    pub fn forall_proof(
        forall_fact: ForallFact,
        then_results: Vec<StmtResult>,
        assumption_infers: SuccessInferResult,
    ) -> Self {
        let mut proves = Vec::new();
        for (stmt, result) in forall_fact
            .then_facts
            .iter()
            .cloned()
            .zip(then_results.into_iter())
        {
            proves.push(SuccessForallProvedFactResult::new(stmt, result));
        }
        Self::ForallProof(SuccessForallProofResult::new(
            forall_fact,
            assumption_infers,
            proves,
        ))
    }

    pub fn tree_is_builtin_rules_only(&self) -> bool {
        match self {
            SuccessFactProofResult::BuiltinRule(r) | SuccessFactProofResult::BuiltinStrategy(r) => {
                !r.msg.is_empty()
            }
            SuccessFactProofResult::Fact(_) => false,
            SuccessFactProofResult::KnownForallInstantiation(_) => false,
            SuccessFactProofResult::CombinedProofs(w) => {
                !w.cite_what.is_empty() && w.cite_what.iter().all(|b| b.is_builtin_rule())
            }
            SuccessFactProofResult::ForallProof(_) => false,
            SuccessFactProofResult::Transform(result) => {
                result.source.proof().tree_is_builtin_rules_only()
            }
            SuccessFactProofResult::Reuse(result) => {
                result.source.is_verified_by_builtin_rules_only()
            }
        }
    }
}

impl SuccessCombinedFactProofItemResult {
    pub fn builtin_rule(msg: String, verify_what: Fact, subgoals: Vec<StmtResult>) -> Self {
        Self::builtin_rule_with_evidence(msg, verify_what, None, subgoals)
    }

    fn builtin_rule_with_evidence(
        msg: String,
        verify_what: Fact,
        evidence: Option<BuiltinRuleEvidence>,
        subgoals: Vec<StmtResult>,
    ) -> Self {
        SuccessCombinedFactProofItemResult::ByBuiltinRule(SuccessCombinedBuiltinFactProofResult {
            msg,
            verify_what,
            evidence,
            subgoals,
        })
    }

    pub fn builtin_strategy(msg: String, verify_what: Fact, subgoals: Vec<StmtResult>) -> Self {
        Self::builtin_strategy_with_evidence(msg, verify_what, None, subgoals)
    }

    fn builtin_strategy_with_evidence(
        msg: String,
        verify_what: Fact,
        evidence: Option<BuiltinRuleEvidence>,
        subgoals: Vec<StmtResult>,
    ) -> Self {
        SuccessCombinedFactProofItemResult::ByBuiltinStrategy(
            SuccessCombinedBuiltinFactProofResult {
                msg,
                verify_what,
                evidence,
                subgoals,
            },
        )
    }

    pub fn cited_fact(verify_what: Fact, cite_what: Fact, detail: Option<String>) -> Self {
        Self::cited_stmt(verify_what, cite_what.into_stmt(), detail)
    }

    pub fn cited_stmt(verify_what: Fact, cite_what: Stmt, detail: Option<String>) -> Self {
        SuccessCombinedFactProofItemResult::ByFact(SuccessCombinedFactCitationProofResult {
            detail,
            verify_what,
            cite_what: Box::new(cite_what),
            source_fact_id: None,
            equality_transport: None,
            fact_transformation: None,
            definition_reduction: None,
        })
    }

    pub fn known_forall_instantiation(
        verify_what: Fact,
        result: SuccessInstantiateKnownForallResult,
    ) -> Self {
        SuccessCombinedFactProofItemResult::ByKnownForall(SuccessCombinedKnownForallProofResult {
            verify_what,
            result,
        })
    }

    pub fn fact_with_note(verify_what: Fact, msg: Option<String>) -> Self {
        let cite_what = verify_what.clone();
        Self::cited_fact(verify_what, cite_what, msg)
    }

    fn from_verified_by_result(
        verify_what: Fact,
        verified_by: SuccessFactProofResult,
    ) -> Vec<Self> {
        match verified_by {
            SuccessFactProofResult::BuiltinRule(r) => {
                vec![Self::builtin_rule_with_evidence(
                    r.msg,
                    verify_what,
                    r.evidence,
                    r.subgoals,
                )]
            }
            SuccessFactProofResult::BuiltinStrategy(r) => {
                vec![Self::builtin_strategy_with_evidence(
                    r.msg,
                    verify_what,
                    r.evidence,
                    r.subgoals,
                )]
            }
            SuccessFactProofResult::Fact(r) => {
                vec![SuccessCombinedFactProofItemResult::ByFact(
                    SuccessCombinedFactCitationProofResult {
                        detail: r.detail,
                        verify_what,
                        cite_what: r.cite_what,
                        source_fact_id: r.source_fact_id,
                        equality_transport: r.equality_transport,
                        fact_transformation: r.fact_transformation,
                        definition_reduction: r.definition_reduction,
                    },
                )]
            }
            SuccessFactProofResult::KnownForallInstantiation(r) => {
                vec![Self::known_forall_instantiation(verify_what, r)]
            }
            SuccessFactProofResult::CombinedProofs(w) => w.cite_what,
            SuccessFactProofResult::ForallProof(_) => {
                vec![Self::fact_with_note(
                    verify_what,
                    Some("forall proof".to_string()),
                )]
            }
            SuccessFactProofResult::Transform(result) => {
                let source_fact = result.source.fact();
                let mut items = vec![SuccessCombinedFactProofItemResult::Reuse(Box::new(
                    SuccessCombinedReuseFactProofResult {
                        statement: source_fact,
                        source: result.source,
                    },
                ))];
                items.push(Self::fact_with_note(
                    verify_what,
                    Some("fact transformation".to_string()),
                ));
                items
            }
            SuccessFactProofResult::Reuse(result) => {
                vec![SuccessCombinedFactProofItemResult::Reuse(Box::new(
                    SuccessCombinedReuseFactProofResult {
                        statement: verify_what,
                        source: result.source,
                    },
                ))]
            }
        }
    }

    fn is_builtin_rule(&self) -> bool {
        match self {
            SuccessCombinedFactProofItemResult::ByBuiltinRule(r)
            | SuccessCombinedFactProofItemResult::ByBuiltinStrategy(r) => !r.msg.is_empty(),
            SuccessCombinedFactProofItemResult::ByFact(_)
            | SuccessCombinedFactProofItemResult::ByKnownForall(_) => false,
            SuccessCombinedFactProofItemResult::Reuse(result) => {
                result.source.is_verified_by_builtin_rules_only()
            }
        }
    }
}

impl KnownForallInstantiationItem {
    pub fn new(param: String, arg_obj: Obj) -> Self {
        KnownForallInstantiationItem {
            param,
            arg: arg_obj.to_string(),
            arg_obj,
        }
    }
}

impl SuccessVerifyKnownForallRequirementResult {
    pub fn new(stmt: Fact, result: StmtResult, kind: KnownForallRequirementKind) -> Self {
        SuccessVerifyKnownForallRequirementResult {
            stmt,
            result: Box::new(result),
            kind,
        }
    }
}

impl SuccessInstantiateKnownForallResult {
    pub fn new(
        cite_what: Stmt,
        source_fact_id: Option<FactId>,
        instantiation: Vec<KnownForallInstantiationItem>,
        requirements: Vec<SuccessVerifyKnownForallRequirementResult>,
    ) -> Self {
        SuccessInstantiateKnownForallResult {
            cite_what: Box::new(cite_what),
            source_fact_id,
            instantiation,
            requirements,
        }
    }
}

impl ObjectIntroductionItem {
    pub fn new(name: String, facts: Vec<Fact>) -> Self {
        ObjectIntroductionItem { name, facts }
    }
}

impl SuccessForallProofResult {
    pub fn new(
        forall_fact: ForallFact,
        assumption_infers: SuccessInferResult,
        proves: Vec<SuccessForallProvedFactResult>,
    ) -> Self {
        SuccessForallProofResult {
            forall_fact,
            assumption_infers,
            proves,
        }
    }
}

impl SuccessForallProvedFactResult {
    pub fn new(stmt: ExistOrAndChainAtomicFact, result: StmtResult) -> Self {
        SuccessForallProvedFactResult {
            stmt,
            result: Box::new(result),
        }
    }
}

impl fmt::Debug for SuccessForallProofResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessForallProofResult")
            .field("forall_fact", &self.forall_fact.to_string())
            .field("assumption_infers", &self.assumption_infers)
            .field("proves", &self.proves)
            .finish()
    }
}

impl fmt::Debug for SuccessForallProvedFactResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessForallProvedFactResult")
            .field("stmt", &self.stmt.to_string())
            .field("result", &self.result)
            .finish()
    }
}

impl SuccessVerifyTheoremResult {
    pub fn new(
        name: String,
        forall_fact: ForallFact,
        well_definedness: SuccessVerifyFactWellDefinedResult,
        proof_scope: SuccessVerifyLocalProofScopeResult,
        proof_steps: Vec<StmtResult>,
        conclusion_checks: Vec<StmtResult>,
    ) -> Self {
        SuccessVerifyTheoremResult {
            name,
            forall_fact,
            well_definedness,
            proof_scope,
            proof_steps,
            conclusion_checks,
        }
    }
}

impl SuccessVerifyClaimForallResult {
    pub fn new(
        forall_fact: ForallFact,
        well_definedness: SuccessVerifyFactWellDefinedResult,
        proof_scope: SuccessVerifyLocalProofScopeResult,
        proof_steps: Vec<StmtResult>,
        conclusion_checks: Vec<StmtResult>,
    ) -> Self {
        SuccessVerifyClaimForallResult {
            forall_fact,
            well_definedness,
            proof_scope,
            proof_steps,
            conclusion_checks,
        }
    }
}

impl SuccessVerifyClaimFactResult {
    pub fn new(
        fact: Fact,
        well_definedness: SuccessVerifyFactWellDefinedResult,
        proof_scope: SuccessVerifyLocalProofScopeResult,
        proof_steps: Vec<StmtResult>,
        conclusion_check: StmtResult,
    ) -> Self {
        SuccessVerifyClaimFactResult {
            fact,
            well_definedness,
            proof_scope,
            proof_steps,
            conclusion_check: Box::new(conclusion_check),
        }
    }
}

impl From<SuccessVerifyClaimForallResult> for SuccessVerifyClaimResult {
    fn from(v: SuccessVerifyClaimForallResult) -> Self {
        SuccessVerifyClaimResult::Forall(Box::new(v))
    }
}

impl From<SuccessVerifyClaimFactResult> for SuccessVerifyClaimResult {
    fn from(v: SuccessVerifyClaimFactResult) -> Self {
        SuccessVerifyClaimResult::Fact(Box::new(v))
    }
}

impl SuccessVerifyByCasesResult {
    pub fn new(
        goal_well_definedness: Vec<SuccessVerifyFactWellDefinedResult>,
        coverage_check: StmtResult,
        then_facts: Vec<Fact>,
        branches: Vec<SuccessVerifyByCaseBranchResult>,
    ) -> Self {
        SuccessVerifyByCasesResult {
            goal_well_definedness,
            coverage_check: Box::new(coverage_check),
            then_facts,
            branches,
        }
    }
}

impl SuccessVerifyByContraResult {
    pub fn new(
        to_prove: Fact,
        reverse_assumption: Fact,
        reverse_assumption_fact_id: FactId,
        proof_scope: SuccessVerifyLocalProofScopeResult,
        proof_steps: Vec<StmtResult>,
        impossible_fact: AtomicFact,
        contradiction: SuccessVerifyContradictionResult,
    ) -> Self {
        SuccessVerifyByContraResult {
            to_prove,
            reverse_assumption,
            reverse_assumption_fact_id,
            proof_scope,
            proof_steps,
            impossible_fact,
            contradiction,
        }
    }
}

impl SuccessVerifyByAssignmentResult {
    pub fn new(
        assignment: Vec<(String, String)>,
        assumptions: Vec<(String, String)>,
        domain_checks: Vec<SuccessVerifyByAssignmentDomainResult>,
        proof_steps: Vec<StmtResult>,
        conclusion_checks: Vec<StmtResult>,
    ) -> Self {
        SuccessVerifyByAssignmentResult {
            assignment,
            assumptions,
            domain_checks,
            proof_steps,
            conclusion_checks,
        }
    }
}

impl SuccessVerifyByEnumerateFiniteSetResult {
    pub fn new(
        parameters: Vec<String>,
        parameter_sets: Vec<String>,
        prove_goal: String,
        assignments: Vec<SuccessVerifyByAssignmentResult>,
        generated_forall: String,
    ) -> Self {
        SuccessVerifyByEnumerateFiniteSetResult {
            parameters,
            parameter_sets,
            prove_goal,
            assignments,
            generated_forall,
        }
    }
}

impl SuccessVerifyByForResult {
    pub fn new(
        iteration_mode: String,
        parameters: Vec<String>,
        domains: Vec<String>,
        prove_goal: String,
        assignments: Vec<SuccessVerifyByAssignmentResult>,
        generated_forall: String,
    ) -> Self {
        SuccessVerifyByForResult {
            iteration_mode,
            parameters,
            domains,
            prove_goal,
            assignments,
            generated_forall,
        }
    }
}

impl SuccessVerifyByEnumerateRangeResult {
    pub fn new(
        proof_type: String,
        element: String,
        range: String,
        membership_fact: String,
        endpoint_facts: Vec<String>,
        generated_cases: String,
        membership_check: StmtResult,
        endpoint_checks: Vec<StmtResult>,
    ) -> Self {
        SuccessVerifyByEnumerateRangeResult {
            proof_type,
            element,
            range,
            membership_fact,
            endpoint_facts,
            generated_cases,
            membership_check: Box::new(membership_check),
            endpoint_checks,
        }
    }
}

impl SuccessVerifyByInducResult {
    pub fn new(
        parameter: String,
        prove_goals: Vec<String>,
        generated_forall: String,
        proof: SuccessVerifyByInducProofResult,
    ) -> Self {
        SuccessVerifyByInducResult {
            parameter,
            prove_goals,
            generated_forall,
            proof,
        }
    }
}

impl SuccessVerifyByExtensionResult {
    pub fn new(
        left: String,
        right: String,
        prove_goal: String,
        left_to_right_subset: String,
        right_to_left_subset: String,
        proof_steps: Vec<StmtResult>,
        left_to_right_check: StmtResult,
        right_to_left_check: StmtResult,
    ) -> Self {
        SuccessVerifyByExtensionResult {
            left,
            right,
            prove_goal,
            left_to_right_subset,
            right_to_left_subset,
            proof_steps,
            left_to_right_check: Box::new(left_to_right_check),
            right_to_left_check: Box::new(right_to_left_check),
        }
    }
}

impl SuccessVerifyByPropRegistrationResult {
    pub fn new(
        registration_type: String,
        prop_name: String,
        forall_fact: ForallFact,
        assumption_infers: SuccessInferResult,
        proof_steps: Vec<StmtResult>,
        conclusion_check: StmtResult,
    ) -> Self {
        SuccessVerifyByPropRegistrationResult {
            registration_type,
            prop_name,
            forall_fact,
            assumption_infers,
            proof_steps,
            conclusion_check: Box::new(conclusion_check),
        }
    }
}

impl SuccessVerifyByChoiceResult {
    pub fn new(
        proof_type: String,
        target: String,
        proof_steps: Vec<StmtResult>,
        obligations: Vec<SuccessVerifyByChoiceObligationResult>,
        trusted_conclusion: String,
    ) -> Self {
        SuccessVerifyByChoiceResult {
            proof_type,
            target,
            proof_steps,
            obligations,
            trusted_conclusion,
        }
    }
}

impl SuccessVerifyByTheoremResult {
    pub fn new(
        theorem: String,
        arguments: Vec<String>,
        domain_facts: Vec<String>,
        direct_conclusions: Vec<Fact>,
        stored_then_facts: Vec<String>,
        argument_verification: Option<SuccessVerifyArgsSatisfyParamDefResult>,
        domain_checks: Vec<StmtResult>,
    ) -> Self {
        let parent_stored_facts = stored_then_facts.clone();
        SuccessVerifyByTheoremResult {
            theorem,
            theorem_source: "litex".to_string(),
            mode: "release_all".to_string(),
            arguments,
            domain_facts,
            requirement_roles: vec![],
            direct_conclusions,
            stored_then_facts,
            temporary_then_facts: vec![],
            selected_fact: None,
            parent_stored_facts,
            provenance: None,
            argument_verification: argument_verification.map(Box::new),
            requirement_checks: Vec::new(),
            domain_checks,
            selected_fact_check: None,
        }
    }

    pub fn new_builtin(
        theorem: String,
        arguments: Vec<String>,
        requirement_facts: Vec<String>,
        requirement_roles: Vec<String>,
        direct_conclusions: Vec<Fact>,
        stored_then_facts: Vec<String>,
        requirement_checks: Vec<StmtResult>,
        provenance: Option<String>,
    ) -> Self {
        let parent_stored_facts = stored_then_facts.clone();
        SuccessVerifyByTheoremResult {
            theorem,
            theorem_source: "builtin_rule".to_string(),
            mode: "release_all".to_string(),
            arguments,
            domain_facts: requirement_facts,
            requirement_roles,
            direct_conclusions,
            stored_then_facts,
            temporary_then_facts: vec![],
            selected_fact: None,
            parent_stored_facts,
            provenance,
            argument_verification: None,
            requirement_checks,
            domain_checks: Vec::new(),
            selected_fact_check: None,
        }
    }

    pub fn select_atomic_fact(&mut self, selected_fact: String) {
        self.mode = "select_atomic_fact".to_string();
        self.temporary_then_facts = self.stored_then_facts.clone();
        self.stored_then_facts.clear();
        self.parent_stored_facts = vec![selected_fact.clone()];
        self.selected_fact = Some(selected_fact);
    }

    pub fn retain_selected_fact_check(&mut self, result: StmtResult) {
        self.selected_fact_check = Some(Box::new(result));
    }
}

impl SuccessVerifyByDefinitionResult {
    pub fn new(
        prop: String,
        definition: Option<DefPropStmt>,
        arguments: Vec<String>,
        definition_clauses: Vec<String>,
        stored_fact: String,
        concrete_user_prop: bool,
        definition_clause_facts: Vec<Fact>,
        argument_verification: Option<SuccessVerifyArgsSatisfyParamDefResult>,
        clause_checks: Vec<StmtResult>,
    ) -> Self {
        SuccessVerifyByDefinitionResult {
            prop,
            definition,
            arguments,
            definition_clauses,
            stored_fact,
            concrete_user_prop,
            definition_clause_facts,
            argument_verification: argument_verification.map(Box::new),
            clause_checks,
        }
    }
}

impl fmt::Debug for SuccessVerifyClaimResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            SuccessVerifyClaimResult::Forall(v) => f.debug_tuple("Forall").field(v).finish(),
            SuccessVerifyClaimResult::Fact(v) => f.debug_tuple("Fact").field(v).finish(),
        }
    }
}

impl fmt::Debug for SuccessVerifyTheoremResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyTheoremResult")
            .field("name", &self.name)
            .field("forall_fact", &self.forall_fact.to_string())
            .field("well_definedness", &self.well_definedness)
            .field("proof_scope", &self.proof_scope)
            .field("proof_steps", &self.proof_steps)
            .field("conclusion_checks", &self.conclusion_checks)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyClaimForallResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyClaimForallResult")
            .field("forall_fact", &self.forall_fact.to_string())
            .field("well_definedness", &self.well_definedness)
            .field("proof_scope", &self.proof_scope)
            .field("proof_steps", &self.proof_steps)
            .field("conclusion_checks", &self.conclusion_checks)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyClaimFactResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyClaimFactResult")
            .field("fact", &self.fact.to_string())
            .field("well_definedness", &self.well_definedness)
            .field("proof_scope", &self.proof_scope)
            .field("proof_steps", &self.proof_steps)
            .field("conclusion_check", &self.conclusion_check)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyByCasesResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let cases = self
            .branches
            .iter()
            .map(|branch| branch.assumption.to_string())
            .collect::<Vec<_>>();
        let then_facts = self
            .then_facts
            .iter()
            .map(|fact| fact.to_string())
            .collect::<Vec<_>>();
        f.debug_struct("SuccessVerifyByCasesResult")
            .field("goal_well_definedness", &self.goal_well_definedness)
            .field("coverage_check", &self.coverage_check)
            .field("cases", &cases)
            .field("then_facts", &then_facts)
            .field("branches", &self.branches)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyByCaseBranchResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByCaseBranchResult")
            .field("assumption", &self.assumption.to_string())
            .field("assumption_fact_id", &self.assumption_fact_id)
            .field("proof_scope", &self.proof_scope)
            .field("proof_steps", &self.proof_steps)
            .field("exit", &self.exit)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyByCaseBranchExitResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::Conclusions(result) => f.debug_tuple("Conclusions").field(result).finish(),
            Self::Contradiction(result) => f.debug_tuple("Contradiction").field(result).finish(),
        }
    }
}

impl fmt::Debug for SuccessVerifyByCaseConclusionsResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByCaseConclusionsResult")
            .field("checks", &self.checks)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyByCaseContradictionResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByCaseContradictionResult")
            .field("impossible_fact", &self.impossible_fact.to_string())
            .field("contradiction", &self.contradiction)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyByContraResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByContraResult")
            .field("to_prove", &self.to_prove.to_string())
            .field("reverse_assumption", &self.reverse_assumption.to_string())
            .field(
                "reverse_assumption_fact_id",
                &self.reverse_assumption_fact_id,
            )
            .field("proof_scope", &self.proof_scope)
            .field("proof_steps", &self.proof_steps)
            .field("impossible_fact", &self.impossible_fact.to_string())
            .field("contradiction", &self.contradiction)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyByPropRegistrationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByPropRegistrationResult")
            .field("registration_type", &self.registration_type)
            .field("prop_name", &self.prop_name)
            .field("forall_fact", &self.forall_fact.to_string())
            .field("assumption_infers", &self.assumption_infers)
            .field("proof_steps", &self.proof_steps)
            .field("conclusion_check", &self.conclusion_check)
            .finish()
    }
}

fn merge_verified_by_with_steps(
    _goal: Fact,
    verified_by: SuccessFactProofResult,
    step_results: Vec<StmtResult>,
) -> SuccessFactProofResult {
    if step_results.is_empty() {
        return verified_by;
    }
    let mut items = SuccessCombinedFactProofItemResult::from_verified_by_result(_goal, verified_by);
    for r in step_results {
        items.extend(verified_by_items_from_stmt_result(r));
    }
    SuccessFactProofResult::wrap_bys(items)
}

fn verified_by_items_from_stmt_result(
    result: StmtResult,
) -> Vec<SuccessCombinedFactProofItemResult> {
    match result {
        StmtResult::Success(SuccessStmtResult::Fact(success)) => {
            vec![SuccessCombinedFactProofItemResult::Reuse(Box::new(
                SuccessCombinedReuseFactProofResult {
                    statement: success.fact(),
                    source: success.verification,
                },
            ))]
        }
        StmtResult::Success(success) => success
            .into_child_results()
            .into_iter()
            .flat_map(verified_by_items_from_stmt_result)
            .collect::<Vec<_>>(),
        StmtResult::Unknown(_) => Vec::new(),
    }
}
