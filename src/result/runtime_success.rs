use crate::prelude::*;
use std::fmt;
use std::rc::Rc;

#[derive(Debug)]
pub struct NonFactualStmtSuccess {
    pub stmt: Stmt,
    pub litex_to_lean_ir: Option<LitexToLeanStatementIr>,
    pub well_definedness: WellDefinednessCertificate,
    pub infers: InferResult,
    /// Stored facts selected for ordinary statement output. Most statements keep
    /// their environment effects in the detailed execution trace only; value-
    /// producing statements such as `eval` may expose their primary result.
    pub reported_store_facts: Vec<StoreFactOutput>,
    pub inside_results: Vec<StmtResult>,
    pub execution_trace: Option<StatementExecutionTrace>,
    pub theorem_verification: Option<TheoremVerificationResult>,
    pub claim_verification: Option<ClaimVerificationResult>,
    /// Exact verifier-to-environment mapping for bare `have x T` selection.
    /// The proof results stay in `inside_results`; this record identifies which
    /// one certifies each selected object's stored type fact.
    pub object_choice_verification: Option<ObjectChoiceVerificationResult>,
    /// Checked witness, parameter, and body-result layout for
    /// `witness exist ... from ...`.
    pub witness_exist_verification: Option<WitnessExistVerificationResult>,
    /// Runtime-resolved definition and witness evidence for
    /// `witness $P(args) from ...`.
    pub witness_atomic_fact_verification: Option<WitnessAtomicFactVerificationResult>,
    /// Exact source-to-environment projection contract for `obtain ... from
    /// exist ...` and body-style `have x T: ...`.
    pub existential_elimination_verification: Option<ExistentialEliminationVerificationResult>,
    /// Exact verifier-to-environment contract for `have fn f(...) ... = body`.
    /// The statement retains the signature/body; this mapping freezes which
    /// checked result certifies the return value and which two stored facts
    /// introduce the function object to later statements.
    pub function_definition_verification: Option<FunctionDefinitionVerificationResult>,
    pub by_verification: Option<ByVerificationResult>,
}

#[derive(Clone, Debug)]
pub struct FunctionDefinitionVerificationResult {
    pub return_check_index: usize,
    /// Membership/domain facts installed while checking the return value,
    /// with their temporary FactIds frozen before that local scope closes.
    pub assumption_infers: InferResult,
    pub function_membership: Fact,
    pub defining_equality: Fact,
}

impl FunctionDefinitionVerificationResult {
    pub fn new(
        return_check_index: usize,
        assumption_infers: InferResult,
        function_membership: Fact,
        defining_equality: Fact,
    ) -> Self {
        Self {
            return_check_index,
            assumption_infers,
            function_membership,
            defining_equality,
        }
    }
}

pub struct TheoremVerificationResult {
    pub name: String,
    pub forall_fact: ForallFact,
    pub assumption_infers: InferResult,
    pub proof_step_count: usize,
}

pub enum ClaimVerificationResult {
    Forall(ClaimForallVerificationResult),
    Fact(ClaimFactVerificationResult),
}

pub struct ClaimForallVerificationResult {
    pub forall_fact: ForallFact,
    pub assumption_infers: InferResult,
    pub proof_step_count: usize,
}

pub struct ClaimFactVerificationResult {
    pub fact: Fact,
    pub proof_step_count: usize,
}

pub enum ByVerificationResult {
    Cases(ByCasesVerificationResult),
    Contra(ByContraVerificationResult),
    EnumerateFiniteSet(ByEnumerateFiniteSetVerificationResult),
    EnumerateRange(ByEnumerateRangeVerificationResult),
    Induc(ByInducVerificationResult),
    For(ByForVerificationResult),
    Extension(ByExtensionVerificationResult),
    PropRegistration(ByPropRegistrationVerificationResult),
    AxiomOfChoice(ByChoiceVerificationResult),
    ZornLemma(ByChoiceVerificationResult),
    RegularityAxiom(ByChoiceVerificationResult),
    Definition(ByDefinitionVerificationResult),
    Theorem(ByTheoremVerificationResult),
}

pub struct ByCasesVerificationResult {
    pub cases: Vec<AndChainAtomicFact>,
    /// Stable IDs of the temporary case assumptions, captured before each
    /// branch environment is popped. Compiler backends use these IDs to bind
    /// citations inside the corresponding proof scope.
    pub case_fact_ids: Vec<FactId>,
    pub then_facts: Vec<Fact>,
    pub proof_step_counts: Vec<usize>,
    pub case_result_counts: Vec<usize>,
    pub impossible_facts: Vec<Option<AtomicFact>>,
}

pub struct ByContraVerificationResult {
    pub to_prove: Fact,
    pub reverse_assumption: Fact,
    /// Stable ID of the temporary reverse assumption while the contradiction
    /// proof environment was alive.
    pub reverse_assumption_fact_id: FactId,
    pub proof_step_count: usize,
    pub impossible_fact: AtomicFact,
}

#[derive(Clone, Debug)]
pub struct ByAssignmentVerificationResult {
    pub assignment: Vec<(String, String)>,
    pub assumptions: Vec<(String, String)>,
    pub domain_check_count: usize,
    pub proof_step_count: usize,
    pub conclusion_count: usize,
    pub skipped_domain: Option<String>,
    pub result_count: usize,
}

#[derive(Clone, Debug)]
pub struct ByEnumerateFiniteSetVerificationResult {
    pub parameters: Vec<String>,
    pub parameter_sets: Vec<String>,
    pub prove_goal: String,
    pub assignments: Vec<ByAssignmentVerificationResult>,
    pub generated_forall: String,
}

#[derive(Clone, Debug)]
pub struct ByForVerificationResult {
    pub iteration_mode: String,
    pub parameters: Vec<String>,
    pub domains: Vec<String>,
    pub prove_goal: String,
    pub assignments: Vec<ByAssignmentVerificationResult>,
    pub generated_forall: String,
}

#[derive(Clone, Debug)]
pub struct ByEnumerateRangeVerificationResult {
    pub proof_type: String,
    pub element: String,
    pub range: String,
    pub membership_fact: String,
    pub endpoint_facts: Vec<String>,
    pub generated_cases: String,
}

#[derive(Clone, Debug)]
pub struct ByInducVerificationResult {
    pub strong: bool,
    pub finite_set: bool,
    pub structured: bool,
    pub parameter: String,
    pub start: String,
    pub prove_goals: Vec<String>,
    pub generated_forall: String,
    pub proof_step_count: usize,
    pub base_assumptions: Vec<(String, String)>,
    pub base_proof_step_count: usize,
    pub base_result_count: usize,
    pub step_assumptions: Vec<(String, String)>,
    pub step_proof_step_count: usize,
    pub step_result_count: usize,
}

#[derive(Clone, Debug)]
pub struct ByExtensionVerificationResult {
    pub left: String,
    pub right: String,
    pub prove_goal: String,
    pub proof_step_count: usize,
    pub left_to_right_subset: String,
    pub right_to_left_subset: String,
}

#[derive(Clone)]
pub struct ByPropRegistrationVerificationResult {
    pub registration_type: String,
    pub prop_name: String,
    pub forall_fact: ForallFact,
    pub assumption_infers: InferResult,
    pub proof_step_count: usize,
}

#[derive(Clone, Debug)]
pub struct ByChoiceVerificationResult {
    pub proof_type: String,
    pub target: String,
    pub proof_step_count: usize,
    pub obligations: Vec<(String, String, bool)>,
    pub trusted_conclusion: String,
}

#[derive(Clone, Debug)]
pub struct ByTheoremVerificationResult {
    pub theorem: String,
    pub theorem_source: String,
    pub mode: String,
    pub arguments: Vec<String>,
    pub domain_facts: Vec<String>,
    pub requirement_roles: Vec<String>,
    pub stored_then_facts: Vec<String>,
    pub temporary_then_facts: Vec<String>,
    pub selected_fact: Option<String>,
    pub parent_stored_facts: Vec<String>,
    pub provenance: Option<String>,
}

#[derive(Clone, Debug)]
pub struct ByDefinitionVerificationResult {
    pub prop: String,
    pub arguments: Vec<String>,
    pub definition_clauses: Vec<String>,
    pub stored_fact: String,
}

#[derive(Clone, Debug)]
pub struct ObjectIntroductionItem {
    pub name: String,
    pub facts: Vec<Fact>,
}

#[derive(Clone, Debug)]
pub struct ObjectChoiceVerificationResult {
    /// One exact stored type fact for every selected object, in declaration
    /// order. For an object carrier this is the selected membership fact.
    pub selected_type_facts: Vec<Fact>,
    /// Index into `NonFactualStmtSuccess::inside_results` for the checked
    /// nonemptiness producer. Meta-level parameter types currently have no
    /// such producer and retain `None` as an explicit backend boundary.
    pub nonempty_check_indices: Vec<Option<usize>>,
}

impl ObjectChoiceVerificationResult {
    pub fn new(selected_type_facts: Vec<Fact>, nonempty_check_indices: Vec<Option<usize>>) -> Self {
        ObjectChoiceVerificationResult {
            selected_type_facts,
            nonempty_check_indices,
        }
    }
}

#[derive(Debug)]
pub struct WitnessExistVerificationResult {
    /// Number of user proof statements at the front of `inside_results`.
    pub proof_step_count: usize,
    /// One factual type-check result for every witness value that contributes
    /// a target-side existential requirement.  Plain `set` binders need no
    /// separate target proposition because every value already has type
    /// `LitexSet`.
    pub parameter_checks: Vec<Option<Box<StmtResult>>>,
    /// One factual result for every direct existential body fact.
    pub body_check_indices: Vec<usize>,
    /// The final result for the uniqueness obligation, when the source form
    /// is `exist!`.
    pub uniqueness_check_index: Option<usize>,
}

pub struct WitnessAtomicFactVerificationResult {
    pub definition: DefPropStmt,
    pub instantiated_existential: ExistFactEnum,
    pub definition_parameter_check: Box<StmtResult>,
    pub witness_verification: WitnessExistVerificationResult,
}

impl WitnessAtomicFactVerificationResult {
    pub fn new(
        definition: DefPropStmt,
        instantiated_existential: ExistFactEnum,
        definition_parameter_check: StmtResult,
        witness_verification: WitnessExistVerificationResult,
    ) -> Self {
        WitnessAtomicFactVerificationResult {
            definition,
            instantiated_existential,
            definition_parameter_check: Box::new(definition_parameter_check),
            witness_verification,
        }
    }
}

impl fmt::Debug for WitnessAtomicFactVerificationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("WitnessAtomicFactVerificationResult")
            .field("definition", &self.definition.name)
            .field(
                "instantiated_existential",
                &self.instantiated_existential.to_string(),
            )
            .field(
                "definition_parameter_check",
                &self.definition_parameter_check,
            )
            .field("witness_verification", &self.witness_verification)
            .finish()
    }
}

impl WitnessExistVerificationResult {
    pub fn new(
        proof_step_count: usize,
        parameter_checks: Vec<Option<Box<StmtResult>>>,
        body_check_indices: Vec<usize>,
        uniqueness_check_index: Option<usize>,
    ) -> Self {
        Self {
            proof_step_count,
            parameter_checks,
            body_check_indices,
            uniqueness_check_index,
        }
    }
}

#[derive(Clone)]
pub struct ExistentialEliminationVerificationResult {
    /// Index of the checked source existential in `inside_results`.
    pub source_result_index: usize,
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

impl fmt::Debug for ExistentialEliminationVerificationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("ExistentialEliminationVerificationResult")
            .field("source_result_index", &self.source_result_index)
            .field("source_exist_fact", &self.source_exist_fact.to_string())
            .field("witness_type_facts", &self.witness_type_facts)
            .field("instantiated_body_facts", &self.instantiated_body_facts)
            .field("includes_uniqueness", &self.includes_uniqueness)
            .finish()
    }
}

impl ExistentialEliminationVerificationResult {
    pub fn new(
        source_result_index: usize,
        source_exist_fact: ExistFactEnum,
        witness_type_facts: Vec<Fact>,
        instantiated_body_facts: Vec<Fact>,
        includes_uniqueness: bool,
    ) -> Self {
        Self {
            source_result_index,
            source_exist_fact,
            witness_type_facts,
            instantiated_body_facts,
            includes_uniqueness,
        }
    }
}

#[derive(Debug)]
pub struct VerifiedByBuiltinRuleResult {
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
pub struct VerifiedByFactResult {
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
    pub checked_definition_replay: Option<CheckedDefinitionReplayEvidence>,
}

#[derive(Clone)]
pub struct CheckedDefinitionReplayEvidence {
    pub definition_object: Obj,
    pub defining_equality: Fact,
    pub defining_equality_fact_id: FactId,
    pub application_side: Obj,
    pub reduced: Obj,
    pub other_side: Obj,
    pub application_is_left: bool,
    pub reduced_matches_other_by_alpha: bool,
}

impl fmt::Debug for CheckedDefinitionReplayEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("CheckedDefinitionReplayEvidence")
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
pub struct KnownForallRequirementResult {
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
pub struct KnownForallInstantiationResult {
    pub cite_what: Box<Stmt>,
    /// Captured while the source forall's environment is still alive.
    pub source_fact_id: Option<FactId>,
    pub instantiation: Vec<KnownForallInstantiationItem>,
    pub requirements: Vec<KnownForallRequirementResult>,
}

#[derive(Debug)]
pub struct VerifiedBysResult {
    pub cite_what: Vec<VerifiedBysEnum>,
}

pub struct ForallProofResult {
    pub forall_fact: ForallFact,
    pub assumption_infers: InferResult,
    pub proves: Vec<ForallProvedFactResult>,
}

pub struct ForallProvedFactResult {
    pub stmt: ExistOrAndChainAtomicFact,
    pub result: Box<StmtResult>,
}

#[derive(Debug)]
pub struct FactVerifiedByBuiltinRuleInVerifiedBys {
    pub msg: String,
    pub verify_what: Fact,
    pub evidence: Option<BuiltinRuleEvidence>,
    pub subgoals: Vec<StmtResult>,
}

#[derive(Debug)]
pub struct FactVerifiedByFactInVerifiedBys {
    pub detail: Option<String>,
    pub verify_what: Fact,
    pub cite_what: Box<Stmt>,
    pub source_fact_id: Option<FactId>,
    pub equality_transport: Option<EqualityTransportEvidence>,
    pub fact_transformation: Option<FactTransformationEvidence>,
}

#[derive(Debug)]
pub struct FactVerifiedByKnownForallInVerifiedBys {
    pub verify_what: Fact,
    pub result: KnownForallInstantiationResult,
}

#[derive(Debug)]
pub enum VerifiedBysEnum {
    ByBuiltinRule(FactVerifiedByBuiltinRuleInVerifiedBys),
    ByBuiltinStrategy(FactVerifiedByBuiltinRuleInVerifiedBys),
    ByFact(FactVerifiedByFactInVerifiedBys),
    ByKnownForall(FactVerifiedByKnownForallInVerifiedBys),
    /// Internal proof sharing; output and dependency analysis expose the source proof.
    ByStatementMemo(Fact, Rc<FactualStmtSuccess>),
}

#[derive(Debug)]
pub enum VerifiedByResult {
    BuiltinRule(VerifiedByBuiltinRuleResult),
    BuiltinStrategy(VerifiedByBuiltinRuleResult),
    Fact(VerifiedByFactResult),
    KnownForallInstantiation(KnownForallInstantiationResult),
    VerifiedBys(VerifiedBysResult),
    ForallProof(ForallProofResult),
    /// Internal proof sharing; this is not a user-visible verification method.
    StatementMemo(Rc<FactualStmtSuccess>),
}

#[derive(Debug)]
pub struct FactualStmtSuccess {
    pub stmt: Fact,
    /// Filled when this proved fact has actually been stored. Verification-only
    /// subgoals legitimately keep `None`.
    pub fact_id: Option<FactId>,
    pub litex_to_lean_ir: Option<LitexToLeanStatementIr>,
    pub well_definedness: WellDefinednessCertificate,
    pub infers: InferResult,
    pub verified_by: VerifiedByResult,
    pub execution_trace: Option<StatementExecutionTrace>,
}

impl FactualStmtSuccess {
    pub fn new_with_verified_by_builtin_rules(
        stmt: Fact,
        infers: InferResult,
        verified_by: VerifiedByResult,
    ) -> Self {
        FactualStmtSuccess {
            stmt,
            fact_id: None,
            litex_to_lean_ir: None,
            well_definedness: WellDefinednessCertificate::default(),
            infers,
            verified_by,
            execution_trace: None,
        }
    }

    pub fn new_with_verified_by_builtin_rules_recording_stmt(
        stmt: Fact,
        builtin_rule_label: String,
        step_results: Vec<StmtResult>,
    ) -> Self {
        let infers = InferResult::new();
        let verified_by =
            VerifiedByResult::builtin_rule_with_subgoals(builtin_rule_label, step_results);
        Self::new_with_verified_by_builtin_rules(stmt, infers, verified_by)
    }

    pub fn new_with_verified_by_builtin_strategy_recording_stmt(
        stmt: Fact,
        strategy_label: String,
        step_results: Vec<StmtResult>,
    ) -> Self {
        let verified_by = VerifiedByResult::BuiltinStrategy(VerifiedByBuiltinRuleResult {
            msg: strategy_label,
            evidence: None,
            subgoals: step_results,
        });
        Self::new_with_verified_by_builtin_rules(stmt, InferResult::new(), verified_by)
    }

    pub fn new_with_verified_by_builtin_strategy_evidence_recording_stmt(
        stmt: Fact,
        strategy_label: String,
        evidence: BuiltinRuleEvidence,
        step_results: Vec<StmtResult>,
    ) -> Self {
        let verified_by = VerifiedByResult::BuiltinStrategy(VerifiedByBuiltinRuleResult {
            msg: strategy_label,
            evidence: Some(evidence),
            subgoals: step_results,
        });
        Self::new_with_verified_by_builtin_rules(stmt, InferResult::new(), verified_by)
    }

    pub fn new_with_verified_by_builtin_rules_label_and_steps(
        stmt: Fact,
        infers: InferResult,
        builtin_rule_label: String,
        step_results: Vec<StmtResult>,
    ) -> Self {
        let verified_by =
            VerifiedByResult::builtin_rule_with_subgoals(builtin_rule_label, step_results);
        Self::new_with_verified_by_builtin_rules(stmt, infers, verified_by)
    }

    pub fn new_with_verified_by_builtin_rule_evidence_and_steps(
        stmt: Fact,
        infers: InferResult,
        builtin_rule_label: String,
        evidence: BuiltinRuleEvidence,
        step_results: Vec<StmtResult>,
    ) -> Self {
        let verified_by = VerifiedByResult::builtin_rule_with_evidence(
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
            InferResult::new(),
            builtin_rule_label,
            evidence,
            step_results,
        )
    }

    pub fn new_with_verified_by_known_fact_and_infer(
        stmt: Fact,
        infers: InferResult,
        verified_by: VerifiedByResult,
        step_results: Vec<StmtResult>,
    ) -> Self {
        let verified_by = merge_verified_by_with_steps(stmt.clone(), verified_by, step_results);
        FactualStmtSuccess {
            stmt,
            fact_id: None,
            litex_to_lean_ir: None,
            well_definedness: WellDefinednessCertificate::default(),
            infers,
            verified_by,
            execution_trace: None,
        }
    }

    pub fn new_with_verified_by_known_fact(
        stmt: Fact,
        verified_by: VerifiedByResult,
        step_results: Vec<StmtResult>,
    ) -> Self {
        Self::new_with_verified_by_known_fact_and_infer(
            stmt,
            InferResult::new(),
            verified_by,
            step_results,
        )
    }

    pub fn new_with_statement_memo(
        stmt: Fact,
        infers: InferResult,
        source: Rc<FactualStmtSuccess>,
    ) -> Self {
        Self::new_with_verified_by_builtin_rules(
            stmt,
            infers,
            VerifiedByResult::StatementMemo(source),
        )
    }

    pub fn is_verified_by_builtin_rules_only(&self) -> bool {
        self.verified_by.tree_is_builtin_rules_only()
    }

    pub(crate) fn underlying_verified_by(&self) -> &VerifiedByResult {
        let mut success = self;
        loop {
            match &success.verified_by {
                VerifiedByResult::StatementMemo(source) => success = source,
                verified_by => return verified_by,
            }
        }
    }
}

impl VerifiedByResult {
    pub fn builtin_rule(msg: impl Into<String>) -> Self {
        Self::builtin_rule_with_subgoals(msg, Vec::new())
    }

    pub fn builtin_rule_with_subgoals(
        msg: impl Into<String>,
        subgoals: Vec<StmtResult>,
    ) -> Self {
        Self::BuiltinRule(VerifiedByBuiltinRuleResult {
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
        Self::BuiltinRule(VerifiedByBuiltinRuleResult {
            msg: msg.into(),
            evidence: Some(evidence),
            subgoals,
        })
    }

    pub fn cited_fact(_goal: Fact, cite_what: Fact, detail: Option<String>) -> Self {
        Self::cited_stmt(_goal, cite_what.into_stmt(), detail)
    }

    pub fn cited_stmt(_goal: Fact, cite_what: Stmt, detail: Option<String>) -> Self {
        Self::Fact(VerifiedByFactResult {
            detail,
            cite_what: Box::new(cite_what),
            source_fact_id: None,
            equality_transport: None,
            fact_transformation: None,
            checked_definition_replay: None,
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
        Self::Fact(VerifiedByFactResult {
            detail,
            cite_what: Box::new(cite_what.into_stmt()),
            source_fact_id,
            equality_transport,
            fact_transformation,
            checked_definition_replay: None,
        })
    }

    pub fn known_forall_instantiation(
        cite_what: Fact,
        source_fact_id: Option<FactId>,
        instantiation: Vec<KnownForallInstantiationItem>,
        requirements: Vec<KnownForallRequirementResult>,
    ) -> Self {
        Self::KnownForallInstantiation(KnownForallInstantiationResult::new(
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

    pub fn fact_with_checked_definition_replay(
        goal: Fact,
        evidence: CheckedDefinitionReplayEvidence,
        detail: Option<String>,
    ) -> Self {
        let cite_what = goal.clone().into_stmt();
        Self::Fact(VerifiedByFactResult {
            detail,
            cite_what: Box::new(cite_what),
            source_fact_id: None,
            equality_transport: None,
            fact_transformation: None,
            checked_definition_replay: Some(evidence),
        })
    }

    pub fn cached_fact(fact: Fact, cite_fact_source: LineFile, source_fact_id: FactId) -> Self {
        let cite_what = fact.with_line_file(cite_fact_source);
        Self::Fact(VerifiedByFactResult {
            detail: None,
            cite_what: Box::new(cite_what.into_stmt()),
            source_fact_id: Some(source_fact_id),
            equality_transport: None,
            fact_transformation: None,
            checked_definition_replay: None,
        })
    }

    pub fn wrap_bys(children: Vec<VerifiedBysEnum>) -> Self {
        Self::VerifiedBys(VerifiedBysResult {
            cite_what: children,
        })
    }

    pub fn forall_proof(
        forall_fact: ForallFact,
        then_results: Vec<StmtResult>,
        assumption_infers: InferResult,
    ) -> Self {
        let mut proves = Vec::new();
        for (stmt, result) in forall_fact
            .then_facts
            .iter()
            .cloned()
            .zip(then_results.into_iter())
        {
            proves.push(ForallProvedFactResult::new(stmt, result));
        }
        Self::ForallProof(ForallProofResult::new(
            forall_fact,
            assumption_infers,
            proves,
        ))
    }

    pub fn tree_is_builtin_rules_only(&self) -> bool {
        match self {
            VerifiedByResult::BuiltinRule(r) | VerifiedByResult::BuiltinStrategy(r) => {
                !r.msg.is_empty()
            }
            VerifiedByResult::Fact(_) => false,
            VerifiedByResult::KnownForallInstantiation(_) => false,
            VerifiedByResult::VerifiedBys(w) => {
                !w.cite_what.is_empty() && w.cite_what.iter().all(|b| b.is_builtin_rule())
            }
            VerifiedByResult::ForallProof(_) => false,
            VerifiedByResult::StatementMemo(source) => source.is_verified_by_builtin_rules_only(),
        }
    }
}

impl VerifiedBysEnum {
    pub fn builtin_rule(msg: String, verify_what: Fact, subgoals: Vec<StmtResult>) -> Self {
        Self::builtin_rule_with_evidence(msg, verify_what, None, subgoals)
    }

    fn builtin_rule_with_evidence(
        msg: String,
        verify_what: Fact,
        evidence: Option<BuiltinRuleEvidence>,
        subgoals: Vec<StmtResult>,
    ) -> Self {
        VerifiedBysEnum::ByBuiltinRule(FactVerifiedByBuiltinRuleInVerifiedBys {
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
        VerifiedBysEnum::ByBuiltinStrategy(FactVerifiedByBuiltinRuleInVerifiedBys {
            msg,
            verify_what,
            evidence,
            subgoals,
        })
    }

    pub fn cited_fact(verify_what: Fact, cite_what: Fact, detail: Option<String>) -> Self {
        Self::cited_stmt(verify_what, cite_what.into_stmt(), detail)
    }

    pub fn cited_stmt(verify_what: Fact, cite_what: Stmt, detail: Option<String>) -> Self {
        VerifiedBysEnum::ByFact(FactVerifiedByFactInVerifiedBys {
            detail,
            verify_what,
            cite_what: Box::new(cite_what),
            source_fact_id: None,
            equality_transport: None,
            fact_transformation: None,
        })
    }

    pub fn known_forall_instantiation(
        verify_what: Fact,
        result: KnownForallInstantiationResult,
    ) -> Self {
        VerifiedBysEnum::ByKnownForall(FactVerifiedByKnownForallInVerifiedBys {
            verify_what,
            result,
        })
    }

    pub fn fact_with_note(verify_what: Fact, msg: Option<String>) -> Self {
        let cite_what = verify_what.clone();
        Self::cited_fact(verify_what, cite_what, msg)
    }

    fn from_verified_by_result(verify_what: Fact, verified_by: VerifiedByResult) -> Vec<Self> {
        match verified_by {
            VerifiedByResult::BuiltinRule(r) => {
                vec![Self::builtin_rule_with_evidence(
                    r.msg,
                    verify_what,
                    r.evidence,
                    r.subgoals,
                )]
            }
            VerifiedByResult::BuiltinStrategy(r) => {
                vec![Self::builtin_strategy_with_evidence(
                    r.msg,
                    verify_what,
                    r.evidence,
                    r.subgoals,
                )]
            }
            VerifiedByResult::Fact(r) => {
                vec![VerifiedBysEnum::ByFact(FactVerifiedByFactInVerifiedBys {
                    detail: r.detail,
                    verify_what,
                    cite_what: r.cite_what,
                    source_fact_id: r.source_fact_id,
                    equality_transport: r.equality_transport,
                    fact_transformation: r.fact_transformation,
                })]
            }
            VerifiedByResult::KnownForallInstantiation(r) => {
                vec![Self::known_forall_instantiation(verify_what, r)]
            }
            VerifiedByResult::VerifiedBys(w) => w.cite_what,
            VerifiedByResult::ForallProof(_) => {
                vec![Self::fact_with_note(
                    verify_what,
                    Some("forall proof".to_string()),
                )]
            }
            VerifiedByResult::StatementMemo(source) => {
                vec![VerifiedBysEnum::ByStatementMemo(verify_what, source)]
            }
        }
    }

    fn is_builtin_rule(&self) -> bool {
        match self {
            VerifiedBysEnum::ByBuiltinRule(r) | VerifiedBysEnum::ByBuiltinStrategy(r) => {
                !r.msg.is_empty()
            }
            VerifiedBysEnum::ByFact(_) | VerifiedBysEnum::ByKnownForall(_) => false,
            VerifiedBysEnum::ByStatementMemo(_, source) => {
                source.is_verified_by_builtin_rules_only()
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

impl KnownForallRequirementResult {
    pub fn new(stmt: Fact, result: StmtResult, kind: KnownForallRequirementKind) -> Self {
        KnownForallRequirementResult {
            stmt,
            result: Box::new(result),
            kind,
        }
    }
}

impl KnownForallInstantiationResult {
    pub fn new(
        cite_what: Stmt,
        source_fact_id: Option<FactId>,
        instantiation: Vec<KnownForallInstantiationItem>,
        requirements: Vec<KnownForallRequirementResult>,
    ) -> Self {
        KnownForallInstantiationResult {
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

impl ForallProofResult {
    pub fn new(
        forall_fact: ForallFact,
        assumption_infers: InferResult,
        proves: Vec<ForallProvedFactResult>,
    ) -> Self {
        ForallProofResult {
            forall_fact,
            assumption_infers,
            proves,
        }
    }
}

impl ForallProvedFactResult {
    pub fn new(stmt: ExistOrAndChainAtomicFact, result: StmtResult) -> Self {
        ForallProvedFactResult {
            stmt,
            result: Box::new(result),
        }
    }
}

impl fmt::Debug for ForallProofResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("ForallProofResult")
            .field("forall_fact", &self.forall_fact.to_string())
            .field("assumption_infers", &self.assumption_infers)
            .field("proves", &self.proves)
            .finish()
    }
}

impl fmt::Debug for ForallProvedFactResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("ForallProvedFactResult")
            .field("stmt", &self.stmt.to_string())
            .field("result", &self.result)
            .finish()
    }
}

impl NonFactualStmtSuccess {
    pub fn new(stmt: Stmt, infers: InferResult, inside_results: Vec<StmtResult>) -> Self {
        NonFactualStmtSuccess {
            stmt,
            litex_to_lean_ir: None,
            well_definedness: WellDefinednessCertificate::default(),
            infers,
            reported_store_facts: vec![],
            inside_results,
            execution_trace: None,
            theorem_verification: None,
            claim_verification: None,
            object_choice_verification: None,
            witness_exist_verification: None,
            witness_atomic_fact_verification: None,
            existential_elimination_verification: None,
            function_definition_verification: None,
            by_verification: None,
        }
    }

    pub fn new_with_theorem_verification(
        stmt: Stmt,
        infers: InferResult,
        inside_results: Vec<StmtResult>,
        theorem_verification: TheoremVerificationResult,
    ) -> Self {
        NonFactualStmtSuccess {
            stmt,
            litex_to_lean_ir: None,
            well_definedness: WellDefinednessCertificate::default(),
            infers,
            reported_store_facts: vec![],
            inside_results,
            execution_trace: None,
            theorem_verification: Some(theorem_verification),
            claim_verification: None,
            object_choice_verification: None,
            witness_exist_verification: None,
            witness_atomic_fact_verification: None,
            existential_elimination_verification: None,
            function_definition_verification: None,
            by_verification: None,
        }
    }

    pub fn new_with_claim_verification(
        stmt: Stmt,
        infers: InferResult,
        inside_results: Vec<StmtResult>,
        claim_verification: ClaimVerificationResult,
    ) -> Self {
        NonFactualStmtSuccess {
            stmt,
            litex_to_lean_ir: None,
            well_definedness: WellDefinednessCertificate::default(),
            infers,
            reported_store_facts: vec![],
            inside_results,
            execution_trace: None,
            theorem_verification: None,
            claim_verification: Some(claim_verification),
            object_choice_verification: None,
            witness_exist_verification: None,
            witness_atomic_fact_verification: None,
            existential_elimination_verification: None,
            function_definition_verification: None,
            by_verification: None,
        }
    }

    pub fn new_with_by_verification(
        stmt: Stmt,
        infers: InferResult,
        inside_results: Vec<StmtResult>,
        by_verification: ByVerificationResult,
    ) -> Self {
        NonFactualStmtSuccess {
            stmt,
            litex_to_lean_ir: None,
            well_definedness: WellDefinednessCertificate::default(),
            infers,
            reported_store_facts: vec![],
            inside_results,
            execution_trace: None,
            theorem_verification: None,
            claim_verification: None,
            object_choice_verification: None,
            witness_exist_verification: None,
            witness_atomic_fact_verification: None,
            existential_elimination_verification: None,
            function_definition_verification: None,
            by_verification: Some(by_verification),
        }
    }

    pub fn new_with_stmt(stmt: Stmt) -> Self {
        Self::new(stmt, InferResult::new(), vec![])
    }

    pub fn with_reported_store_facts(mut self, reported_store_facts: Vec<StoreFactOutput>) -> Self {
        self.reported_store_facts = reported_store_facts;
        self
    }
}

impl TheoremVerificationResult {
    pub fn new(
        name: String,
        forall_fact: ForallFact,
        assumption_infers: InferResult,
        proof_step_count: usize,
    ) -> Self {
        TheoremVerificationResult {
            name,
            forall_fact,
            assumption_infers,
            proof_step_count,
        }
    }
}

impl ClaimForallVerificationResult {
    pub fn new(
        forall_fact: ForallFact,
        assumption_infers: InferResult,
        proof_step_count: usize,
    ) -> Self {
        ClaimForallVerificationResult {
            forall_fact,
            assumption_infers,
            proof_step_count,
        }
    }
}

impl ClaimFactVerificationResult {
    pub fn new(fact: Fact, proof_step_count: usize) -> Self {
        ClaimFactVerificationResult {
            fact,
            proof_step_count,
        }
    }
}

impl From<ClaimForallVerificationResult> for ClaimVerificationResult {
    fn from(v: ClaimForallVerificationResult) -> Self {
        ClaimVerificationResult::Forall(v)
    }
}

impl From<ClaimFactVerificationResult> for ClaimVerificationResult {
    fn from(v: ClaimFactVerificationResult) -> Self {
        ClaimVerificationResult::Fact(v)
    }
}

impl ByCasesVerificationResult {
    pub fn new(
        cases: Vec<AndChainAtomicFact>,
        case_fact_ids: Vec<FactId>,
        then_facts: Vec<Fact>,
        proof_step_counts: Vec<usize>,
        case_result_counts: Vec<usize>,
        impossible_facts: Vec<Option<AtomicFact>>,
    ) -> Self {
        ByCasesVerificationResult {
            cases,
            case_fact_ids,
            then_facts,
            proof_step_counts,
            case_result_counts,
            impossible_facts,
        }
    }
}

impl ByContraVerificationResult {
    pub fn new(
        to_prove: Fact,
        reverse_assumption: Fact,
        reverse_assumption_fact_id: FactId,
        proof_step_count: usize,
        impossible_fact: AtomicFact,
    ) -> Self {
        ByContraVerificationResult {
            to_prove,
            reverse_assumption,
            reverse_assumption_fact_id,
            proof_step_count,
            impossible_fact,
        }
    }
}

impl ByAssignmentVerificationResult {
    pub fn new(
        assignment: Vec<(String, String)>,
        assumptions: Vec<(String, String)>,
        domain_check_count: usize,
        proof_step_count: usize,
        conclusion_count: usize,
        skipped_domain: Option<String>,
        result_count: usize,
    ) -> Self {
        ByAssignmentVerificationResult {
            assignment,
            assumptions,
            domain_check_count,
            proof_step_count,
            conclusion_count,
            skipped_domain,
            result_count,
        }
    }
}

impl ByEnumerateFiniteSetVerificationResult {
    pub fn new(
        parameters: Vec<String>,
        parameter_sets: Vec<String>,
        prove_goal: String,
        assignments: Vec<ByAssignmentVerificationResult>,
        generated_forall: String,
    ) -> Self {
        ByEnumerateFiniteSetVerificationResult {
            parameters,
            parameter_sets,
            prove_goal,
            assignments,
            generated_forall,
        }
    }
}

impl ByForVerificationResult {
    pub fn new(
        iteration_mode: String,
        parameters: Vec<String>,
        domains: Vec<String>,
        prove_goal: String,
        assignments: Vec<ByAssignmentVerificationResult>,
        generated_forall: String,
    ) -> Self {
        ByForVerificationResult {
            iteration_mode,
            parameters,
            domains,
            prove_goal,
            assignments,
            generated_forall,
        }
    }
}

impl ByEnumerateRangeVerificationResult {
    pub fn new(
        proof_type: String,
        element: String,
        range: String,
        membership_fact: String,
        endpoint_facts: Vec<String>,
        generated_cases: String,
    ) -> Self {
        ByEnumerateRangeVerificationResult {
            proof_type,
            element,
            range,
            membership_fact,
            endpoint_facts,
            generated_cases,
        }
    }
}

impl ByInducVerificationResult {
    pub fn new(
        strong: bool,
        finite_set: bool,
        structured: bool,
        parameter: String,
        start: String,
        prove_goals: Vec<String>,
        generated_forall: String,
        proof_step_count: usize,
        base_assumptions: Vec<(String, String)>,
        base_proof_step_count: usize,
        base_result_count: usize,
        step_assumptions: Vec<(String, String)>,
        step_proof_step_count: usize,
        step_result_count: usize,
    ) -> Self {
        ByInducVerificationResult {
            strong,
            finite_set,
            structured,
            parameter,
            start,
            prove_goals,
            generated_forall,
            proof_step_count,
            base_assumptions,
            base_proof_step_count,
            base_result_count,
            step_assumptions,
            step_proof_step_count,
            step_result_count,
        }
    }
}

impl ByExtensionVerificationResult {
    pub fn new(
        left: String,
        right: String,
        prove_goal: String,
        proof_step_count: usize,
        left_to_right_subset: String,
        right_to_left_subset: String,
    ) -> Self {
        ByExtensionVerificationResult {
            left,
            right,
            prove_goal,
            proof_step_count,
            left_to_right_subset,
            right_to_left_subset,
        }
    }
}

impl ByPropRegistrationVerificationResult {
    pub fn new(
        registration_type: String,
        prop_name: String,
        forall_fact: ForallFact,
        assumption_infers: InferResult,
        proof_step_count: usize,
    ) -> Self {
        ByPropRegistrationVerificationResult {
            registration_type,
            prop_name,
            forall_fact,
            assumption_infers,
            proof_step_count,
        }
    }
}

impl ByChoiceVerificationResult {
    pub fn new(
        proof_type: String,
        target: String,
        proof_step_count: usize,
        obligations: Vec<(String, String, bool)>,
        trusted_conclusion: String,
    ) -> Self {
        ByChoiceVerificationResult {
            proof_type,
            target,
            proof_step_count,
            obligations,
            trusted_conclusion,
        }
    }
}

impl ByTheoremVerificationResult {
    pub fn new(
        theorem: String,
        arguments: Vec<String>,
        domain_facts: Vec<String>,
        stored_then_facts: Vec<String>,
    ) -> Self {
        let parent_stored_facts = stored_then_facts.clone();
        ByTheoremVerificationResult {
            theorem,
            theorem_source: "litex".to_string(),
            mode: "release_all".to_string(),
            arguments,
            domain_facts,
            requirement_roles: vec![],
            stored_then_facts,
            temporary_then_facts: vec![],
            selected_fact: None,
            parent_stored_facts,
            provenance: None,
        }
    }

    pub fn new_builtin(
        theorem: String,
        arguments: Vec<String>,
        requirement_facts: Vec<String>,
        requirement_roles: Vec<String>,
        stored_then_facts: Vec<String>,
        provenance: Option<String>,
    ) -> Self {
        let parent_stored_facts = stored_then_facts.clone();
        ByTheoremVerificationResult {
            theorem,
            theorem_source: "builtin_rule".to_string(),
            mode: "release_all".to_string(),
            arguments,
            domain_facts: requirement_facts,
            requirement_roles,
            stored_then_facts,
            temporary_then_facts: vec![],
            selected_fact: None,
            parent_stored_facts,
            provenance,
        }
    }

    pub fn select_atomic_fact(&mut self, selected_fact: String) {
        self.mode = "select_atomic_fact".to_string();
        self.temporary_then_facts = self.stored_then_facts.clone();
        self.stored_then_facts.clear();
        self.parent_stored_facts = vec![selected_fact.clone()];
        self.selected_fact = Some(selected_fact);
    }
}

impl ByDefinitionVerificationResult {
    pub fn new(
        prop: String,
        arguments: Vec<String>,
        definition_clauses: Vec<String>,
        stored_fact: String,
    ) -> Self {
        ByDefinitionVerificationResult {
            prop,
            arguments,
            definition_clauses,
            stored_fact,
        }
    }
}

impl From<ByCasesVerificationResult> for ByVerificationResult {
    fn from(v: ByCasesVerificationResult) -> Self {
        ByVerificationResult::Cases(v)
    }
}

impl From<ByContraVerificationResult> for ByVerificationResult {
    fn from(v: ByContraVerificationResult) -> Self {
        ByVerificationResult::Contra(v)
    }
}

impl From<ByEnumerateFiniteSetVerificationResult> for ByVerificationResult {
    fn from(v: ByEnumerateFiniteSetVerificationResult) -> Self {
        ByVerificationResult::EnumerateFiniteSet(v)
    }
}

impl From<ByEnumerateRangeVerificationResult> for ByVerificationResult {
    fn from(v: ByEnumerateRangeVerificationResult) -> Self {
        ByVerificationResult::EnumerateRange(v)
    }
}

impl From<ByInducVerificationResult> for ByVerificationResult {
    fn from(v: ByInducVerificationResult) -> Self {
        ByVerificationResult::Induc(v)
    }
}

impl From<ByForVerificationResult> for ByVerificationResult {
    fn from(v: ByForVerificationResult) -> Self {
        ByVerificationResult::For(v)
    }
}

impl From<ByExtensionVerificationResult> for ByVerificationResult {
    fn from(v: ByExtensionVerificationResult) -> Self {
        ByVerificationResult::Extension(v)
    }
}

impl From<ByPropRegistrationVerificationResult> for ByVerificationResult {
    fn from(v: ByPropRegistrationVerificationResult) -> Self {
        ByVerificationResult::PropRegistration(v)
    }
}

impl From<ByTheoremVerificationResult> for ByVerificationResult {
    fn from(v: ByTheoremVerificationResult) -> Self {
        ByVerificationResult::Theorem(v)
    }
}

impl From<ByDefinitionVerificationResult> for ByVerificationResult {
    fn from(v: ByDefinitionVerificationResult) -> Self {
        ByVerificationResult::Definition(v)
    }
}

impl fmt::Debug for ClaimVerificationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            ClaimVerificationResult::Forall(v) => f.debug_tuple("Forall").field(v).finish(),
            ClaimVerificationResult::Fact(v) => f.debug_tuple("Fact").field(v).finish(),
        }
    }
}

impl fmt::Debug for TheoremVerificationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("TheoremVerificationResult")
            .field("name", &self.name)
            .field("forall_fact", &self.forall_fact.to_string())
            .field("assumption_infers", &self.assumption_infers)
            .field("proof_step_count", &self.proof_step_count)
            .finish()
    }
}

impl fmt::Debug for ClaimForallVerificationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("ClaimForallVerificationResult")
            .field("forall_fact", &self.forall_fact.to_string())
            .field("assumption_infers", &self.assumption_infers)
            .field("proof_step_count", &self.proof_step_count)
            .finish()
    }
}

impl fmt::Debug for ClaimFactVerificationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("ClaimFactVerificationResult")
            .field("fact", &self.fact.to_string())
            .field("proof_step_count", &self.proof_step_count)
            .finish()
    }
}

impl fmt::Debug for ByVerificationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            ByVerificationResult::Cases(v) => f.debug_tuple("Cases").field(v).finish(),
            ByVerificationResult::Contra(v) => f.debug_tuple("Contra").field(v).finish(),
            ByVerificationResult::EnumerateFiniteSet(v) => {
                f.debug_tuple("EnumerateFiniteSet").field(v).finish()
            }
            ByVerificationResult::EnumerateRange(v) => {
                f.debug_tuple("EnumerateRange").field(v).finish()
            }
            ByVerificationResult::Induc(v) => f.debug_tuple("Induc").field(v).finish(),
            ByVerificationResult::For(v) => f.debug_tuple("For").field(v).finish(),
            ByVerificationResult::Extension(v) => f.debug_tuple("Extension").field(v).finish(),
            ByVerificationResult::PropRegistration(v) => {
                f.debug_tuple("PropRegistration").field(v).finish()
            }
            ByVerificationResult::AxiomOfChoice(v) => {
                f.debug_tuple("AxiomOfChoice").field(v).finish()
            }
            ByVerificationResult::ZornLemma(v) => f.debug_tuple("ZornLemma").field(v).finish(),
            ByVerificationResult::RegularityAxiom(v) => {
                f.debug_tuple("RegularityAxiom").field(v).finish()
            }
            ByVerificationResult::Definition(v) => f.debug_tuple("Definition").field(v).finish(),
            ByVerificationResult::Theorem(v) => f.debug_tuple("Theorem").field(v).finish(),
        }
    }
}

impl fmt::Debug for ByCasesVerificationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let cases = self
            .cases
            .iter()
            .map(|case| case.to_string())
            .collect::<Vec<_>>();
        let then_facts = self
            .then_facts
            .iter()
            .map(|fact| fact.to_string())
            .collect::<Vec<_>>();
        let impossible_facts = self
            .impossible_facts
            .iter()
            .map(|fact| fact.as_ref().map(|f| f.to_string()))
            .collect::<Vec<_>>();
        f.debug_struct("ByCasesVerificationResult")
            .field("cases", &cases)
            .field("case_fact_ids", &self.case_fact_ids)
            .field("then_facts", &then_facts)
            .field("proof_step_counts", &self.proof_step_counts)
            .field("case_result_counts", &self.case_result_counts)
            .field("impossible_facts", &impossible_facts)
            .finish()
    }
}

impl fmt::Debug for ByContraVerificationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("ByContraVerificationResult")
            .field("to_prove", &self.to_prove.to_string())
            .field("reverse_assumption", &self.reverse_assumption.to_string())
            .field(
                "reverse_assumption_fact_id",
                &self.reverse_assumption_fact_id,
            )
            .field("proof_step_count", &self.proof_step_count)
            .field("impossible_fact", &self.impossible_fact.to_string())
            .finish()
    }
}

impl fmt::Debug for ByPropRegistrationVerificationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("ByPropRegistrationVerificationResult")
            .field("registration_type", &self.registration_type)
            .field("prop_name", &self.prop_name)
            .field("forall_fact", &self.forall_fact.to_string())
            .field("assumption_infers", &self.assumption_infers)
            .field("proof_step_count", &self.proof_step_count)
            .finish()
    }
}

fn merge_verified_by_with_steps(
    _goal: Fact,
    verified_by: VerifiedByResult,
    step_results: Vec<StmtResult>,
) -> VerifiedByResult {
    if step_results.is_empty() {
        return verified_by;
    }
    let mut items = VerifiedBysEnum::from_verified_by_result(_goal, verified_by);
    for r in step_results {
        items.extend(verified_by_items_from_stmt_result(r));
    }
    VerifiedByResult::wrap_bys(items)
}

fn verified_by_items_from_stmt_result(result: StmtResult) -> Vec<VerifiedBysEnum> {
    match result {
        StmtResult::Fact(fact_result) => {
            if let Some(f) = (*fact_result).into_success() {
                VerifiedBysEnum::from_verified_by_result(f.stmt, f.verified_by)
            } else {
                Vec::new()
            }
        }
        other => {
            let inside_results = other
                .into_non_factual_success()
                .map(|n| n.inside_results)
                .unwrap_or_default();
            inside_results
                .into_iter()
                .flat_map(verified_by_items_from_stmt_result)
                .collect::<Vec<_>>()
        }
    }
}
