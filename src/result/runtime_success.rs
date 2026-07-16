use crate::prelude::*;
use std::fmt;

#[derive(Debug)]
pub struct NonFactualStmtSuccess {
    pub stmt: Stmt,
    pub infers: InferResult,
    /// Stored facts selected for ordinary statement output. Most statements keep
    /// their environment effects in the detailed execution trace only; value-
    /// producing statements such as `eval` may expose their primary result.
    pub reported_store_facts: Vec<StoreFactOutput>,
    pub inside_results: Vec<StmtResult>,
    pub execution_trace: Option<StatementExecutionTrace>,
    pub theorem_verification: Option<TheoremVerificationResult>,
    pub claim_verification: Option<ClaimVerificationResult>,
    pub by_verification: Option<ByVerificationResult>,
}

pub struct TheoremVerificationResult {
    pub names: Vec<String>,
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
    Theorem(ByTheoremVerificationResult),
}

pub struct ByCasesVerificationResult {
    pub cases: Vec<AndChainAtomicFact>,
    pub then_facts: Vec<Fact>,
    pub proof_step_counts: Vec<usize>,
    pub case_result_counts: Vec<usize>,
    pub impossible_facts: Vec<Option<AtomicFact>>,
}

pub struct ByContraVerificationResult {
    pub to_prove: Fact,
    pub reverse_assumption: Fact,
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
    pub arguments: Vec<String>,
    pub domain_facts: Vec<String>,
    pub stored_then_facts: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct ObjectIntroductionItem {
    pub name: String,
    pub facts: Vec<Fact>,
}

#[derive(Debug)]
pub struct VerifiedByBuiltinRuleResult {
    pub msg: String,
    pub subgoals: Vec<StmtResult>,
}

#[derive(Debug)]
pub struct VerifiedByFactResult {
    pub detail: Option<String>,
    pub cite_what: Box<Stmt>,
}

#[derive(Debug)]
pub struct KnownForallInstantiationItem {
    pub param: String,
    pub arg: String,
}

#[derive(Debug)]
pub struct KnownForallRequirementResult {
    pub stmt: Fact,
    pub result: Box<StmtResult>,
}

#[derive(Debug)]
pub struct KnownForallInstantiationResult {
    pub cite_what: Box<Stmt>,
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
    pub subgoals: Vec<StmtResult>,
}

#[derive(Debug)]
pub struct FactVerifiedByFactInVerifiedBys {
    pub detail: Option<String>,
    pub verify_what: Fact,
    pub cite_what: Box<Stmt>,
}

#[derive(Debug)]
pub struct FactVerifiedByKnownForallInVerifiedBys {
    pub verify_what: Fact,
    pub result: KnownForallInstantiationResult,
}

#[derive(Debug)]
pub enum VerifiedBysEnum {
    ByBuiltinRule(FactVerifiedByBuiltinRuleInVerifiedBys),
    ByFact(FactVerifiedByFactInVerifiedBys),
    ByKnownForall(FactVerifiedByKnownForallInVerifiedBys),
}

#[derive(Debug)]
pub enum VerifiedByResult {
    BuiltinRule(VerifiedByBuiltinRuleResult),
    Fact(VerifiedByFactResult),
    KnownForallInstantiation(KnownForallInstantiationResult),
    VerifiedBys(VerifiedBysResult),
    ForallProof(ForallProofResult),
}

#[derive(Debug)]
pub struct FactualStmtSuccess {
    pub stmt: Fact,
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
        let verified_by = VerifiedByResult::builtin_rule_with_subgoals(
            builtin_rule_label,
            stmt.clone(),
            step_results,
        );
        Self::new_with_verified_by_builtin_rules(stmt, infers, verified_by)
    }

    pub fn new_with_verified_by_builtin_rules_label_and_steps(
        stmt: Fact,
        infers: InferResult,
        builtin_rule_label: String,
        step_results: Vec<StmtResult>,
    ) -> Self {
        let verified_by = VerifiedByResult::builtin_rule_with_subgoals(
            builtin_rule_label,
            stmt.clone(),
            step_results,
        );
        Self::new_with_verified_by_builtin_rules(stmt, infers, verified_by)
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

    pub fn is_verified_by_builtin_rules_only(&self) -> bool {
        self.verified_by.tree_is_builtin_rules_only()
    }
}

impl VerifiedByResult {
    pub fn builtin_rule(msg: impl Into<String>, _goal: Fact) -> Self {
        Self::builtin_rule_with_subgoals(msg, _goal, Vec::new())
    }

    pub fn builtin_rule_with_subgoals(
        msg: impl Into<String>,
        _goal: Fact,
        subgoals: Vec<StmtResult>,
    ) -> Self {
        Self::BuiltinRule(VerifiedByBuiltinRuleResult {
            msg: msg.into(),
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
        })
    }

    pub fn known_forall_instantiation(
        cite_what: Fact,
        instantiation: Vec<KnownForallInstantiationItem>,
        requirements: Vec<KnownForallRequirementResult>,
    ) -> Self {
        Self::KnownForallInstantiation(KnownForallInstantiationResult::new(
            cite_what.into_stmt(),
            instantiation,
            requirements,
        ))
    }

    /// Same statement as goal and citation; optional human note in `msg`.
    pub fn fact_with_note(goal: Fact, msg: Option<String>) -> Self {
        let cite_what = goal.clone();
        Self::cited_fact(goal, cite_what, msg)
    }

    pub fn cached_fact(fact: Fact, cite_fact_source: LineFile) -> Self {
        let cite_what = fact.with_line_file(cite_fact_source);
        Self::Fact(VerifiedByFactResult {
            detail: None,
            cite_what: Box::new(cite_what.into_stmt()),
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
            VerifiedByResult::BuiltinRule(r) => !r.msg.is_empty(),
            VerifiedByResult::Fact(_) => false,
            VerifiedByResult::KnownForallInstantiation(_) => false,
            VerifiedByResult::VerifiedBys(w) => {
                !w.cite_what.is_empty() && w.cite_what.iter().all(|b| b.is_builtin_rule())
            }
            VerifiedByResult::ForallProof(_) => false,
        }
    }
}

impl VerifiedBysEnum {
    pub fn builtin_rule(msg: String, verify_what: Fact, subgoals: Vec<StmtResult>) -> Self {
        VerifiedBysEnum::ByBuiltinRule(FactVerifiedByBuiltinRuleInVerifiedBys {
            msg,
            verify_what,
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
                vec![Self::builtin_rule(r.msg, verify_what, r.subgoals)]
            }
            VerifiedByResult::Fact(r) => {
                vec![Self::cited_stmt(verify_what, *r.cite_what, r.detail)]
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
        }
    }

    fn is_builtin_rule(&self) -> bool {
        match self {
            VerifiedBysEnum::ByBuiltinRule(r) => !r.msg.is_empty(),
            VerifiedBysEnum::ByFact(_) | VerifiedBysEnum::ByKnownForall(_) => false,
        }
    }
}

impl KnownForallInstantiationItem {
    pub fn new(param: String, arg: String) -> Self {
        KnownForallInstantiationItem { param, arg }
    }
}

impl KnownForallRequirementResult {
    pub fn new(stmt: Fact, result: StmtResult) -> Self {
        KnownForallRequirementResult {
            stmt,
            result: Box::new(result),
        }
    }
}

impl KnownForallInstantiationResult {
    pub fn new(
        cite_what: Stmt,
        instantiation: Vec<KnownForallInstantiationItem>,
        requirements: Vec<KnownForallRequirementResult>,
    ) -> Self {
        KnownForallInstantiationResult {
            cite_what: Box::new(cite_what),
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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ForallProofResult")
            .field("forall_fact", &self.forall_fact.to_string())
            .field("assumption_infers", &self.assumption_infers)
            .field("proves", &self.proves)
            .finish()
    }
}

impl fmt::Debug for ForallProvedFactResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
            infers,
            reported_store_facts: vec![],
            inside_results,
            execution_trace: None,
            theorem_verification: None,
            claim_verification: None,
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
            infers,
            reported_store_facts: vec![],
            inside_results,
            execution_trace: None,
            theorem_verification: Some(theorem_verification),
            claim_verification: None,
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
            infers,
            reported_store_facts: vec![],
            inside_results,
            execution_trace: None,
            theorem_verification: None,
            claim_verification: Some(claim_verification),
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
            infers,
            reported_store_facts: vec![],
            inside_results,
            execution_trace: None,
            theorem_verification: None,
            claim_verification: None,
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
        names: Vec<String>,
        forall_fact: ForallFact,
        assumption_infers: InferResult,
        proof_step_count: usize,
    ) -> Self {
        TheoremVerificationResult {
            names,
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
        then_facts: Vec<Fact>,
        proof_step_counts: Vec<usize>,
        case_result_counts: Vec<usize>,
        impossible_facts: Vec<Option<AtomicFact>>,
    ) -> Self {
        ByCasesVerificationResult {
            cases,
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
        proof_step_count: usize,
        impossible_fact: AtomicFact,
    ) -> Self {
        ByContraVerificationResult {
            to_prove,
            reverse_assumption,
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
        ByTheoremVerificationResult {
            theorem,
            arguments,
            domain_facts,
            stored_then_facts,
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

impl fmt::Debug for ClaimVerificationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ClaimVerificationResult::Forall(v) => f.debug_tuple("Forall").field(v).finish(),
            ClaimVerificationResult::Fact(v) => f.debug_tuple("Fact").field(v).finish(),
        }
    }
}

impl fmt::Debug for TheoremVerificationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TheoremVerificationResult")
            .field("names", &self.names)
            .field("forall_fact", &self.forall_fact.to_string())
            .field("assumption_infers", &self.assumption_infers)
            .field("proof_step_count", &self.proof_step_count)
            .finish()
    }
}

impl fmt::Debug for ClaimForallVerificationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ClaimForallVerificationResult")
            .field("forall_fact", &self.forall_fact.to_string())
            .field("assumption_infers", &self.assumption_infers)
            .field("proof_step_count", &self.proof_step_count)
            .finish()
    }
}

impl fmt::Debug for ClaimFactVerificationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ClaimFactVerificationResult")
            .field("fact", &self.fact.to_string())
            .field("proof_step_count", &self.proof_step_count)
            .finish()
    }
}

impl fmt::Debug for ByVerificationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
            ByVerificationResult::Theorem(v) => f.debug_tuple("Theorem").field(v).finish(),
        }
    }
}

impl fmt::Debug for ByCasesVerificationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
            .field("then_facts", &then_facts)
            .field("proof_step_counts", &self.proof_step_counts)
            .field("case_result_counts", &self.case_result_counts)
            .field("impossible_facts", &impossible_facts)
            .finish()
    }
}

impl fmt::Debug for ByContraVerificationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ByContraVerificationResult")
            .field("to_prove", &self.to_prove.to_string())
            .field("reverse_assumption", &self.reverse_assumption.to_string())
            .field("proof_step_count", &self.proof_step_count)
            .field("impossible_fact", &self.impossible_fact.to_string())
            .finish()
    }
}

impl fmt::Debug for ByPropRegistrationVerificationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
