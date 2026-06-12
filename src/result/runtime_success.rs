use crate::prelude::*;
use std::fmt;

#[derive(Debug)]
pub struct NonFactualStmtSuccess {
    pub stmt: Stmt,
    pub infers: InferResult,
    pub inside_results: Vec<StmtResult>,
    pub claim_verification: Option<ClaimVerificationResult>,
    pub by_verification: Option<ByVerificationResult>,
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
            inside_results,
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
            inside_results,
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
            inside_results,
            claim_verification: None,
            by_verification: Some(by_verification),
        }
    }

    pub fn new_with_stmt(stmt: Stmt) -> Self {
        Self::new(stmt, InferResult::new(), vec![])
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

impl fmt::Debug for ClaimVerificationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ClaimVerificationResult::Forall(v) => f.debug_tuple("Forall").field(v).finish(),
            ClaimVerificationResult::Fact(v) => f.debug_tuple("Fact").field(v).finish(),
        }
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
