use crate::prelude::*;
use std::fmt;

#[derive(Debug)]
pub struct NonFactualStmtSuccess {
    pub stmt: Stmt,
    pub infers: InferResult,
    pub inside_results: Vec<StmtResult>,
    pub accepted_by: AcceptedByResult,
}

#[derive(Debug)]
pub struct AcceptedByResult {
    pub kind: Box<AcceptedByKind>,
    pub introduces: Vec<ObjectIntroductionItem>,
}

#[derive(Debug)]
pub enum AcceptedByKind {
    Assumption,
    Definition,
    ObjectIntroduction,
    ExistElimination,
    ProofBlock {
        proved: Option<Fact>,
        steps_count: usize,
    },
    CaseSplit {
        goals: Vec<Fact>,
        coverage: Option<CaseSplitCoverage>,
        cases: Vec<CaseSplitAcceptedBy>,
    },
    TheoremCall,
    Witness,
    NoOp,
    Evaluation,
    Command,
    VerifiedFact,
}

#[derive(Clone, Debug)]
pub struct ObjectIntroductionItem {
    pub name: String,
    pub facts: Vec<Fact>,
}

pub struct CaseSplitAcceptedBy {
    pub case_fact: AndChainAtomicFact,
    pub impossible_fact: Option<AtomicFact>,
    pub inside_results: Vec<StmtResult>,
}

pub struct CaseSplitCoverage {
    pub fact: Fact,
    pub result: Box<StmtResult>,
}

#[derive(Debug)]
pub struct VerifiedByBuiltinRuleResult {
    pub msg: String,
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
        let verified_by = merge_verified_by_with_steps(
            stmt.clone(),
            VerifiedByResult::builtin_rule(builtin_rule_label, stmt.clone()),
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
        let verified_by = merge_verified_by_with_steps(
            stmt.clone(),
            VerifiedByResult::builtin_rule(builtin_rule_label, stmt.clone()),
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
        Self::BuiltinRule(VerifiedByBuiltinRuleResult { msg: msg.into() })
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

    pub fn forall_proof(forall_fact: ForallFact, then_results: Vec<StmtResult>) -> Self {
        let mut proves = Vec::new();
        for (stmt, result) in forall_fact
            .then_facts
            .iter()
            .cloned()
            .zip(then_results.into_iter())
        {
            proves.push(ForallProvedFactResult::new(stmt, result));
        }
        Self::ForallProof(ForallProofResult::new(forall_fact, proves))
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
    pub fn builtin_rule(msg: String, verify_what: Fact) -> Self {
        VerifiedBysEnum::ByBuiltinRule(FactVerifiedByBuiltinRuleInVerifiedBys { msg, verify_what })
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
            VerifiedByResult::BuiltinRule(r) => vec![Self::builtin_rule(r.msg, verify_what)],
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

impl AcceptedByResult {
    pub fn new(kind: AcceptedByKind) -> Self {
        AcceptedByResult {
            kind: Box::new(kind),
            introduces: Vec::new(),
        }
    }

    pub fn from_stmt(stmt: &Stmt, steps_count: usize) -> Self {
        match stmt {
            Stmt::UnsafeStmt(UnsafeStmt::KnowStmt(_)) => Self::new(AcceptedByKind::Assumption),
            Stmt::UnsafeStmt(UnsafeStmt::DefLetStmt(_)) => Self::new(AcceptedByKind::Definition),
            Stmt::DefObjStmt(DefObjStmt::HaveObjByExistFactsStmt(_))
            | Stmt::DefObjStmt(DefObjStmt::HaveByExistStmt(_)) => {
                Self::new(AcceptedByKind::ExistElimination)
            }
            Stmt::DefObjStmt(_) => Self::new(AcceptedByKind::Definition),
            Stmt::DefInterfaceStmt(DefInterfaceStmt::DefThmStmt(_))
            | Stmt::DefInterfaceStmt(DefInterfaceStmt::DefStrategyStmt(_))
            | Stmt::ProofBlock(_) => Self::proof_block(None, steps_count),
            Stmt::DefInterfaceStmt(_) => Self::new(AcceptedByKind::Definition),
            Stmt::By(ByStmt::ByCasesStmt(_)) => Self::case_split(vec![], vec![]),
            Stmt::By(ByStmt::ByThmStmt(_)) => Self::new(AcceptedByKind::TheoremCall),
            Stmt::By(_) => Self::proof_block(None, steps_count),
            Stmt::Witness(_) => Self::new(AcceptedByKind::Witness),
            Stmt::Command(CommandStmt::DoNothingStmt(_)) => Self::new(AcceptedByKind::NoOp),
            Stmt::Command(CommandStmt::EvalStmt(_)) | Stmt::Command(CommandStmt::EvalByStmt(_)) => {
                Self::new(AcceptedByKind::Evaluation)
            }
            Stmt::Command(_) => Self::new(AcceptedByKind::Command),
            Stmt::Fact(_) => Self::new(AcceptedByKind::VerifiedFact),
        }
    }

    pub fn proof_block(proved: Option<Fact>, steps_count: usize) -> Self {
        Self::new(AcceptedByKind::ProofBlock {
            proved,
            steps_count,
        })
    }

    pub fn case_split(goals: Vec<Fact>, cases: Vec<CaseSplitAcceptedBy>) -> Self {
        Self::case_split_with_coverage(goals, None, cases)
    }

    pub fn case_split_with_coverage(
        goals: Vec<Fact>,
        coverage: Option<CaseSplitCoverage>,
        cases: Vec<CaseSplitAcceptedBy>,
    ) -> Self {
        Self::new(AcceptedByKind::CaseSplit {
            goals,
            coverage,
            cases,
        })
    }

    pub fn exist_elimination() -> Self {
        Self::new(AcceptedByKind::ExistElimination)
    }

    pub fn object_introduction(introduces: Vec<ObjectIntroductionItem>) -> Self {
        let mut result = Self::new(AcceptedByKind::ObjectIntroduction);
        result.introduces = introduces;
        result
    }

    pub fn exist_elimination_with_introduces(introduces: Vec<ObjectIntroductionItem>) -> Self {
        let mut result = Self::exist_elimination();
        result.introduces = introduces;
        result
    }
}

impl ObjectIntroductionItem {
    pub fn new(name: String, facts: Vec<Fact>) -> Self {
        ObjectIntroductionItem { name, facts }
    }
}

impl CaseSplitAcceptedBy {
    pub fn new(
        case_fact: AndChainAtomicFact,
        impossible_fact: Option<AtomicFact>,
        inside_results: Vec<StmtResult>,
    ) -> Self {
        CaseSplitAcceptedBy {
            case_fact,
            impossible_fact,
            inside_results,
        }
    }
}

impl CaseSplitCoverage {
    pub fn new(fact: Fact, result: StmtResult) -> Self {
        CaseSplitCoverage {
            fact,
            result: Box::new(result),
        }
    }
}

impl ForallProofResult {
    pub fn new(forall_fact: ForallFact, proves: Vec<ForallProvedFactResult>) -> Self {
        ForallProofResult {
            forall_fact,
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

impl fmt::Debug for CaseSplitCoverage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CaseSplitCoverage")
            .field("fact", &self.fact.to_string())
            .field("result", &self.result)
            .finish()
    }
}

impl fmt::Debug for CaseSplitAcceptedBy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CaseSplitAcceptedBy")
            .field("case_fact", &self.case_fact.to_string())
            .field(
                "impossible_fact",
                &self.impossible_fact.as_ref().map(|fact| fact.to_string()),
            )
            .field("inside_results", &self.inside_results)
            .finish()
    }
}

impl NonFactualStmtSuccess {
    pub fn new(stmt: Stmt, infers: InferResult, inside_results: Vec<StmtResult>) -> Self {
        let accepted_by = AcceptedByResult::from_stmt(&stmt, inside_results.len());
        Self::new_with_accepted_by(stmt, infers, inside_results, accepted_by)
    }

    pub fn new_with_accepted_by(
        stmt: Stmt,
        infers: InferResult,
        inside_results: Vec<StmtResult>,
        accepted_by: AcceptedByResult,
    ) -> Self {
        NonFactualStmtSuccess {
            stmt,
            infers,
            inside_results,
            accepted_by,
        }
    }

    pub fn new_with_stmt(stmt: Stmt) -> Self {
        Self::new(stmt, InferResult::new(), vec![])
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
