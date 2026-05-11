use crate::prelude::*;

#[derive(Debug)]
pub struct NonFactualStmtSuccess {
    pub stmt: Stmt,
    pub infers: InferResult,
    pub inside_results: Vec<StmtResult>,
}

#[derive(Debug)]
pub struct VerifiedByBuiltinRuleResult {
    pub msg: String,
}

#[derive(Debug)]
pub struct VerifiedByFactResult {
    pub detail: Option<String>,
    pub cite_what: Stmt,
    pub children: Vec<VerifiedBysEnum>,
}

#[derive(Debug)]
pub struct VerifiedBysResult {
    pub cite_what: Vec<VerifiedBysEnum>,
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
    pub cite_what: Stmt,
    pub children: Vec<VerifiedBysEnum>,
}

#[derive(Debug)]
pub enum VerifiedBysEnum {
    ByBuiltinRule(FactVerifiedByBuiltinRuleInVerifiedBys),
    ByFact(FactVerifiedByFactInVerifiedBys),
}

#[derive(Debug)]
pub enum VerifiedByResult {
    BuiltinRule(VerifiedByBuiltinRuleResult),
    Fact(VerifiedByFactResult),
    VerifiedBys(VerifiedBysResult),
}

#[derive(Debug)]
pub struct FactualStmtSuccess {
    pub stmt: Fact,
    pub infers: InferResult,
    pub verified_by: VerifiedByResult,
}

impl FactualStmtSuccess {
    pub fn verification_display_line(&self) -> String {
        self.verified_by.display_line()
    }

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
        let infers = InferResult::from_fact(&stmt);
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

    pub fn line_file_for_verified_by_known_fact_in_json(&self) -> LineFile {
        self.verified_by
            .first_cited_fact_line_file()
            .unwrap_or_else(|| self.stmt.line_file())
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
        Self::cited_stmt_with_children(_goal, cite_what, detail, Vec::new())
    }

    pub fn cited_stmt_with_children(
        _goal: Fact,
        cite_what: Stmt,
        detail: Option<String>,
        children: Vec<VerifiedBysEnum>,
    ) -> Self {
        Self::Fact(VerifiedByFactResult {
            detail,
            cite_what,
            children,
        })
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
            cite_what: cite_what.into_stmt(),
            children: Vec::new(),
        })
    }

    pub fn wrap_bys(children: Vec<VerifiedBysEnum>) -> Self {
        Self::VerifiedBys(VerifiedBysResult {
            cite_what: children,
        })
    }

    pub fn tree_is_builtin_rules_only(&self) -> bool {
        match self {
            VerifiedByResult::BuiltinRule(r) => !r.msg.is_empty(),
            VerifiedByResult::Fact(_) => false,
            VerifiedByResult::VerifiedBys(w) => {
                !w.cite_what.is_empty() && w.cite_what.iter().all(|b| b.is_builtin_rule())
            }
        }
    }

    pub fn first_builtin_rule_label(&self) -> Option<&str> {
        match self {
            VerifiedByResult::BuiltinRule(r) => {
                if r.msg.is_empty() {
                    None
                } else {
                    Some(r.msg.as_str())
                }
            }
            VerifiedByResult::VerifiedBys(w) => {
                for b in w.cite_what.iter() {
                    if let VerifiedBysEnum::ByBuiltinRule(r) = b {
                        return Some(r.msg.as_str());
                    }
                }
                for b in w.cite_what.iter() {
                    if let Some(l) = b.first_builtin_rule_label() {
                        return Some(l);
                    }
                }
                None
            }
            VerifiedByResult::Fact(_) => None,
        }
    }

    fn first_cited_fact_line_file(&self) -> Option<LineFile> {
        match self {
            VerifiedByResult::BuiltinRule(_) => None,
            VerifiedByResult::Fact(r) => Some(r.cite_what.line_file()),
            VerifiedByResult::VerifiedBys(w) => {
                for b in &w.cite_what {
                    if let Some(lf) = b.first_cited_fact_line_file() {
                        return Some(lf);
                    }
                }
                None
            }
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
        Self::cited_stmt_with_children(verify_what, cite_what, detail, Vec::new())
    }

    pub fn cited_stmt_with_children(
        verify_what: Fact,
        cite_what: Stmt,
        detail: Option<String>,
        children: Vec<VerifiedBysEnum>,
    ) -> Self {
        VerifiedBysEnum::ByFact(FactVerifiedByFactInVerifiedBys {
            detail,
            verify_what,
            cite_what,
            children,
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
                vec![Self::cited_stmt_with_children(
                    verify_what,
                    r.cite_what,
                    r.detail,
                    r.children,
                )]
            }
            VerifiedByResult::VerifiedBys(w) => w.cite_what,
        }
    }

    fn is_builtin_rule(&self) -> bool {
        match self {
            VerifiedBysEnum::ByBuiltinRule(r) => !r.msg.is_empty(),
            VerifiedBysEnum::ByFact(_) => false,
        }
    }

    fn first_builtin_rule_label(&self) -> Option<&str> {
        match self {
            VerifiedBysEnum::ByBuiltinRule(r) => Some(r.msg.as_str()),
            VerifiedBysEnum::ByFact(_) => None,
        }
    }

    fn first_cited_fact_line_file(&self) -> Option<LineFile> {
        match self {
            VerifiedBysEnum::ByBuiltinRule(_) => None,
            VerifiedBysEnum::ByFact(r) => Some(r.cite_what.line_file()),
        }
    }

    fn display_line(&self) -> String {
        match self {
            VerifiedBysEnum::ByBuiltinRule(r) => r.msg.clone(),
            VerifiedBysEnum::ByFact(r) => {
                if let Some(d) = &r.detail {
                    if !d.is_empty() {
                        return d.clone();
                    }
                }
                r.cite_what.to_string()
            }
        }
    }
}

impl VerifiedByResult {
    pub fn display_line(&self) -> String {
        match self {
            VerifiedByResult::BuiltinRule(r) => r.msg.clone(),
            VerifiedByResult::Fact(r) => {
                if let Some(d) = &r.detail {
                    if !d.is_empty() {
                        return d.clone();
                    }
                }
                r.cite_what.to_string()
            }
            VerifiedByResult::VerifiedBys(w) => {
                if w.cite_what.is_empty() {
                    return String::new();
                }
                w.cite_what
                    .iter()
                    .map(|b| b.display_line())
                    .collect::<Vec<_>>()
                    .join("; ")
            }
        }
    }
}

impl NonFactualStmtSuccess {
    pub fn new(stmt: Stmt, infers: InferResult, inside_results: Vec<StmtResult>) -> Self {
        NonFactualStmtSuccess {
            stmt,
            infers,
            inside_results,
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

pub(crate) fn verified_by_items_from_stmt_result(result: StmtResult) -> Vec<VerifiedBysEnum> {
    match result {
        StmtResult::FactualStmtSuccess(f) => {
            VerifiedBysEnum::from_verified_by_result(f.stmt, f.verified_by)
        }
        StmtResult::NonFactualStmtSuccess(n) => {
            let items = n
                .inside_results
                .into_iter()
                .flat_map(verified_by_items_from_stmt_result)
                .collect::<Vec<_>>();
            items
        }
        StmtResult::StmtUnknown(_) => Vec::new(),
    }
}
