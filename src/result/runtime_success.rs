use crate::prelude::*;

#[derive(Debug)]
pub struct NonFactualStmtSuccess {
    pub stmt: Stmt,
    pub infers: InferResult,
    pub inside_results: Vec<StmtResult>,
}

#[derive(Debug)]
pub enum VerifiedByResult {
    BuiltinRules(String),
    Fact(Fact, String),
    Step(Box<StmtResult>),
    VerifiedBys(Vec<Box<VerifiedByResult>>),
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
            VerifiedByResult::BuiltinRules(builtin_rule_label),
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
            VerifiedByResult::BuiltinRules(builtin_rule_label),
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
        let verified_by = merge_verified_by_with_steps(verified_by, step_results);
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
    pub fn tree_is_builtin_rules_only(&self) -> bool {
        match self {
            VerifiedByResult::BuiltinRules(s) => !s.is_empty(),
            VerifiedByResult::Fact(_, _) => false,
            VerifiedByResult::Step(r) => match r.as_ref() {
                StmtResult::FactualStmtSuccess(f) => f.is_verified_by_builtin_rules_only(),
                StmtResult::NonFactualStmtSuccess(_) | StmtResult::StmtUnknown(_) => false,
            },
            VerifiedByResult::VerifiedBys(items) => {
                !items.is_empty() && items.iter().all(|b| b.tree_is_builtin_rules_only())
            }
        }
    }

    pub fn first_builtin_rule_label(&self) -> Option<&str> {
        match self {
            VerifiedByResult::BuiltinRules(s) => {
                if s.is_empty() {
                    None
                } else {
                    Some(s.as_str())
                }
            }
            VerifiedByResult::VerifiedBys(items) => {
                for b in items.iter() {
                    if let VerifiedByResult::BuiltinRules(s) = &**b {
                        if !s.is_empty() {
                            return Some(s.as_str());
                        }
                    }
                }
                for b in items.iter() {
                    if let Some(l) = b.first_builtin_rule_label() {
                        return Some(l);
                    }
                }
                None
            }
            VerifiedByResult::Step(r) => match r.as_ref() {
                StmtResult::FactualStmtSuccess(f) => f.verified_by.first_builtin_rule_label(),
                StmtResult::NonFactualStmtSuccess(_) | StmtResult::StmtUnknown(_) => None,
            },
            VerifiedByResult::Fact(_, _) => None,
        }
    }

    pub fn composite_step_stmt_results_in_order(v: &VerifiedByResult) -> Vec<&StmtResult> {
        let mut out = Vec::new();
        Self::collect_steps(v, &mut out);
        out
    }

    fn collect_steps<'a>(v: &'a VerifiedByResult, out: &mut Vec<&'a StmtResult>) {
        match v {
            VerifiedByResult::Step(r) => out.push(r),
            VerifiedByResult::VerifiedBys(items) => {
                for b in items {
                    Self::collect_steps(b, out);
                }
            }
            VerifiedByResult::BuiltinRules(_) | VerifiedByResult::Fact(_, _) => {}
        }
    }

    fn first_cited_fact_line_file(&self) -> Option<LineFile> {
        match self {
            VerifiedByResult::BuiltinRules(_) => None,
            VerifiedByResult::Fact(f, _) => Some(f.line_file()),
            VerifiedByResult::Step(r) => match r.as_ref() {
                StmtResult::FactualStmtSuccess(f) => {
                    Some(f.line_file_for_verified_by_known_fact_in_json())
                }
                StmtResult::NonFactualStmtSuccess(n) => Some(n.stmt.line_file()),
                StmtResult::StmtUnknown(_) => None,
            },
            VerifiedByResult::VerifiedBys(items) => {
                for b in items {
                    if let Some(lf) = b.first_cited_fact_line_file() {
                        return Some(lf);
                    }
                }
                None
            }
        }
    }
}

impl VerifiedByResult {
    pub fn display_line(&self) -> String {
        match self {
            VerifiedByResult::BuiltinRules(s) => s.clone(),
            VerifiedByResult::Fact(f, detail) => {
                if !detail.is_empty() {
                    detail.clone()
                } else {
                    f.to_string()
                }
            }
            VerifiedByResult::Step(r) => match r.as_ref() {
                StmtResult::FactualStmtSuccess(f) => f.verification_display_line(),
                StmtResult::NonFactualStmtSuccess(n) => n.stmt.to_string(),
                StmtResult::StmtUnknown(u) => u.to_string(),
            },
            VerifiedByResult::VerifiedBys(items) => {
                if items.is_empty() {
                    return String::new();
                }
                items
                    .iter()
                    .map(|b| b.display_line())
                    .collect::<Vec<_>>()
                    .join("; ")
            }
        }
    }

    pub fn wrap_bys(children: Vec<VerifiedByResult>) -> Self {
        VerifiedByResult::VerifiedBys(children.into_iter().map(Box::new).collect())
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
    verified_by: VerifiedByResult,
    step_results: Vec<StmtResult>,
) -> VerifiedByResult {
    if step_results.is_empty() {
        return verified_by;
    }
    let mut items: Vec<VerifiedByResult> = match verified_by {
        VerifiedByResult::VerifiedBys(inner) => inner.into_iter().map(|b| *b).collect(),
        other => vec![other],
    };
    for r in step_results {
        items.push(VerifiedByResult::Step(Box::new(r)));
    }
    VerifiedByResult::wrap_bys(items)
}
