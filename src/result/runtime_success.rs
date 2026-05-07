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
    pub verify_what: Fact,
}

#[derive(Debug)]
pub struct VerifiedByFactResult {
    pub msg: Option<String>,
    pub verify_what: Fact,
    pub cite_what: Fact,
}

#[derive(Debug)]
pub struct VerifiedByVerifiedBysResult {
    pub verify_what: Fact,
    pub cite_what: Vec<Box<VerifiedByResult>>,
}

#[derive(Debug)]
pub enum VerifiedByResult {
    BuiltinRule(VerifiedByBuiltinRuleResult),
    Fact(VerifiedByFactResult),
    VerifiedBys(VerifiedByVerifiedBysResult),
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
    pub fn builtin_rule(msg: impl Into<String>, verify_what: Fact) -> Self {
        Self::BuiltinRule(VerifiedByBuiltinRuleResult {
            msg: msg.into(),
            verify_what,
        })
    }

    /// Goal `verify_what` justified by citing `cite_what`.
    pub fn cited_fact(verify_what: Fact, cite_what: Fact, msg: Option<String>) -> Self {
        Self::Fact(VerifiedByFactResult {
            msg,
            verify_what,
            cite_what,
        })
    }

    /// Same statement as goal and citation; optional human note in `msg`.
    pub fn fact_with_note(verify_what: Fact, msg: Option<String>) -> Self {
        let cite_what = verify_what.clone();
        Self::cited_fact(verify_what, cite_what, msg)
    }

    pub fn wrap_bys(verify_what: Fact, children: Vec<VerifiedByResult>) -> Self {
        Self::VerifiedBys(VerifiedByVerifiedBysResult {
            verify_what,
            cite_what: children.into_iter().map(Box::new).collect(),
        })
    }

    fn primary_verify_what(&self) -> &Fact {
        match self {
            VerifiedByResult::BuiltinRule(r) => &r.verify_what,
            VerifiedByResult::Fact(r) => &r.verify_what,
            VerifiedByResult::VerifiedBys(r) => &r.verify_what,
        }
    }

    pub fn tree_is_builtin_rules_only(&self) -> bool {
        match self {
            VerifiedByResult::BuiltinRule(r) => !r.msg.is_empty(),
            VerifiedByResult::Fact(_) => false,
            VerifiedByResult::VerifiedBys(w) => {
                !w.cite_what.is_empty()
                    && w.cite_what.iter().all(|b| b.tree_is_builtin_rules_only())
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
                    if let VerifiedByResult::BuiltinRule(r) = &**b {
                        if !r.msg.is_empty() {
                            return Some(r.msg.as_str());
                        }
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

impl VerifiedByResult {
    pub fn display_line(&self) -> String {
        match self {
            VerifiedByResult::BuiltinRule(r) => r.msg.clone(),
            VerifiedByResult::Fact(r) => {
                if let Some(d) = &r.msg {
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

fn patch_verify_what_root(outer: Fact, v: VerifiedByResult) -> VerifiedByResult {
    match v {
        VerifiedByResult::BuiltinRule(mut r) => {
            r.verify_what = outer;
            VerifiedByResult::BuiltinRule(r)
        }
        VerifiedByResult::Fact(mut r) => {
            r.verify_what = outer;
            VerifiedByResult::Fact(r)
        }
        VerifiedByResult::VerifiedBys(mut w) => {
            w.verify_what = outer;
            VerifiedByResult::VerifiedBys(w)
        }
    }
}

fn merge_verified_by_with_steps(
    verify_what: Fact,
    verified_by: VerifiedByResult,
    step_results: Vec<StmtResult>,
) -> VerifiedByResult {
    if step_results.is_empty() {
        return patch_verify_what_root(verify_what, verified_by);
    }
    let mut items: Vec<VerifiedByResult> = match verified_by {
        VerifiedByResult::VerifiedBys(w) => w.cite_what.into_iter().map(|b| *b).collect(),
        other => vec![other],
    };
    for r in step_results {
        if let Some(vb) = verified_by_from_stmt_result(r) {
            items.push(vb);
        }
    }
    VerifiedByResult::wrap_bys(verify_what, items)
}

pub(crate) fn verified_by_from_stmt_result(result: StmtResult) -> Option<VerifiedByResult> {
    match result {
        StmtResult::FactualStmtSuccess(f) => Some(f.verified_by),
        StmtResult::NonFactualStmtSuccess(n) => {
            let items = n
                .inside_results
                .into_iter()
                .filter_map(verified_by_from_stmt_result)
                .collect::<Vec<_>>();
            if items.is_empty() {
                None
            } else if items.len() == 1 {
                Some(items.into_iter().next().unwrap())
            } else {
                let verify_what = items[0].primary_verify_what().clone();
                Some(VerifiedByResult::wrap_bys(verify_what, items))
            }
        }
        StmtResult::StmtUnknown(_) => None,
    }
}
