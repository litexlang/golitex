use crate::prelude::*;

#[derive(Debug)]
pub struct NonFactualStmtSuccess {
    pub stmt: Stmt,
    pub infers: InferResult,
    pub inside_results: Vec<StmtResult>,
}

#[derive(Debug)]
pub struct FactualStmtSuccess {
    pub stmt: Fact,
    pub infers: InferResult,
    pub msg: String,
    pub verified_by_fact: Option<Fact>,
    pub verified_by_fact_known_line_file: Option<LineFile>,
    pub inside_results: Vec<StmtResult>,
}

impl FactualStmtSuccess {
    pub fn new_with_verified_by_builtin_rules(
        stmt: Fact,
        infers: InferResult,
        builtin_rule_label: String,
        inside_results: Vec<StmtResult>,
    ) -> Self {
        FactualStmtSuccess {
            stmt,
            infers,
            msg: builtin_rule_label,
            verified_by_fact: None,
            verified_by_fact_known_line_file: None,
            inside_results,
        }
    }

    /// 与 [`Self::new_with_verified_by_builtin_rules`] 相同，且 `infers` 为 [`InferResult::from_fact`]`(&stmt)`（空 `inside_results` 时常用）。
    pub fn new_with_verified_by_builtin_rules_recording_stmt(
        stmt: Fact,
        builtin_rule_label: String,
        inside_results: Vec<StmtResult>,
    ) -> Self {
        let infers = InferResult::from_fact(&stmt);
        Self::new_with_verified_by_builtin_rules(stmt, infers, builtin_rule_label, inside_results)
    }

    pub fn new_with_verified_by_known_fact_source(
        stmt: Fact,
        infers: InferResult,
        msg: String,
        verified_by_fact: Option<Fact>,
        verified_by_fact_known_line_file: Option<LineFile>,
        inside_results: Vec<StmtResult>,
    ) -> Self {
        FactualStmtSuccess {
            stmt,
            infers,
            msg,
            verified_by_fact,
            verified_by_fact_known_line_file,
            inside_results,
        }
    }

    pub fn new_with_verified_by_known_fact_source_recording_facts(
        stmt: Fact,
        msg: String,
        verified_by_fact: Option<Fact>,
        verified_by_fact_known_line_file: Option<LineFile>,
        inside_results: Vec<StmtResult>,
    ) -> Self {
        Self::new_with_verified_by_known_fact_source(
            stmt,
            InferResult::new(),
            msg,
            verified_by_fact,
            verified_by_fact_known_line_file,
            inside_results,
        )
    }

    pub fn line_file_for_verified_by_known_fact_in_json(&self) -> LineFile {
        if let Some(ref line_file) = self.verified_by_fact_known_line_file {
            return line_file.clone();
        }
        if let Some(cited_fact) = &self.verified_by_fact {
            return cited_fact.line_file();
        }
        default_line_file()
    }

    pub fn is_verified_by_builtin_rules_only(&self) -> bool {
        self.verified_by_fact.is_none() && self.verified_by_fact_known_line_file.is_none()
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
}
