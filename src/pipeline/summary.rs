use crate::common::json_value::{line_file_line_json_value, render_json_value, JsonValue};
use crate::prelude::*;
use std::collections::BTreeMap;

#[derive(Clone, Debug, Default)]
pub struct RunSummary {
    pub statements: usize,
    pub top_level_statements: usize,
    pub verified_statements: usize,
    pub fact_statements: usize,
    pub prop_definitions: usize,
    pub abstract_prop_definitions: usize,
    pub theorem_statements: usize,
    pub theorem_names: usize,
    pub by_statements: usize,
    pub proof_blocks: usize,
    pub object_definitions: usize,
    pub function_definitions: usize,
    pub alias_statements: usize,
    pub import_statements: usize,
    pub direct_proof_debt: usize,
    pub indirect_proof_debt: usize,
    pub axioms: usize,
    pub supposes: usize,
    pub abstract_interfaces: usize,
    pub stack_runner_warnings: usize,
    indirect_proof_debt_reasons: Vec<String>,
    statement_items: Vec<StatementSummaryItem>,
    statement_type_counts: BTreeMap<String, usize>,
    output_type_counts: BTreeMap<String, usize>,
}

#[derive(Clone, Debug)]
struct StatementSummaryItem {
    index: usize,
    line_file: LineFile,
    statement_type: String,
    output_type: String,
    statement: String,
}

impl RunSummary {
    pub fn from_run(
        stmt_results: &[StmtResult],
        runtime_error: &Option<RuntimeError>,
    ) -> RunSummary {
        let mut summary = RunSummary::default();
        summary.top_level_statements = stmt_results.len();
        for result in stmt_results {
            summary.visit_result(result);
        }
        if let Some(error) = runtime_error {
            summary.visit_runtime_error(error);
        }
        summary.indirect_proof_debt = summary.indirect_proof_debt_reasons.len();
        summary
    }

    fn visit_result(&mut self, result: &StmtResult) {
        if result.is_true() {
            self.verified_statements += 1;
        }
        if let Some(success) = result.factual_success() {
            self.visit_fact_stmt(&success.stmt);
            self.visit_infer_result(&success.infers);
            self.visit_verified_by(&success.verified_by);
        }
        if let Some(success) = result.non_factual_success() {
            self.visit_stmt(&success.stmt);
            self.visit_infer_result(&success.infers);
            for inside_result in success.inside_results.iter() {
                self.visit_result(inside_result);
            }
        }
    }

    fn visit_stmt(&mut self, stmt: &Stmt) {
        self.record_stmt(stmt);
        match stmt {
            Stmt::Fact(_) => {
                self.fact_statements += 1;
            }
            Stmt::UnsafeStmt(UnsafeStmt::ProofDebtStmt(_)) => {
                self.direct_proof_debt += 1;
            }
            Stmt::UnsafeStmt(UnsafeStmt::DefLetStmt(_)) => {
                self.supposes += 1;
            }
            Stmt::DefObjStmt(def_obj) => {
                self.object_definitions += 1;
                if is_function_definition(def_obj) {
                    self.function_definitions += 1;
                }
            }
            Stmt::DefPredicateStmt(DefPredicateStmt::DefPropStmt(_)) => {
                self.prop_definitions += 1;
            }
            Stmt::DefPredicateStmt(DefPredicateStmt::DefAbstractPropStmt(_)) => {
                self.abstract_prop_definitions += 1;
                self.abstract_interfaces += 1;
            }
            Stmt::DefAliasStmt(_) => {
                self.alias_statements += 1;
            }
            Stmt::DefInterfaceStmt(_) => {
                self.abstract_interfaces += 1;
            }
            Stmt::DefThmStmt(def_thm) => {
                if def_thm.is_axiom() {
                    self.axioms += 1;
                } else {
                    self.theorem_statements += 1;
                    self.theorem_names += def_thm.names.len();
                }
            }
            Stmt::By(_) => {
                self.by_statements += 1;
            }
            Stmt::ProofBlock(_) => {
                self.proof_blocks += 1;
            }
            Stmt::Command(CommandStmt::ImportStmt(_)) => {
                self.import_statements += 1;
            }
            _ => {}
        }
    }

    fn visit_fact_stmt(&mut self, fact: &Fact) {
        self.record_fact(fact);
        self.fact_statements += 1;
    }

    fn record_stmt(&mut self, stmt: &Stmt) {
        self.statements += 1;
        let statement_type = stmt.stmt_type_name();
        let output_type = stmt.output_type_string();
        self.bump_statement_type(statement_type.as_str());
        self.bump_output_type(output_type.as_str());
        self.statement_items.push(StatementSummaryItem::new(
            self.statements,
            stmt.line_file(),
            statement_type,
            output_type,
            stmt.to_string(),
        ));
    }

    fn record_fact(&mut self, fact: &Fact) {
        self.statements += 1;
        let statement_type = fact.fact_type_string();
        let output_type = fact.output_type_string();
        self.bump_statement_type(statement_type.as_str());
        self.bump_output_type(output_type.as_str());
        self.statement_items.push(StatementSummaryItem::new(
            self.statements,
            fact.line_file(),
            statement_type,
            output_type,
            fact.to_string(),
        ));
    }

    fn bump_statement_type(&mut self, statement_type: &str) {
        *self
            .statement_type_counts
            .entry(statement_type.to_string())
            .or_insert(0) += 1;
    }

    fn bump_output_type(&mut self, output_type: &str) {
        *self
            .output_type_counts
            .entry(output_type.to_string())
            .or_insert(0) += 1;
    }

    fn visit_infer_result(&mut self, infer_result: &InferResult) {
        for output in infer_result.store_fact_outputs() {
            let reason = &output.itself_and_why_itself_is_stored.1;
            if reason.contains("depends_on_unproved_assumptions")
                && reason.contains("proof_debt")
                && !self
                    .indirect_proof_debt_reasons
                    .iter()
                    .any(|existing| existing == reason)
            {
                self.indirect_proof_debt_reasons.push(reason.clone());
            }
        }
    }

    fn visit_verified_by(&mut self, verified_by: &VerifiedByResult) {
        match verified_by {
            VerifiedByResult::BuiltinRule(result) => {
                for subgoal in result.subgoals.iter() {
                    self.visit_result(subgoal);
                }
            }
            VerifiedByResult::KnownForallInstantiation(result) => {
                self.visit_known_forall_instantiation(result);
            }
            VerifiedByResult::VerifiedBys(result) => {
                for item in result.cite_what.iter() {
                    self.visit_verified_by_item(item);
                }
            }
            VerifiedByResult::ForallProof(result) => {
                for proved in result.proves.iter() {
                    self.visit_result(&proved.result);
                }
            }
            VerifiedByResult::Fact(_) => {}
        }
    }

    fn visit_verified_by_item(&mut self, item: &VerifiedBysEnum) {
        match item {
            VerifiedBysEnum::ByBuiltinRule(result) => {
                for subgoal in result.subgoals.iter() {
                    self.visit_result(subgoal);
                }
            }
            VerifiedBysEnum::ByKnownForall(result) => {
                self.visit_known_forall_instantiation(&result.result);
            }
            VerifiedBysEnum::ByFact(_) => {}
        }
    }

    fn visit_known_forall_instantiation(&mut self, result: &KnownForallInstantiationResult) {
        for requirement in result.requirements.iter() {
            self.visit_result(&requirement.result);
        }
    }

    fn visit_runtime_error(&mut self, error: &RuntimeError) {
        let text = error.to_string().to_ascii_lowercase();
        if text.contains("stack") || text.contains("runner warning") {
            self.stack_runner_warnings += 1;
        }
    }

    fn to_json_value(&self, ok: bool) -> JsonValue {
        let result_label = if ok { "success" } else { "error" };
        JsonValue::Object(vec![
            (
                "result".to_string(),
                JsonValue::JsonString(result_label.to_string()),
            ),
            (
                "output_type".to_string(),
                JsonValue::JsonString("run summary".to_string()),
            ),
            (
                "summary".to_string(),
                JsonValue::Object(vec![
                    ("statements".to_string(), JsonValue::Number(self.statements)),
                    (
                        "top_level_statements".to_string(),
                        JsonValue::Number(self.top_level_statements),
                    ),
                    (
                        "verified_statements".to_string(),
                        JsonValue::Number(self.verified_statements),
                    ),
                    (
                        "fact_statements".to_string(),
                        JsonValue::Number(self.fact_statements),
                    ),
                    (
                        "prop_definitions".to_string(),
                        JsonValue::Number(self.prop_definitions),
                    ),
                    (
                        "abstract_prop_definitions".to_string(),
                        JsonValue::Number(self.abstract_prop_definitions),
                    ),
                    (
                        "theorem_statements".to_string(),
                        JsonValue::Number(self.theorem_statements),
                    ),
                    (
                        "theorem_names".to_string(),
                        JsonValue::Number(self.theorem_names),
                    ),
                    (
                        "by_statements".to_string(),
                        JsonValue::Number(self.by_statements),
                    ),
                    (
                        "proof_blocks".to_string(),
                        JsonValue::Number(self.proof_blocks),
                    ),
                    (
                        "object_definitions".to_string(),
                        JsonValue::Number(self.object_definitions),
                    ),
                    (
                        "function_definitions".to_string(),
                        JsonValue::Number(self.function_definitions),
                    ),
                    (
                        "alias_statements".to_string(),
                        JsonValue::Number(self.alias_statements),
                    ),
                    (
                        "import_statements".to_string(),
                        JsonValue::Number(self.import_statements),
                    ),
                    (
                        "direct_proof_debt".to_string(),
                        JsonValue::Number(self.direct_proof_debt),
                    ),
                    (
                        "indirect_proof_debt".to_string(),
                        JsonValue::Number(self.indirect_proof_debt),
                    ),
                    ("axioms".to_string(), JsonValue::Number(self.axioms)),
                    ("supposes".to_string(), JsonValue::Number(self.supposes)),
                    (
                        "abstract_interfaces".to_string(),
                        JsonValue::Number(self.abstract_interfaces),
                    ),
                    (
                        "stack_runner_warnings".to_string(),
                        JsonValue::Number(self.stack_runner_warnings),
                    ),
                ]),
            ),
            (
                "statement_type_counts".to_string(),
                count_map_json_value(&self.statement_type_counts),
            ),
            (
                "output_type_counts".to_string(),
                count_map_json_value(&self.output_type_counts),
            ),
            (
                "statements".to_string(),
                JsonValue::Array(
                    self.statement_items
                        .iter()
                        .map(StatementSummaryItem::json_value)
                        .collect(),
                ),
            ),
            (
                "summary_text".to_string(),
                JsonValue::JsonString(self.summary_text()),
            ),
        ])
    }

    fn summary_text(&self) -> String {
        format!(
            "statements: {}; top-level statements: {}; verified statements: {}; facts: {}; props: {}; abstract props: {}; theorem statements: {}; theorem names: {}; by statements: {}; direct proof debt: {}; indirect proof debt: {}; axioms: {}; supposes: {}; abstract interfaces: {}; stack/runner warnings: {}",
            self.statements,
            self.top_level_statements,
            self.verified_statements,
            self.fact_statements,
            self.prop_definitions,
            self.abstract_prop_definitions,
            self.theorem_statements,
            self.theorem_names,
            self.by_statements,
            self.direct_proof_debt,
            self.indirect_proof_debt,
            self.axioms,
            self.supposes,
            self.abstract_interfaces,
            self.stack_runner_warnings
        )
    }
}

impl StatementSummaryItem {
    fn new(
        index: usize,
        line_file: LineFile,
        statement_type: String,
        output_type: String,
        statement: String,
    ) -> Self {
        Self {
            index,
            line_file,
            statement_type,
            output_type,
            statement,
        }
    }

    fn json_value(&self) -> JsonValue {
        JsonValue::Object(vec![
            ("index".to_string(), JsonValue::Number(self.index)),
            (
                "line".to_string(),
                line_file_line_json_value(&self.line_file),
            ),
            (
                "statement_type".to_string(),
                JsonValue::JsonString(self.statement_type.clone()),
            ),
            (
                "output_type".to_string(),
                JsonValue::JsonString(self.output_type.clone()),
            ),
            (
                "statement".to_string(),
                JsonValue::JsonString(strip_free_param_numeric_tags_in_display(&self.statement)),
            ),
        ])
    }
}

pub fn display_run_summary_json(
    stmt_results: &[StmtResult],
    runtime_error: &Option<RuntimeError>,
) -> String {
    let summary = RunSummary::from_run(stmt_results, runtime_error);
    render_json_value(&summary.to_json_value(runtime_error.is_none()), 0)
}

fn count_map_json_value(counts: &BTreeMap<String, usize>) -> JsonValue {
    JsonValue::Object(
        counts
            .iter()
            .map(|(name, count)| (name.clone(), JsonValue::Number(*count)))
            .collect(),
    )
}

fn is_function_definition(stmt: &DefObjStmt) -> bool {
    match stmt {
        DefObjStmt::HaveFnEqualStmt(_)
        | DefObjStmt::HaveFnEqualCaseByCaseStmt(_)
        | DefObjStmt::HaveFnByInducStmt(_)
        | DefObjStmt::HaveFnByForallExistUniqueStmt(_) => true,
        _ => false,
    }
}
