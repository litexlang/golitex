//! Failed case evidence retains its actual local context and checked prefix.
use litex::knowledge_base::JsonValue;
use litex::launch_command::{LaunchCommand, OutputLanguage};
use litex::reading::{build_reading, ReadingInput};
use litex::runtime::Runtime;

trait TestJsonField {
    fn field(&self, key: &str) -> &JsonValue;
}
impl TestJsonField for JsonValue {
    fn field(&self, key: &str) -> &JsonValue {
        self.as_object()
            .ok()
            .and_then(|object| object.get(key))
            .unwrap_or(&JsonValue::Null)
    }
}

fn document(source: &str) -> JsonValue {
    let result = build_reading(
        &ReadingInput::Source(source.into()),
        true,
        OutputLanguage::English,
    );
    assert!(!result.success);
    result.document
}
fn resolve<'a>(data: &'a JsonValue, mut value: &'a JsonValue) -> &'a JsonValue {
    while value.field("kind").as_str().ok() == Some("evidence_reference") {
        let id = value.field("evidence_id");
        value = data
            .field("evidence_nodes")
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row.field("id") == id)
            .unwrap()
            .field("node");
    }
    value
}
fn node<'a>(data: &'a JsonValue, name: &str) -> &'a JsonValue {
    data.field("evidence_nodes")
        .as_array()
        .unwrap()
        .iter()
        .map(|row| row.field("node"))
        .find(|node| node.field("type").as_str().ok() == Some(name))
        .unwrap()
}
fn line(data: &JsonValue, number: u64) -> &JsonValue {
    data.field("statements")
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row.field("line").as_u64().unwrap() == number)
        .unwrap()
}
fn check_span(source: &str, span: &JsonValue) {
    let start = span.field("start_byte").as_u64().unwrap() as usize;
    let end = span.field("end_byte").as_u64().unwrap() as usize;
    assert_eq!(
        source.get(start..end),
        span.field("source_text").as_str().ok()
    );
    assert_eq!(
        source[..start]
            .bytes()
            .filter(|byte| *byte == b'\n')
            .count()
            + 1,
        span.field("line").as_u64().unwrap() as usize
    );
}

#[test]
fn original_case_headers_keep_complete_utf8_conditions_and_ordered_body_spans() {
    let source = "# 范围与分支\nby cases: # 原始位置\n    ? 0 = 0\n    case (0) = 0: # 当前条件\n        3 = 3\n        2 = 3\n    case 0 != 0:\n        0 = 0\n";
    let data = document(source);
    let statement = line(&data, 2);
    let cases = statement.field("case_contexts").as_array().unwrap();
    assert_eq!(cases.len(), 2);
    for (index, context) in cases.iter().enumerate() {
        assert_eq!(context.field("index").as_u64().unwrap() as usize, index);
        assert_eq!(
            context.field("condition").field("type").as_str().unwrap(),
            "AndChainAtomicFact"
        );
        check_span(source, context.field("header"));
        for step in context.field("proof_steps").as_array().unwrap() {
            check_span(source, step);
        }
        assert!(
            context.as_object().unwrap().get("scope_id").is_none(),
            "source syntax is not a scope certificate"
        );
    }
    assert_eq!(cases[0].field("condition_text").as_str().unwrap(), "0 = 0");
    assert!(cases[0]
        .field("header")
        .field("source_text")
        .as_str()
        .unwrap()
        .contains("(0)"));
    assert_eq!(cases[0].field("proof_steps").as_array().unwrap().len(), 2);
}

#[test]
fn actual_failed_case_scope_contains_the_assumption_and_both_step_verdicts() {
    let data = document(include_str!(
        "../examples/test_statements/negative/by_cases_stmt/failed-body-context.lit"
    ));
    let case = data
        .field("statements")
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row.field("statement_kind").as_str().ok() == Some("By.ByCasesStmt"))
        .unwrap();
    let original = &case.field("case_contexts").as_array().unwrap()[0];
    let steps = original.field("proof_steps").as_array().unwrap();
    let accepted = line(&data, steps[0].field("line").as_u64().unwrap());
    let rejected = line(&data, steps[1].field("line").as_u64().unwrap());
    assert_eq!(accepted.field("status").as_str().unwrap(), "accepted");
    assert_eq!(rejected.field("status").as_str().unwrap(), "rejected");
    let context = node(&data, "ByCasesBranchFailure").field("fields");
    let scope = context.field("local_env").field("scope_id");
    assert_eq!(accepted.field("scope_id"), scope);
    assert_eq!(rejected.field("scope_id"), scope);
    assert!(case
        .field("produced_fact_ids")
        .as_array()
        .unwrap()
        .is_empty());
    let id = context.field("assumption_fact_id").field("fact_id");
    let assumption = data
        .field("facts")
        .as_array()
        .unwrap()
        .iter()
        .find(|fact| fact.field("id") == id)
        .unwrap();
    assert_eq!(assumption.field("scope_id"), scope);
    let failure = node(&data, "ProofBlockBodyFailed").field("fields");
    let prefix = failure.field("prior_steps").as_array().unwrap();
    assert_eq!(prefix.len(), 1);
    assert_eq!(prefix[0].field("statement_id"), accepted.field("id"));
    assert_eq!(
        failure.field("result").field("statement_id"),
        rejected.field("id")
    );
    assert_eq!(
        resolve(&data, accepted.field("evidence"))
            .field("type")
            .as_str()
            .unwrap(),
        "ExecStmtResult"
    );
}

#[test]
fn a_failed_claims_prefix_never_becomes_file_scope_data() {
    let data = document("claim:\n    ? 0 = 0\n    3 = 3\n    2 = 3\n    4 = 4\n");
    assert_eq!(line(&data, 3).field("status").as_str().unwrap(), "accepted");
    assert_eq!(line(&data, 4).field("status").as_str().unwrap(), "rejected");
    assert_eq!(
        line(&data, 5).field("status").as_str().unwrap(),
        "not_exported"
    );
    let scope = line(&data, 3).field("scope_id");
    assert_eq!(scope, line(&data, 4).field("scope_id"));
    let frame = data
        .field("scopes")
        .as_array()
        .unwrap()
        .iter()
        .find(|frame| frame.field("id") == scope)
        .unwrap();
    assert_eq!(frame.field("statement_id"), line(&data, 1).field("id"));
    assert_eq!(
        node(&data, "ExecClaimLocalFailure")
            .field("fields")
            .field("local_env")
            .field("scope_id"),
        scope
    );
    assert!(line(&data, 1)
        .field("produced_fact_ids")
        .as_array()
        .unwrap()
        .is_empty());
}

#[test]
fn retaining_failure_evidence_does_not_commit_case_assumptions_or_break_recovery() {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: true,
        strict: true,
        language: OutputLanguage::English,
    });
    assert!(
        runtime
            .run_litex_code("have case_context_value R")
            .unwrap()
            .success
    );
    let count = runtime.top_exec_env().facts.facts_by_id.len();
    assert!(!runtime.run_litex_code("by cases:\n    ? case_context_value = case_context_value\n    case case_context_value = 0:\n        3 = 3\n        2 = 3\n    case case_context_value != 0:\n        case_context_value = case_context_value").unwrap().success);
    assert_eq!(runtime.top_exec_env().facts.facts_by_id.len(), count);
    assert!(
        !runtime
            .run_litex_code("case_context_value = 0")
            .unwrap()
            .success
    );
    assert!(
        runtime
            .run_litex_code("case_context_value $in R")
            .unwrap()
            .success
    );
}

#[test]
fn later_case_failure_retains_coverage_and_completed_branch_proofs() {
    let data = document(include_str!(
        "../examples/test_statements/negative/by_cases_stmt/completed-branch-before-failure.lit"
    ));
    let fields = node(&data, "ExecByCasesStmtFailed").field("fields");
    let branches = fields.field("branches").as_array().unwrap();
    assert_eq!(branches.len(), 1);
    assert!(!fields.field("coverage").eq(&JsonValue::Null));
    assert_eq!(fields.field("then_facts_wd").as_array().unwrap().len(), 1);
    let branch = resolve(&data, &branches[0]).field("fields");
    let steps = branch.field("proof_steps").as_array().unwrap();
    assert_eq!(steps.len(), 1);
    let id = steps[0].field("statement_id");
    let step = data
        .field("statements")
        .as_array()
        .unwrap()
        .iter()
        .find(|statement| statement.field("id") == id)
        .unwrap();
    assert_eq!(step.field("status").as_str().unwrap(), "accepted");
    assert_eq!(
        step.field("scope_id"),
        branch.field("local_env").field("scope_id")
    );
    let owner = step.field("parent_statement_id");
    let parent = data
        .field("statements")
        .as_array()
        .unwrap()
        .iter()
        .find(|statement| statement.field("id") == owner)
        .unwrap();
    assert_eq!(parent.field("status").as_str().unwrap(), "rejected");
    assert!(parent
        .field("produced_fact_ids")
        .as_array()
        .unwrap()
        .is_empty());
    let suffix = data
        .field("statements")
        .as_array()
        .unwrap()
        .iter()
        .find(|statement| statement.field("source_text").as_str().ok() == Some("4 = 4"))
        .unwrap();
    assert_eq!(suffix.field("status").as_str().unwrap(), "not_exported");
}

#[test]
fn a_failed_later_closing_goal_retains_earlier_local_goal_proofs() {
    let data = document("by cases:\n    ? 0 = 0\n    ? 2 = 3\n    case 2 = 3:\n        0 = 0\n    case 2 != 3:\n        0 = 0\n");
    let stage = data
        .field("evidence_nodes")
        .as_array()
        .unwrap()
        .iter()
        .map(|row| row.field("node"))
        .find(|node| {
            node.field("type").as_str().ok() == Some("ByCasesEnteredBranchFailed")
                && node.field("variant").as_str().ok() == Some("ClosingThen")
        })
        .unwrap();
    assert_eq!(
        stage
            .field("fields")
            .field("proved_then_facts")
            .as_array()
            .unwrap()
            .len(),
        1
    );
    assert_eq!(
        stage
            .field("fields")
            .field("proof_steps")
            .as_array()
            .unwrap()
            .len(),
        1
    );
    let branches = node(&data, "ExecByCasesStmtFailed")
        .field("fields")
        .field("branches")
        .as_array()
        .unwrap();
    let closing = resolve(
        &data,
        resolve(&data, &branches[0])
            .field("fields")
            .field("closing"),
    );
    assert_eq!(
        closing
            .field("fields")
            .field("proved_then_facts")
            .as_array()
            .unwrap()
            .len(),
        2
    );
}

#[test]
fn a_completed_sibling_cannot_publish_its_predicate_or_inferred_inequality() {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: true,
        strict: true,
        language: OutputLanguage::English,
    });
    assert!(
        runtime
            .run_litex_code("prop case_prefix_nonnegative(x R):\n    x >= 0")
            .unwrap()
            .success
    );
    assert!(
        runtime
            .run_litex_code("have case_prefix_value R")
            .unwrap()
            .success
    );
    let before = runtime.top_exec_env().facts.facts_by_id.len();
    assert!(!runtime.run_litex_code("by cases:\n    ? $case_prefix_nonnegative(case_prefix_value)\n    case case_prefix_value = 0:\n        by def $case_prefix_nonnegative(case_prefix_value)\n    case case_prefix_value != 0:\n        $case_prefix_nonnegative(case_prefix_value)").unwrap().success);
    assert_eq!(runtime.top_exec_env().facts.facts_by_id.len(), before);
    assert!(
        !runtime
            .run_litex_code("$case_prefix_nonnegative(case_prefix_value)")
            .unwrap()
            .success
    );
    assert!(
        !runtime
            .run_litex_code("case_prefix_value >= 0")
            .unwrap()
            .success
    );
    assert!(
        runtime
            .run_litex_code("case_prefix_value $in R")
            .unwrap()
            .success
    );
}

#[test]
fn common_publication_is_outer_and_case_assumptions_remain_local_after_success() {
    let source = "have case_owner_value R\nby cases:\n    ? case_owner_value = case_owner_value\n    case case_owner_value = 0:\n        3 = 3\n    case case_owner_value != 0:\n        4 = 4\n";
    let result = build_reading(
        &ReadingInput::Source(source.into()),
        true,
        OutputLanguage::English,
    );
    assert!(result.success);
    let data = &result.document;
    let statement = line(data, 2);
    let published = statement.field("produced_fact_ids").as_array().unwrap();
    assert!(!published.is_empty());
    for id in published {
        let fact = data
            .field("facts")
            .as_array()
            .unwrap()
            .iter()
            .find(|fact| fact.field("id") == id)
            .unwrap();
        assert_eq!(fact.field("scope_id"), statement.field("scope_id"));
    }
    for branch in node(data, "ExecByCasesStmtSuccess")
        .field("fields")
        .field("branches")
        .as_array()
        .unwrap()
    {
        let fields = resolve(data, branch).field("fields");
        let id = fields.field("assumption_fact_id").field("fact_id");
        assert!(!published.contains(id));
        let fact = data
            .field("facts")
            .as_array()
            .unwrap()
            .iter()
            .find(|fact| fact.field("id") == id)
            .unwrap();
        assert_eq!(
            fact.field("scope_id"),
            fields.field("local_env").field("scope_id")
        );
    }
}
