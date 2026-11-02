//! Real exported/imported chapter evaluation, without fabricated runtime state.
use litex::knowledge_base::JsonValue;
use litex::launch_command::OutputLanguage;
use litex::reading::{build_reading, ReadingInput};
use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

const SOURCE: &str = include_str!("../examples/stmt_nodes/command/eval_qualified_algorithms.lit");

fn temporary_project(tag: &str) -> PathBuf {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let path = std::env::temp_dir().join(format!(
        "litex-qualified-eval-{}-{tag}-{nonce}",
        std::process::id()
    ));
    fs::create_dir_all(&path).unwrap();
    path
}

fn evidence_count(document: &JsonValue, kind: &str) -> usize {
    document
        .as_object()
        .unwrap()
        .get("evidence_nodes")
        .unwrap()
        .as_array()
        .unwrap()
        .iter()
        .filter(|row| {
            row.as_object()
                .unwrap()
                .get("node")
                .unwrap()
                .as_object()
                .unwrap()
                .get("type")
                .and_then(|v| v.as_str().ok())
                == Some(kind)
        })
        .count()
}

fn field<'a>(value: &'a JsonValue, key: &str) -> &'a JsonValue {
    value.as_object().unwrap().get(key).unwrap()
}

fn resolve<'a>(mut value: &'a JsonValue, nodes: &BTreeMap<String, &'a JsonValue>) -> &'a JsonValue {
    while value
        .as_object()
        .unwrap()
        .get("kind")
        .and_then(|v| v.as_str().ok())
        == Some("evidence_reference")
    {
        value = nodes
            .get(field(value, "evidence_id").as_str().unwrap())
            .copied()
            .unwrap();
    }
    value
}

fn entry_eval_values(document: &JsonValue) -> Vec<String> {
    let nodes = field(document, "evidence_nodes")
        .as_array()
        .unwrap()
        .iter()
        .map(|row| {
            (
                field(row, "id").as_str().unwrap().to_owned(),
                field(row, "node"),
            )
        })
        .collect::<BTreeMap<_, _>>();
    field(document, "statements")
        .as_array()
        .unwrap()
        .iter()
        .filter(|statement| {
            field(statement, "source_id") == field(document, "entry_source_id")
                && field(statement, "statement_kind")
                    .as_str()
                    .unwrap()
                    .ends_with("EvalStmt")
        })
        .map(|statement| {
            let mut result = resolve(field(statement, "evidence"), &nodes);
            while let Some(next) = field(result, "fields").as_object().unwrap().get("0") {
                result = resolve(next, &nodes);
            }
            assert_eq!(
                field(result, "type").as_str().unwrap(),
                "ExecEvalStmtSuccess"
            );
            field(
                resolve(field(field(result, "fields"), "evaluated_object"), &nodes),
                "text",
            )
            .as_str()
            .unwrap()
            .to_owned()
        })
        .collect()
}

#[test]
fn exported_algorithm_chapters_keep_current_file_identity() {
    let project = temporary_project("exports");
    fs::write(
        project.join("litex.config"),
        "[export]\nfirst=\"./first.lit\"\nsecond=\"./second.lit\"\n",
    )
    .unwrap();
    fs::write(project.join("first.lit"), SOURCE).unwrap();
    fs::write(project.join("second.lit"), SOURCE).unwrap();
    let result = build_reading(
        &ReadingInput::Project(project.clone()),
        true,
        OutputLanguage::English,
    );
    assert!(
        result.success,
        "every exact eval in both chapters must succeed: {:?}",
        result.document
    );
    let expected = SOURCE
        .lines()
        .filter(|line| line.trim_start().starts_with("eval "))
        .count()
        * 2;
    assert_eq!(
        evidence_count(&result.document, "ExecEvalStmtSuccess"),
        expected
    );
    fs::remove_dir_all(project).unwrap();
}

#[test]
fn imported_algorithm_chapter_keeps_module_and_export_identity() {
    let project = temporary_project("import");
    fs::create_dir(project.join("library")).unwrap();
    fs::write(
        project.join("library/litex.config"),
        "[export]\nchapter=\"./chapter.lit\"\n",
    )
    .unwrap();
    fs::write(project.join("library/chapter.lit"), SOURCE).unwrap();
    fs::write(
        project.join("litex.config"),
        "[import]\nLibrary=\"./library\"\n[export]\nmain=\"./main.lit\"\n",
    )
    .unwrap();
    // These exact calls and the required release interfaces were accepted in
    // one persistent Session, including a domain rejection before the last call.
    fs::write(
        project.join("main.lit"),
        "release obj def Library::chapter::eval_flag\n\
         eval Library::chapter::eval_flag(0)\n\
         eval Library::chapter::eval_flag(2) + 1\n\
         release obj def Library::chapter::recursive_eval\n\
         eval Library::chapter::recursive_eval(2)\n\
         release obj def Library::chapter::eval_identity\n\
         eval Library::chapter::eval_identity(2) + 1\n",
    )
    .unwrap();
    let result = build_reading(
        &ReadingInput::Project(project.clone()),
        true,
        OutputLanguage::English,
    );
    assert!(
        result.success,
        "loading an imported chapter must execute its qualified algorithms: {:?}",
        result.document
    );
    assert_eq!(entry_eval_values(&result.document), ["0", "2", "0", "3"]);
    fs::remove_dir_all(project).unwrap();
}

#[test]
fn exported_algorithm_call_outside_domain_still_has_no_result_equality() {
    let project = temporary_project("wd-negative");
    fs::write(
        project.join("litex.config"),
        "[export]\nmain=\"./main.lit\"\n",
    )
    .unwrap();
    fs::write(
        project.join("main.lit"),
        include_str!("../examples/test_statements/negative/eval_stmt/outside-algo-domain.lit"),
    )
    .unwrap();
    let result = build_reading(
        &ReadingInput::Project(project.clone()),
        true,
        OutputLanguage::English,
    );
    assert!(
        !result.success,
        "qualification must not bypass the source domain"
    );
    assert_eq!(evidence_count(&result.document, "ExecEvalStmtSuccess"), 0);
    fs::remove_dir_all(project).unwrap();
}
