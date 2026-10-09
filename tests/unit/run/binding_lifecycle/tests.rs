use crate::ast::obj::IdentifierObj;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::run::{RunLitexCodeResult, RunSessionError};
use crate::runtime::{CodeSource, Runtime, RuntimeError};
use crate::tokenize::Tokenizer;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

fn success(rt: &mut Runtime, code: &str) {
    let result = rt.run_litex_code(code).unwrap();
    assert!(
        result.success,
        "{code}\n{}",
        crate::json_output::emit_run_normal(&result, rt, "eval", None)
    );
}

fn parse_error(result: &RunLitexCodeResult) {
    assert!(!result.success);
    assert!(matches!(
        result.session_error,
        Some(RunSessionError::Runtime(RuntimeError::ParseError(_)))
    ));
}

#[test]
fn failed_have_can_be_corrected_in_the_same_runtime() {
    let mut rt = runtime();
    assert!(!rt.run_litex_code("have k N = -1").unwrap().success);
    assert!(rt.resolve_plain_atom("k").is_err());
    assert!(!rt.top_exec_env().definitions.identifiers.contains_key("k"));
    success(
        &mut rt,
        include_str!("../../../../examples/stmt_nodes/definition/parse_scope_transaction.lit"),
    );
}

#[test]
fn next_block_is_parsed_after_failed_binding_is_discarded() {
    let mut rt = runtime();
    let result = rt
        .run_litex_code("have k N = -1\nhave k N = 1\nk = 1")
        .unwrap();
    assert!(!result.success);
    assert!(result.session_error.is_none());
    assert_eq!(result.failed_statement_results, Some(vec![0]));
    assert_eq!(result.statement_results.len(), 3);
    success(&mut rt, "k = 1");
}

#[test]
fn failed_obtain_can_be_retried_with_same_named_exist_binder() {
    let mut rt = runtime();
    let result = rt
        .run_litex_code("obtain k from exist t Z st {t = 0, t = 1}")
        .unwrap();
    assert!(!result.success);
    assert!(result.session_error.is_none());
    assert!(rt.resolve_plain_atom("k").is_err());
    success(
        &mut rt,
        "witness exist k Z st {k = 0} from 0\nobtain k from exist k Z st {k = 0}\nk = 0",
    );
    assert!(!rt.run_litex_code("0 = 1").unwrap().success);
}

#[test]
fn standalone_parse_error_restores_all_scopes_and_existing_names() {
    let mut rt = runtime();
    success(&mut rt, "let saved = 7");
    let saved_id = rt.resolve_plain_atom("saved").unwrap();
    rt.push_parse_scope();
    let local = rt.define_plain_atom("local".into()).unwrap();
    let scopes_before: Vec<_> = rt
        .parse_scope_stack
        .iter()
        .map(|scope| scope.plain.clone())
        .collect();
    let tokens = Tokenizer::new()
        .tokenize(
            "let provisional = 3\nsketch:\n    let temporary = 3\n    let broken =\n",
            rt.current_file.clone(),
        )
        .unwrap();
    assert!(rt.parse(&tokens).is_err());
    let scopes_after: Vec<_> = rt
        .parse_scope_stack
        .iter()
        .map(|scope| scope.plain.clone())
        .collect();
    assert_eq!(scopes_after, scopes_before);
    assert_eq!(rt.resolve_plain_atom("saved").unwrap(), saved_id);
    assert_eq!(rt.resolve_plain_atom("local").unwrap(), local.id);
    rt.pop_parse_scope();
    success(
        &mut rt,
        "let provisional = 1\nlet temporary = 2\nlet broken = 3\nsaved = 7",
    );
}

#[test]
fn later_parse_error_keeps_executed_prefix_and_discards_failed_names() {
    let mut rt = runtime();
    let result = rt
        .run_litex_code("let kept = 1\nlet broken =\nlet skipped = 2")
        .unwrap();
    parse_error(&result);
    assert_eq!(result.statement_results.len(), 1);
    assert!(!result.statement_results[0].is_failed());
    assert!(rt.resolve_plain_atom("broken").is_err());
    assert!(rt.resolve_plain_atom("skipped").is_err());
    assert!(rt
        .top_exec_env()
        .definitions
        .identifiers
        .contains_key("kept"));
    success(&mut rt, "let broken = 2\nlet skipped = 3\nkept = 1");
}

#[test]
fn reference_to_failed_declaration_is_rejected_by_next_block_parser() {
    let mut rt = runtime();
    let result = rt
        .run_litex_code("have bad N = -1\nlet copied = bad\nlet skipped = 2")
        .unwrap();
    parse_error(&result);
    assert_eq!(result.failed_statement_results, Some(vec![0]));
    assert_eq!(result.statement_results.len(), 1);
    for name in ["bad", "copied", "skipped"] {
        assert!(rt.resolve_plain_atom(name).is_err(), "leaked {name}");
        assert!(!rt.top_exec_env().definitions.identifiers.contains_key(name));
    }
    success(&mut rt, "have bad N = 1\nlet copied = bad\ncopied = 1");
}

#[test]
fn soft_failure_keeps_successful_prefix_and_later_declarations() {
    let mut rt = runtime();
    let result = rt
        .run_litex_code("let kept = 1\nhave bad N = -1\nlet good = 2")
        .unwrap();
    assert!(result.session_error.is_none());
    assert_eq!(result.failed_statement_results, Some(vec![1]));
    assert_eq!(result.statement_results.len(), 3);
    assert!(rt.resolve_plain_atom("bad").is_err());
    success(&mut rt, "have bad N = 1\nkept = 1\ngood = 2");
}

#[test]
fn hard_execution_error_precedes_later_parse_error() {
    let mut rt = runtime();
    let result = rt
        .run_litex_code("let kept = 1\ntrust have rejected N:\n    rejected = 0\nlet skipped =")
        .unwrap();
    assert!(matches!(
        result.session_error,
        Some(RunSessionError::Runtime(RuntimeError::InvalidArguments(_)))
    ));
    assert_eq!(result.statement_results.len(), 1);
    assert!(rt.resolve_plain_atom("rejected").is_err());
    assert!(rt.resolve_plain_atom("skipped").is_err());
    // Only kept and rejected were parsed; skipped has not consumed an ID.
    assert_eq!(rt.global_ids.to_u64s().3, 3);
    success(&mut rt, "have rejected N = 0\nlet skipped = 2\nkept = 1");
}

#[test]
fn nested_proof_is_one_atomic_block() {
    let mut rt = runtime();
    let result = rt
        .run_litex_code(
            "let kept = 1\nsketch:\n    let local = 2\n    let broken =\nlet skipped = 3",
        )
        .unwrap();
    parse_error(&result);
    assert_eq!(result.statement_results.len(), 1);
    assert_eq!(rt.execution_environments_stack.len(), 1);
    assert_eq!(rt.parse_scope_stack.len(), 1);
    for name in ["local", "broken", "skipped"] {
        assert!(rt.resolve_plain_atom(name).is_err());
        assert!(!rt.top_exec_env().definitions.identifiers.contains_key(name));
    }
    success(&mut rt, "let local = 2\nlet broken = 3\nkept = 1");
}

#[test]
fn rollback_preserves_old_bindings_and_never_reuses_identifier_ids() {
    let mut rt = runtime();
    success(&mut rt, "let original = 0");
    let original_id = rt.resolve_plain_atom("original").unwrap();
    parse_error(&rt.run_litex_code("let original = 1").unwrap());
    assert_eq!(rt.resolve_plain_atom("original").unwrap(), original_id);
    parse_error(&rt.run_litex_code("let k = 1 garbage").unwrap());
    let after_parse_failure = rt.global_ids.to_u64s().3;
    assert!(!rt.run_litex_code("have k N = -1").unwrap().success);
    let after_exec_failure = rt.global_ids.to_u64s().3;
    assert!(after_exec_failure > after_parse_failure);
    success(&mut rt, "let k = 2");
    assert!(rt.resolve_plain_atom("k").unwrap().value() >= after_exec_failure);
    assert!(rt.resolve_plain_atom("k").unwrap().value() > original_id.value());
    success(&mut rt, "original = 0\nk = 2");
    assert!(!rt.run_litex_code("0 = 1").unwrap().success);
}

#[test]
fn isolation_preserves_file_root_qualification_and_inner_bindings() {
    for source in [
        CodeSource::Real("test.lit".into()),
        CodeSource::RootExport {
            path: "test.lit".into(),
            export_file_id: 0,
        },
        CodeSource::ImportedExport {
            path: "test.lit".into(),
            global_mod_id: 0,
            export_file_id: 0,
        },
    ] {
        let mut rt = runtime();
        rt.current_file = source.clone();
        let result = rt
            .run_litex_code("have k N = -1\nhave k N = 1\nk = 1")
            .unwrap();
        assert!(result.session_error.is_none());
        assert_eq!(result.failed_statement_results, Some(vec![0]));
        assert_eq!(result.statement_results.len(), 3);
        assert_eq!(rt.parse_scope_stack.len(), 1);
        let root_ref = rt.identifier_obj_for_plain_free_ref("k".into()).unwrap();
        match source {
            CodeSource::Real(_) => assert!(matches!(root_ref, IdentifierObj::Plain { .. })),
            CodeSource::RootExport { .. } => {
                assert!(matches!(root_ref, IdentifierObj::WithExportFileId { .. }))
            }
            CodeSource::ImportedExport { .. } => {
                assert!(matches!(
                    root_ref,
                    IdentifierObj::WithModAndExportFileId { .. }
                ))
            }
            _ => unreachable!(),
        }
        rt.push_parse_scope();
        success(&mut rt, "let inner = 2\ninner = 2");
        assert_eq!(rt.parse_scope_stack.len(), 2);
        assert!(matches!(
            rt.identifier_obj_for_plain_free_ref("inner".into())
                .unwrap(),
            IdentifierObj::Plain { .. }
        ));
        assert!(!rt.parse_scope_stack[0].plain.contains_key("inner"));
        rt.pop_parse_scope();
    }
}

#[test]
fn repeated_names_never_replace_an_existing_object_or_function() {
    for (prefix, duplicate, old_fact, wrong_fact) in [
        ("let item = 1", "let item = 2", "item = 1", "item = 2"),
        ("let item = 1", "have item R = 2", "item = 1", "item = 2"),
        (
            "let item = 1",
            "have fn item(t R) R = 2",
            "item = 1",
            "item = 2",
        ),
        ("have item R = 1", "let item = 2", "item = 1", "item = 2"),
        (
            "have fn item(t R) R = 1",
            "have fn item(u R) R = 2",
            "item(0) = 1",
            "item(0) = 2",
        ),
        (
            "have fn item(t R) R = 1",
            "let item = 2",
            "item(0) = 1",
            "item(0) = 2",
        ),
    ] {
        let mut rt = runtime();
        success(&mut rt, prefix);
        let original_id = rt.resolve_plain_atom("item").unwrap();
        let facts_before = rt.top_exec_env().facts.facts_by_id.len();
        let result = rt.run_litex_code(duplicate).unwrap();
        parse_error(&result);
        assert!(result.statement_results.is_empty());
        assert!(result
            .session_error
            .unwrap()
            .to_string()
            .contains("already bound"));
        assert_eq!(rt.resolve_plain_atom("item").unwrap(), original_id);
        assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), facts_before);
        assert_eq!(rt.execution_environments_stack.len(), 1);
        assert_eq!(rt.parse_scope_stack.len(), 1);
        // Inspect the retained Runtime through its API; CLI parse errors end
        // the interactive process and are not promised to be recoverable there.
        success(&mut rt, old_fact);
        assert!(!rt.run_litex_code(wrong_fact).unwrap().success);
        assert!(!rt.run_litex_code("0 = 1").unwrap().success);
    }
}

#[test]
fn repeated_names_keep_predicate_theorem_and_struct_definitions() {
    for (prefix, duplicate, old_fact, wrong_fact) in [
        (
            "prop item(t R):\n    t = 0",
            "prop item(t R):\n    t = 1",
            "by def $item(0)",
            "by def $item(1)",
        ),
        (
            "prop item(t R):\n    t = 0",
            "let item = 1",
            "by def $item(0)",
            "by def $item(1)",
        ),
        (
            "thm item:\n    ? forall t N:\n        t >= 0",
            "thm item:\n    ? 0 = 1",
            "release thm item(0)",
            "release thm item(-1)",
        ),
        (
            "struct item:\n    value R\n    other R",
            "struct item:\n    value N\n    other R",
            "forall p &item:\n    p.value $in R",
            "forall p &item:\n    p.value $in N",
        ),
        (
            "let item = 1",
            "prop item(t R):\n    t = 0",
            "item = 1",
            "item = 2",
        ),
        (
            "let item = 1",
            "thm item:\n    ? 1 = 1",
            "item = 1",
            "item = 2",
        ),
    ] {
        let mut rt = runtime();
        success(&mut rt, prefix);
        let original_id = rt.resolve_plain_atom("item").unwrap();
        let result = rt.run_litex_code(duplicate).unwrap();
        parse_error(&result);
        assert!(result
            .session_error
            .unwrap()
            .to_string()
            .contains("already bound"));
        assert_eq!(rt.resolve_plain_atom("item").unwrap(), original_id);
        success(&mut rt, old_fact);
        assert!(!rt.run_litex_code(wrong_fact).unwrap().success);
        assert!(!rt.run_litex_code("0 = 1").unwrap().success);
    }
}

#[test]
fn repeated_names_reject_visible_shadowing_and_duplicate_binders() {
    for duplicate in [
        "forall x R:\n    x = x",
        "sketch:\n    let x = 2",
        "have fn f(x R) R = x",
        "let f = fn(x R) R {x}",
        "let S = {x R: x = x}",
    ] {
        let mut rt = runtime();
        success(&mut rt, "let x = 1");
        let original_id = rt.resolve_plain_atom("x").unwrap();
        let result = rt.run_litex_code(duplicate).unwrap();
        parse_error(&result);
        assert!(result
            .session_error
            .unwrap()
            .to_string()
            .contains("already bound"));
        assert_eq!(rt.resolve_plain_atom("x").unwrap(), original_id);
        success(&mut rt, "x = 1");
        assert!(!rt.run_litex_code("x = 2").unwrap().success);
    }
    let mut rt = runtime();
    let result = rt.run_litex_code("forall t, t R:\n    t = t").unwrap();
    parse_error(&result);
    assert!(rt.resolve_plain_atom("t").is_err());
    success(&mut rt, "let t = 2\nt = 2");
}

#[test]
fn repeated_names_after_closed_scopes_have_fresh_ids_and_no_old_equations() {
    let mut rt = runtime();
    success(&mut rt, "sketch:\n    let item = 1\n    item = 1");
    assert!(rt.resolve_plain_atom("item").is_err());
    let after_first_scope = rt.global_ids.to_u64s().3;
    success(&mut rt, "sketch:\n    let item = 2\n    item = 2");
    assert!(rt.resolve_plain_atom("item").is_err());
    assert!(rt.global_ids.to_u64s().3 > after_first_scope);
    success(&mut rt, "let item = 3\nitem = 3");
    assert!(rt.resolve_plain_atom("item").unwrap().value() >= after_first_scope);
    assert!(!rt.run_litex_code("item = 1").unwrap().success);
    assert!(!rt.run_litex_code("item = 2").unwrap().success);
    success(&mut rt, "forall x R:\n    x = x\nforall x R:\n    x = x");
    assert!(!rt.run_litex_code("0 = 1").unwrap().success);
}

#[test]
fn tokenization_failure_still_precedes_all_execution() {
    let mut rt = runtime();
    assert!(rt.run_litex_code("let unseen = 1\n\"\"\"\n").is_err());
    assert!(rt.resolve_plain_atom("unseen").is_err());
    assert!(!rt
        .top_exec_env()
        .definitions
        .identifiers
        .contains_key("unseen"));
}
