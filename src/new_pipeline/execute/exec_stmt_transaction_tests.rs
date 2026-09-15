//! Transactional exec_stmt + WD-memory regression tests.

use crate::new_pipeline::ast::obj::{Number, Obj};
use crate::new_pipeline::execute::ExecStmtResult;
use crate::new_pipeline::runtime::{RealOrVirtualPath, Runtime};
use crate::new_pipeline::tokenize::Tokenizer;

fn runtime_with_file_env() -> Runtime {
    let mut runtime = Runtime::new();
    runtime.begin_file(RealOrVirtualPath::Eval);
    runtime
}

fn exec_one(runtime: &mut Runtime, code: &str) -> ExecStmtResult {
    let tokens = Tokenizer::new()
        .tokenize(code, runtime.current_file.clone())
        .expect("tokenize");
    let stmts = runtime.parse(&tokens).expect("parse");
    assert_eq!(stmts.len(), 1, "expected exactly one stmt in:\n{code}");
    runtime.exec_stmt(&stmts[0]).expect("exec_stmt RuntimeResult")
}

fn number_one() -> Obj {
    Obj::Number(Number {
        normalized_value: "1".to_string(),
    })
}

#[test]
fn failed_fact_does_not_pollute_parent_env() {
    let mut runtime = runtime_with_file_env();
    let before_facts = runtime.top_exec_env().facts.facts_by_id.len();
    let before_wd = runtime
        .top_exec_env()
        .well_defined_objects
        .object_to_wd_id
        .len();

    let outcome = exec_one(&mut runtime, "1 = 2");
    assert!(
        outcome.is_failed(),
        "expected soft fail for unprovable 1 = 2"
    );

    assert_eq!(
        runtime.top_exec_env().facts.facts_by_id.len(),
        before_facts,
        "Failed must not merge facts into parent"
    );
    assert_eq!(
        runtime
            .top_exec_env()
            .well_defined_objects
            .object_to_wd_id
            .len(),
        before_wd,
        "Failed must not merge WD records into parent"
    );
}

#[test]
fn success_let_merges_identifier_and_wd() {
    let mut runtime = runtime_with_file_env();

    let outcome = exec_one(&mut runtime, "let x = 1");
    assert!(!outcome.is_failed(), "expected Success for let x = 1");

    assert!(
        runtime
            .top_exec_env()
            .definitions
            .identifiers
            .contains_key("x"),
        "Success must merge identifier `x`"
    );
    assert!(
        runtime
            .top_exec_env()
            .well_defined_objects
            .lookup(&number_one())
            .is_some(),
        "Success must merge WD record for RHS `1`"
    );
}

#[test]
fn second_wd_of_same_obj_hits_known_memory_after_merge() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "let x = 1").is_failed());
    let wd_len_after_first = runtime
        .top_exec_env()
        .well_defined_objects
        .object_to_wd_id
        .len();

    assert!(!exec_one(&mut runtime, "let y = 1").is_failed());
    assert_eq!(
        runtime
            .top_exec_env()
            .well_defined_objects
            .object_to_wd_id
            .len(),
        wd_len_after_first,
        "ByKnown must not insert a second WD entry for the same ObjIR"
    );
    assert!(runtime
        .top_exec_env()
        .definitions
        .identifiers
        .contains_key("y"));
}

#[test]
fn success_merges_equality_so_later_stmt_can_prove_transitivity() {
    let mut runtime = runtime_with_file_env();

    assert!(!exec_one(&mut runtime, "trust 1 = 2").is_failed());
    assert!(!exec_one(&mut runtime, "trust 2 = 3").is_failed());

    let outcome = exec_one(&mut runtime, "1 = 3");
    assert!(
        !outcome.is_failed(),
        "expected Success: parent-merged 1=2 and 2=3 should prove 1=3"
    );
}
