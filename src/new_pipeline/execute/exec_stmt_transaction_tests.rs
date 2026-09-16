//! Transactional exec_stmt + WD-memory regression tests.

use crate::new_pipeline::ast::obj::{Number, Obj};
use crate::new_pipeline::execute::ExecStmtResult;
use crate::new_pipeline::launch_command::LaunchCommand;
use crate::new_pipeline::runtime::Runtime;
use crate::new_pipeline::tokenize::Tokenizer;

fn runtime_with_file_env() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: false,
    })
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
fn rational_sum_of_two_fractions_with_product_denominator() {
    use crate::new_pipeline::execute::ExecStmtResult;
    use crate::new_pipeline::execute::execute_fact_stmt::{ExecFactStmtResult, VerifyFactResult};

    let code = "a / b + c / d = (a * d + b * c) / (b * d)";

    // Only b != 0 and d != 0: WD needs (b * d) != 0 for the right denominator.
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R, b R, c R, d R").is_failed());
    assert!(!exec_one(&mut runtime, "trust b != 0").is_failed());
    assert!(!exec_one(&mut runtime, "trust d != 0").is_failed());
    match exec_one(&mut runtime, code) {
        ExecStmtResult::Fact(ExecFactStmtResult::Failed(
            VerifyFactResult::FailToVerifyWellDefined,
        )) => {}
        other => panic!("expected WD fail without b*d != 0, got failed={}", other.is_failed()),
    }

    // With explicit product nonzero, equality should succeed.
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R, b R, c R, d R").is_failed());
    assert!(!exec_one(&mut runtime, "trust b != 0").is_failed());
    assert!(!exec_one(&mut runtime, "trust d != 0").is_failed());
    assert!(!exec_one(&mut runtime, "trust b * d != 0").is_failed());
    assert!(
        !exec_one(&mut runtime, code).is_failed(),
        "expected Success when b*d != 0 is trusted"
    );
}

#[test]
fn calculation_lib_closed_decimal_smoke() {
    use crate::new_pipeline::ast::obj::{Add, Number, Obj};
    use crate::new_pipeline::rational_expression::{
        evaluate_obj_to_normalized_decimal_number, two_objs_equal_by_closed_decimal_calculation,
    };
    let one = Obj::Number(Number { normalized_value: "1".into() });
    let two = Obj::Number(Number { normalized_value: "2".into() });
    let add = Obj::Add(Add { left: Box::new(one.clone()), right: Box::new(one.clone()) });
    let n = evaluate_obj_to_normalized_decimal_number(&add).expect("eval 1+1");
    assert_eq!(n.normalized_value, "2");
    assert!(two_objs_equal_by_closed_decimal_calculation(&add, &two));
}

#[test]
fn calculation_closed_decimal_and_rational_zero_premise() {
    let mut runtime = runtime_with_file_env();

    assert!(
        !exec_one(&mut runtime, "1 $in C").is_failed(),
        "expected Success for 1 $in C"
    );
    assert!(
        !exec_one(&mut runtime, "1 + 1 = 2").is_failed(),
        "expected Success for 1 + 1 = 2"
    );
    assert!(
        !exec_one(&mut runtime, "2 * 3 = 6").is_failed(),
        "expected Success for 2 * 3 = 6"
    );

    assert!(
        !exec_one(&mut runtime, "have x R").is_failed(),
        "expected Success for have x R"
    );
    assert!(
        !exec_one(&mut runtime, "(x + 1) * (x - 1) = x^2 - 1").is_failed(),
        "expected Success for (x + 1) * (x - 1) = x^2 - 1"
    );
    assert!(
        !exec_one(&mut runtime, "x + 0 = x").is_failed(),
        "expected Success for x + 0 = x"
    );
    assert!(
        !exec_one(&mut runtime, "1 * x = x").is_failed(),
        "expected Success for 1 * x = x"
    );
    assert!(
        exec_one(&mut runtime, "x / x = 1").is_failed(),
        "expected soft fail for x / x = 1 (nonzero premise)"
    );

    assert!(
        !exec_one(&mut runtime, "trust x != 0").is_failed(),
        "expected Success for trust x != 0"
    );
    assert!(
        !exec_one(&mut runtime, "x / x = 1").is_failed(),
        "expected Success for x / x = 1 under x != 0"
    );

    assert!(!exec_one(&mut runtime, "have a R, b R, c R").is_failed());
    assert!(!exec_one(&mut runtime, "trust b != 0").is_failed());
    assert!(
        !exec_one(&mut runtime, "a / b + c / b = (a + c) / b").is_failed(),
        "expected Success for same-denominator sum identity"
    );
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
fn forall_reflexive_equality_succeeds_and_stores() {
    let mut runtime = runtime_with_file_env();
    let outcome = exec_one(
        &mut runtime,
        "forall x R:\n    x = x",
    );
    assert!(
        !outcome.is_failed(),
        "expected Success for forall x R: x = x"
    );
    assert!(
        runtime
            .top_exec_env()
            .facts
            .facts_by_id
            .values()
            .any(|f| matches!(f, crate::new_pipeline::ast::fact::Fact::ForallFact(_))),
        "Success must store the forall fact in parent env"
    );
}

#[test]
fn forall_unprovable_then_does_not_store() {
    let mut runtime = runtime_with_file_env();
    let before = runtime.top_exec_env().facts.facts_by_id.len();
    let outcome = exec_one(
        &mut runtime,
        "forall x R:\n    x = 1",
    );
    assert!(
        outcome.is_failed(),
        "expected soft fail for forall with unprovable then"
    );
    assert_eq!(
        runtime.top_exec_env().facts.facts_by_id.len(),
        before,
        "Failed forall must not store into parent"
    );
}

#[test]
fn stored_forall_indexes_equal_then_in_known_forall_conclusions() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "forall x R:\n    x = x").is_failed());
    let facts = &runtime.top_exec_env().facts;
    assert!(
        facts
            .facts_by_id
            .values()
            .any(|f| matches!(f, crate::new_pipeline::ast::fact::Fact::ForallFact(_))),
        "forall must be in facts_by_id"
    );
    assert_eq!(
        facts.known_forall_conclusions.equal_conclusions.len(),
        1,
        "atomic `=` then must be indexed under equal_conclusions"
    );
    let entry = &facts.known_forall_conclusions.equal_conclusions[0];
    assert!(matches!(
        entry.location,
        crate::new_pipeline::ast::fact::ForallConclusionLocation::DirectThenFact(ref loc)
            if loc.then_fact_index == 0
    ));
}

#[test]
fn and_fact_proves_from_known_components_and_projects_store() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "trust 1 < 2").is_failed());
    assert!(!exec_one(&mut runtime, "trust 2 < 3").is_failed());

    let outcome = exec_one(&mut runtime, "1 < 2 and 2 < 3");
    assert!(!outcome.is_failed(), "expected Success for and from known components");
    assert!(
        runtime
            .top_exec_env()
            .facts
            .facts_by_id
            .values()
            .any(|f| matches!(f, crate::new_pipeline::ast::fact::Fact::AndFact(_))),
        "and whole must be stored"
    );
    assert!(
        !exec_one(&mut runtime, "1 < 2").is_failed(),
        "and component must remain usable"
    );
}

#[test]
fn chain_fact_stores_numeric_order_closure() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "trust 1 < 2").is_failed());
    assert!(!exec_one(&mut runtime, "trust 2 < 3").is_failed());
    assert!(!exec_one(&mut runtime, "1 < 2 < 3").is_failed());
    assert!(
        !exec_one(&mut runtime, "1 < 3").is_failed(),
        "expected BuiltinNumericOrder closure 1 < 3"
    );
}

#[test]
fn chain_fact_broken_polarity_does_not_store_cross_edge() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "trust 1 < 2").is_failed());
    assert!(!exec_one(&mut runtime, "trust 2 > 0").is_failed());
    assert!(!exec_one(&mut runtime, "1 < 2 > 0").is_failed());
    assert!(
        exec_one(&mut runtime, "1 < 0").is_failed(),
        "broken polarity must not invent 1 < 0"
    );
}

#[test]
fn chain_fact_stores_equality_closure() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R, b R, c R").is_failed());
    assert!(!exec_one(&mut runtime, "trust a = b").is_failed());
    assert!(!exec_one(&mut runtime, "trust b = c").is_failed());
    assert!(!exec_one(&mut runtime, "a = b = c").is_failed());
    assert!(
        !exec_one(&mut runtime, "a = c").is_failed(),
        "expected BuiltinEquality closure a = c"
    );
}


#[test]
fn witness_exist_succeeds_without_local_proof_body() {
    let mut runtime = runtime_with_file_env();

    let outcome = exec_one(&mut runtime, "witness exist x set st {x = 0} from 0");
    assert!(
        !outcome.is_failed(),
        "expected Success for witness exist with ambient-provable body"
    );
    assert!(matches!(outcome, ExecStmtResult::Witness(_)));
}

#[test]
fn witness_exist_body_miss_is_soft_fail_and_does_not_store() {
    let mut runtime = runtime_with_file_env();
    let before = runtime.top_exec_env().facts.facts_by_id.len();

    let outcome = exec_one(&mut runtime, "witness exist x set st {x = 1} from 0");
    assert!(
        outcome.is_failed(),
        "expected Failed: substituted body 0 = 1 is not provable"
    );
    assert_eq!(
        runtime.top_exec_env().facts.facts_by_id.len(),
        before,
        "Failed witness must not merge exist into parent"
    );
}
