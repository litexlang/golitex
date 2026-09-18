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
    use crate::new_pipeline::execute::execute_fact_stmt::ExecFactStmtResult;

    let code = "a / b + c / d = (a * d + b * c) / (b * d)";

    // Only b != 0 and d != 0: WD needs (b * d) != 0 for the right denominator.
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R, b R, c R, d R").is_failed());
    assert!(!exec_one(&mut runtime, "trust b != 0").is_failed());
    assert!(!exec_one(&mut runtime, "trust d != 0").is_failed());
    match exec_one(&mut runtime, code) {
        ExecStmtResult::Fact(ExecFactStmtResult::Failed(r)) if r.is_wd_failed() => {}
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
fn closed_numeric_order_comparisons() {
    let mut runtime = runtime_with_file_env();
    for code in [
        "1 < 2",
        "2 > 1",
        "1 <= 2",
        "2 >= 1",
        "2 <= 2",
        "2 >= 2",
        "1 + 1 < 5",
        "not 2 < 1",
        "not 1 > 2",
        "not 3 <= 1",
        "not 1 >= 3",
        "1 != 0",
    ] {
        assert!(!exec_one(&mut runtime, code).is_failed(), "expected Success for {code}");
    }
    assert!(exec_one(&mut runtime, "2 < 1").is_failed());
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
fn forall_with_iff_splits_and_proves_both_directions() {
    let mut runtime = runtime_with_file_env();
    let outcome = exec_one(
        &mut runtime,
        "forall x, y R:\n    =>:\n        x = y\n    <=>:\n        y = x",
    );
    assert!(
        !outcome.is_failed(),
        "expected Success for forall <=> equality symmetry"
    );
    assert!(
        runtime
            .top_exec_env()
            .facts
            .facts_by_id
            .values()
            .any(|f| matches!(
                f,
                crate::new_pipeline::ast::fact::Fact::ForallFactWithIff(_)
            )),
        "Success must store the forall-with-iff fact in parent env"
    );
}

#[test]
fn forall_with_iff_one_direction_fail_does_not_store() {
    let mut runtime = runtime_with_file_env();
    let before = runtime.top_exec_env().facts.facts_by_id.len();
    // then⇒iff needs proving y = 1 from x = y (false); should soft-fail.
    let outcome = exec_one(
        &mut runtime,
        "forall x, y R:\n    =>:\n        x = y\n    <=>:\n        y = 1",
    );
    assert!(
        outcome.is_failed(),
        "expected soft fail when one iff direction is unprovable"
    );
    assert_eq!(
        runtime.top_exec_env().facts.facts_by_id.len(),
        before,
        "Failed forall-with-iff must not store into parent"
    );
}

#[test]
fn not_forall_parses_quantifier_free_body() {
    let mut runtime = runtime_with_file_env();
    // Without a known counterexample exist, prove soft-fails.
    let outcome = exec_one(&mut runtime, "not forall x R:\n    x > 0");
    assert!(
        outcome.is_failed(),
        "not forall without known exist counterexample soft-fails"
    );
}

#[test]
fn not_forall_rejects_exist_in_body() {
    let mut runtime = runtime_with_file_env();
    let tokens = Tokenizer::new()
        .tokenize(
            "not forall x R:\n    exist y R st {y = x}",
            runtime.current_file.clone(),
        )
        .expect("tokenize");
    assert!(
        runtime.parse(&tokens).is_err(),
        "nested exist inside not forall must be a parse error"
    );
}

#[test]
fn not_forall_proves_via_known_counterexample_exist() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "trust exist x R st {not x > 0}").is_failed(),
        "trust counterexample exist"
    );
    assert!(
        !exec_one(&mut runtime, "not forall x R:\n    x > 0").is_failed(),
        "not forall proves via known exist counterexample"
    );
}

#[test]
fn not_forall_trust_stores_derived_exist() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(
            &mut runtime,
            "trust:\n    not forall x R:\n        x > 0",
        )
        .is_failed(),
        "trust not forall must store"
    );
    let facts = &runtime.top_exec_env().facts;
    assert!(
        facts
            .facts_by_id
            .values()
            .any(|f| matches!(f, crate::new_pipeline::ast::fact::Fact::NotForall(_))),
        "not forall itself is recorded"
    );
    assert!(
        !facts.known_exist.by_key.is_empty(),
        "derived exist must be indexed in known_exist"
    );
    assert!(
        !exec_one(&mut runtime, "exist x R st {not x > 0}").is_failed(),
        "derived exist must be reusable via known_exist"
    );
}

#[test]
fn fn_eq_is_removed_parse_error() {
    let mut runtime = runtime_with_file_env();
    let tokens = Tokenizer::new()
        .tokenize("$fn_eq(0, 1)", runtime.current_file.clone())
        .expect("tokenize");
    let err = runtime.parse(&tokens).expect_err("`$fn_eq` must be a parse error");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("`$fn_eq` is removed"),
        "expected removal message, got: {msg}"
    );
}

#[test]
fn not_fn_eq_in_parses_trusts_and_proves_known() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "have f set, g set, h set, k set").is_failed(),
        "declare carriers"
    );
    assert!(
        !exec_one(
            &mut runtime,
            "trust not $fn_eq_in(f, g, R)",
        )
        .is_failed(),
        "trust not $fn_eq_in must store"
    );
    assert!(
        !exec_one(&mut runtime, "not $fn_eq_in(f, g, R)").is_failed(),
        "known not $fn_eq_in must prove"
    );
    assert!(
        !exec_one(
            &mut runtime,
            "trust $fn_eq_in(h, k, R)",
        )
        .is_failed(),
        "trust $fn_eq_in still works"
    );
    assert!(
        !exec_one(&mut runtime, "$fn_eq_in(h, k, R)").is_failed(),
        "known $fn_eq_in must prove"
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
fn or_fact_selected_branch_proves_and_stores_known_or() {
    let mut runtime = runtime_with_file_env();
    let outcome = exec_one(&mut runtime, "1 = 1 or 1 = 2");
    assert!(!outcome.is_failed(), "expected Success for or via selected branch");
    let facts = &runtime.top_exec_env().facts;
    assert!(
        facts
            .facts_by_id
            .values()
            .any(|f| matches!(f, crate::new_pipeline::ast::fact::Fact::OrFact(_))),
        "or whole must be stored in facts_by_id"
    );
    assert!(
        !facts.known_or.by_key.is_empty(),
        "or must be indexed in known_or"
    );
    // Second prove should hit known_or.
    assert!(
        !exec_one(&mut runtime, "1 = 1 or 1 = 2").is_failed(),
        "stored or must be reusable via known_or"
    );
}

#[test]
fn or_fact_ill_defined_branch_is_wd_fail() {
    use crate::new_pipeline::execute::execute_fact_stmt::ExecFactStmtResult;

    let mut runtime = runtime_with_file_env();
    match exec_one(&mut runtime, "1 / 0 = 1 or 1 = 1") {
        ExecStmtResult::Fact(ExecFactStmtResult::Failed(r)) if r.is_wd_failed() => {}
        other => panic!(
            "expected WD fail for ill-defined or branch, got failed={}",
            other.is_failed()
        ),
    }
}

#[test]
fn or_fact_unprovable_is_soft_fail_and_does_not_store() {
    let mut runtime = runtime_with_file_env();
    let before = runtime.top_exec_env().facts.facts_by_id.len();
    let known_or_before = runtime.top_exec_env().facts.known_or.by_key.len();
    let outcome = exec_one(&mut runtime, "1 = 2 or 2 = 3");
    assert!(outcome.is_failed(), "expected soft fail when no disjunct proves");
    assert_eq!(
        runtime.top_exec_env().facts.facts_by_id.len(),
        before,
        "Failed or must not store into parent"
    );
    assert_eq!(
        runtime.top_exec_env().facts.known_or.by_key.len(),
        known_or_before,
        "Failed or must not index known_or"
    );
}

#[test]
fn forall_or_then_indexes_by_or_and_instantiates() {
    let mut runtime = runtime_with_file_env();
    // Neither branch is ambient-true, so SelectedBranch fails and known_forall fires.
    assert!(!exec_one(&mut runtime, "prop P(x R)").is_failed());
    assert!(
        !exec_one(
            &mut runtime,
            "trust:\n    forall x R:\n        $P(x)\n        =>:\n            x = 0 or x = 1",
        )
        .is_failed(),
        "trust forall with or then must store"
    );
    let facts = &runtime.top_exec_env().facts;
    assert!(
        !facts.known_forall_conclusions.by_or.is_empty(),
        "or then must be indexed under by_or"
    );
    assert!(!exec_one(&mut runtime, "have a R").is_failed());
    assert!(!exec_one(&mut runtime, "trust $P(a)").is_failed());
    assert!(
        !exec_one(&mut runtime, "a = 0 or a = 1").is_failed(),
        "goal or must instantiate from forall then-or (SelectedBranch cannot prove either arm)"
    );
}

#[test]
fn or_fact_trichotomy_eq_less_greater_by_builtin() {
    use crate::new_pipeline::execute::execute_fact_stmt::{
        ExecFactStmtResult, OrFactSearchProofByBuiltinRule, OrFactSearchedProof, VerifyFactResult,
        VerifyOrFactResult,
    };

    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R, b R").is_failed());
    let outcome = exec_one(&mut runtime, "a = b or a < b or a > b");
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(success)) = outcome else {
        panic!("expected Success for trichotomy EqLessGreater");
    };
    let VerifyFactResult::OrFact(or_result) = success.verify_result else {
        panic!("expected OrFact verify result");
    };
    match or_result.as_ref() {
        VerifyOrFactResult::Success(s) => match &s.searched_proof {
            OrFactSearchedProof::ByBuiltinRule(
                OrFactSearchProofByBuiltinRule::RealLineTrichotomyEqLessGreater(p),
            ) => {
                assert!(!p.left_in_r.is_failed());
                assert!(!p.right_in_r.is_failed());
            }
            _other => panic!("expected EqLessGreater builtin, got other searched_proof"),
        },
        VerifyOrFactResult::Failed(_) => panic!("expected Success"),
    }
}

#[test]
fn or_fact_trichotomy_less_eq_greater_by_builtin() {
    use crate::new_pipeline::execute::execute_fact_stmt::{
        ExecFactStmtResult, OrFactSearchProofByBuiltinRule, OrFactSearchedProof, VerifyFactResult,
        VerifyOrFactResult,
    };

    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R, b R").is_failed());
    let outcome = exec_one(&mut runtime, "a < b or a = b or a > b");
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(success)) = outcome else {
        panic!("expected Success for trichotomy LessEqGreater");
    };
    let VerifyFactResult::OrFact(or_result) = success.verify_result else {
        panic!("expected OrFact verify result");
    };
    match or_result.as_ref() {
        VerifyOrFactResult::Success(s) => assert!(matches!(
            &s.searched_proof,
            OrFactSearchedProof::ByBuiltinRule(
                OrFactSearchProofByBuiltinRule::RealLineTrichotomyLessEqGreater(_)
            )
        )),
        VerifyOrFactResult::Failed(_) => panic!("expected Success"),
    }
}

#[test]
fn or_fact_trichotomy_greater_eq_less_by_builtin() {
    use crate::new_pipeline::execute::execute_fact_stmt::{
        ExecFactStmtResult, OrFactSearchProofByBuiltinRule, OrFactSearchedProof, VerifyFactResult,
        VerifyOrFactResult,
    };

    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R, b R").is_failed());
    let outcome = exec_one(&mut runtime, "a > b or a = b or a < b");
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(success)) = outcome else {
        panic!("expected Success for trichotomy GreaterEqLess");
    };
    let VerifyFactResult::OrFact(or_result) = success.verify_result else {
        panic!("expected OrFact verify result");
    };
    match or_result.as_ref() {
        VerifyOrFactResult::Success(s) => assert!(matches!(
            &s.searched_proof,
            OrFactSearchedProof::ByBuiltinRule(
                OrFactSearchProofByBuiltinRule::RealLineTrichotomyGreaterEqLess(_)
            )
        )),
        VerifyOrFactResult::Failed(_) => panic!("expected Success"),
    }
}

#[test]
fn or_fact_trichotomy_unlisted_order_is_not_builtin() {
    use crate::new_pipeline::execute::execute_fact_stmt::{
        ExecFactStmtResult, OrFactSearchedProof, VerifyFactResult, VerifyOrFactResult,
    };

    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R, b R").is_failed());
    // Supported orders only; this permutation must not hit trichotomy builtin.
    // Without SelectedBranch/forall help it soft-fails.
    let outcome = exec_one(&mut runtime, "a < b or a > b or a = b");
    match outcome {
        ExecStmtResult::Fact(ExecFactStmtResult::Failed(_)) => {}
        ExecStmtResult::Fact(ExecFactStmtResult::Success(success)) => {
            let VerifyFactResult::OrFact(or_result) = success.verify_result else {
                panic!("expected OrFact");
            };
            if let VerifyOrFactResult::Success(s) = or_result.as_ref() {
                assert!(
                    !matches!(&s.searched_proof, OrFactSearchedProof::ByBuiltinRule(_)),
                    "unlisted branch order must not use trichotomy builtin"
                );
            }
        }
        other => panic!("unexpected stmt outcome: failed={}", other.is_failed()),
    }
}

#[test]
fn or_fact_trichotomy_without_reals_does_not_use_builtin() {
    let mut runtime = runtime_with_file_env();
    // a,b introduced without R membership → trichotomy premise miss.
    assert!(!exec_one(&mut runtime, "have a C, b C").is_failed());
    let outcome = exec_one(&mut runtime, "a = b or a < b or a > b");
    assert!(
        outcome.is_failed(),
        "trichotomy requires both sides in R; C alone must soft-fail"
    );
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

#[test]
fn known_atomic_except_equality_by_equality_class() {
    // Exact class hit (reflexive): known `a > 0` proves `a > 0`.
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R, b R").is_failed());
    assert!(!exec_one(&mut runtime, "trust a > 0").is_failed());
    assert!(
        !exec_one(&mut runtime, "a > 0").is_failed(),
        "expected Success for a > 0 from known atomic"
    );

    // Class hit via equality edge: known `a > 0`, `a = b` proves `b > 0`.
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R, b R").is_failed());
    assert!(!exec_one(&mut runtime, "trust a > 0").is_failed());
    assert!(!exec_one(&mut runtime, "trust a = b").is_failed());
    assert!(
        !exec_one(&mut runtime, "b > 0").is_failed(),
        "expected Success for b > 0 via known atomic + a = b"
    );

    // No equality edge: known `a > 0` does not prove `b > 0`.
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R, b R").is_failed());
    assert!(!exec_one(&mut runtime, "trust a > 0").is_failed());
    assert!(
        exec_one(&mut runtime, "b > 0").is_failed(),
        "expected soft fail for b > 0 without a = b"
    );
}

#[test]
fn exist_fact_known_exist_proves_and_stores() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "trust exist x R st {x = 1}").is_failed(),
        "trust exist must store"
    );
    let facts = &runtime.top_exec_env().facts;
    assert!(
        !facts.known_exist.by_key.is_empty(),
        "exist must be indexed in known_exist"
    );
    assert!(
        !exec_one(&mut runtime, "exist x R st {x = 1}").is_failed(),
        "stored exist must be reusable via known_exist"
    );
}

#[test]
fn exist_fact_unprovable_is_soft_fail_and_does_not_store() {
    let mut runtime = runtime_with_file_env();
    let before = runtime.top_exec_env().facts.facts_by_id.len();
    let known_exist_before = runtime.top_exec_env().facts.known_exist.by_key.len();
    // Not covered by RealLineComparisonWitness (both sides are the witness).
    let outcome = exec_one(&mut runtime, "exist x R st {x > x}");
    assert!(
        outcome.is_failed(),
        "expected soft fail when exist has no known/forall/builtin proof"
    );
    assert_eq!(
        runtime.top_exec_env().facts.facts_by_id.len(),
        before,
        "Failed exist must not store into parent"
    );
    assert_eq!(
        runtime.top_exec_env().facts.known_exist.by_key.len(),
        known_exist_before,
        "Failed exist must not index known_exist"
    );
}

#[test]
fn forall_exist_then_indexes_by_exist_and_instantiates() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(
            &mut runtime,
            "trust:\n    forall a R:\n        exist x R st {x = a}",
        )
        .is_failed(),
        "trust forall with exist then must store"
    );
    let facts = &runtime.top_exec_env().facts;
    assert!(
        !facts.known_forall_conclusions.by_exist.is_empty(),
        "exist then must be indexed under by_exist"
    );
    assert!(
        !exec_one(&mut runtime, "exist x R st {x = 2}").is_failed(),
        "goal exist must instantiate from forall then-exist"
    );
}
