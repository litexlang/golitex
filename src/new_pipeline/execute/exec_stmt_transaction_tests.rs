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
    runtime
        .exec_stmt(&stmts[0])
        .expect("exec_stmt RuntimeResult")
}

fn number_one() -> Obj {
    Obj::Number(Number {
        normalized_value: "1".to_string(),
    })
}

#[test]
fn rational_sum_of_two_fractions_with_product_denominator() {
    use crate::new_pipeline::execute::execute_fact_stmt::ExecFactStmtResult;
    use crate::new_pipeline::execute::ExecStmtResult;

    let code = "a / b + c / d = (a * d + b * c) / (b * d)";

    // Only b != 0 and d != 0: WD needs (b * d) != 0 for the right denominator.
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R, b R, c R, d R").is_failed());
    assert!(!exec_one(&mut runtime, "trust b != 0").is_failed());
    assert!(!exec_one(&mut runtime, "trust d != 0").is_failed());
    match exec_one(&mut runtime, code) {
        ExecStmtResult::Fact(ExecFactStmtResult::Failed(r)) if r.is_wd_failed() => {}
        other => panic!(
            "expected WD fail without b*d != 0, got failed={}",
            other.is_failed()
        ),
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
        assert!(
            !exec_one(&mut runtime, code).is_failed(),
            "expected Success for {code}"
        );
    }
    assert!(exec_one(&mut runtime, "2 < 1").is_failed());
}

#[test]
fn calculation_lib_closed_decimal_smoke() {
    use crate::new_pipeline::ast::obj::{Add, Number, Obj};
    use crate::new_pipeline::rational_expression::{
        evaluate_obj_to_normalized_decimal_number, two_objs_equal_by_closed_decimal_calculation,
    };
    let one = Obj::Number(Number {
        normalized_value: "1".into(),
    });
    let two = Obj::Number(Number {
        normalized_value: "2".into(),
    });
    let add = Obj::Add(Add {
        left: Box::new(one.clone()),
        right: Box::new(one.clone()),
    });
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
    let outcome = exec_one(&mut runtime, "forall x R:\n    x = x");
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
        !exec_one(&mut runtime, "trust:\n    not forall x R:\n        x > 0",).is_failed(),
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
    let err = runtime
        .parse(&tokens)
        .expect_err("`$fn_eq` must be a parse error");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("`$fn_eq` is removed"),
        "expected removal message, got: {msg}"
    );
}

#[test]
fn struct_fewer_than_two_fields_is_parse_error() {
    let mut runtime = runtime_with_file_env();
    for code in [
        "struct NoFields:\n    <=>:\n        1 = 1\n",
        "struct Mono:\n    a R\n",
    ] {
        let tokens = Tokenizer::new()
            .tokenize(code, runtime.current_file.clone())
            .expect("tokenize");
        let err = runtime
            .parse(&tokens)
            .expect_err("struct with fewer than two fields must be a parse error");
        let msg = format!("{err:?}");
        assert!(
            msg.contains("at least two fields"),
            "expected two-field requirement, got: {msg} for:\n{code}"
        );
    }
}

#[test]
fn not_fn_eq_in_parses_trusts_and_proves_known() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "have f set, g set, h set, k set").is_failed(),
        "declare carriers"
    );
    assert!(
        !exec_one(&mut runtime, "trust not $fn_eq_in(f, g, R)",).is_failed(),
        "trust not $fn_eq_in must store"
    );
    assert!(
        !exec_one(&mut runtime, "not $fn_eq_in(f, g, R)").is_failed(),
        "known not $fn_eq_in must prove"
    );
    assert!(
        !exec_one(&mut runtime, "trust $fn_eq_in(h, k, R)",).is_failed(),
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
    let outcome = exec_one(&mut runtime, "forall x R:\n    x = 1");
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
    assert!(
        !outcome.is_failed(),
        "expected Success for or via selected branch"
    );
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
    assert!(
        outcome.is_failed(),
        "expected soft fail when no disjunct proves"
    );
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
    assert!(
        !outcome.is_failed(),
        "expected Success for and from known components"
    );
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
fn witness_exist_unique_succeeds_when_body_forces_uniqueness() {
    let mut runtime = runtime_with_file_env();
    let outcome = exec_one(&mut runtime, "witness exist! x R st {x = 0} from 0");
    assert!(
        !outcome.is_failed(),
        "expected Success: uniqueness forall closes from x = 0"
    );
    assert!(
        !exec_one(&mut runtime, "exist! x R st {x = 0}").is_failed(),
        "stored exist! must verify"
    );
}

#[test]
fn witness_atomic_fact_stores_prop_without_storing_exist_first() {
    let mut runtime = runtime_with_file_env();
    let prop = "prop has_copy(a R):\n    exist x R st {x = a}";
    assert!(!exec_one(&mut runtime, prop).is_failed(), "def prop has_copy");
    assert!(
        !exec_one(&mut runtime, "witness $has_copy(2) from 2").is_failed(),
        "witness $P"
    );
    assert!(
        !exec_one(&mut runtime, "$has_copy(2)").is_failed(),
        "stored $P must verify"
    );
}

#[test]
fn witness_atomic_fact_rejects_exist_unique_definition() {
    let mut runtime = runtime_with_file_env();
    let prop = "prop unique_value(a R):\n    exist! x R st {x = a}";
    assert!(!exec_one(&mut runtime, prop).is_failed(), "def prop unique_value");
    let outcome = exec_one(&mut runtime, "witness $unique_value(2) from 2");
    assert!(
        outcome.is_failed(),
        "witness $P must soft-fail on exist! definition clause"
    );
}

#[test]
fn witness_nonempty_set_succeeds_from_membership() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "witness $is_nonempty_set({1, 2}) from 1").is_failed(),
        "witness $is_nonempty_set"
    );
    assert!(
        !exec_one(&mut runtime, "$is_nonempty_set({1, 2})").is_failed(),
        "stored nonempty must verify"
    );
}

#[test]
fn witness_nonempty_set_membership_miss_is_soft_fail() {
    let mut runtime = runtime_with_file_env();
    let before = runtime.top_exec_env().facts.facts_by_id.len();
    let outcome = exec_one(&mut runtime, "witness $is_nonempty_set({1, 2}) from 3");
    assert!(
        outcome.is_failed(),
        "expected Failed: 3 is not in {{1, 2}}"
    );
    assert_eq!(
        runtime.top_exec_env().facts.facts_by_id.len(),
        before,
        "Failed nonempty witness must not merge into parent"
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
fn atomic_order_dual_rewrite_proves_greater_from_known_less() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R, b R").is_failed());
    assert!(!exec_one(&mut runtime, "trust a < b").is_failed());
    assert!(
        !exec_one(&mut runtime, "b > a").is_failed(),
        "OrderDual must prove b > a from known a < b"
    );
}

#[test]
fn atomic_order_dual_does_not_steal_closed_numeric_greater() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "2 > 1").is_failed(),
        "closed 2 > 1 must succeed (builtin ClosedNumericComparison, not dual)"
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

#[test]
fn store_equality_indexes_closed_numeric_equal() {
    use crate::new_pipeline::rational_expression::ClosedNumericExpr;

    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R = 10").is_failed());

    let mut closed_hits = 0;
    for entries in runtime
        .top_exec_env()
        .facts
        .known_closed_numeric_equal
        .values()
    {
        for (expr, _) in entries {
            assert!(
                ClosedNumericExpr::try_from_obj(expr).is_some(),
                "stored representative must classify as ClosedNumericExpr"
            );
            closed_hits += 1;
        }
    }
    assert_eq!(
        closed_hits, 1,
        "exactly one known_closed_numeric_equal for have a R = 10"
    );

    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "1 + 1 = 2").is_failed());
    let closed_hits = runtime
        .top_exec_env()
        .facts
        .known_closed_numeric_equal
        .values()
        .map(|entries| entries.len())
        .sum::<usize>();
    assert_eq!(
        closed_hits, 0,
        "both-closed equality must not index known_closed_numeric_equal"
    );
}

#[test]
fn store_equality_indexes_cart_tuple_equal() {
    use crate::new_pipeline::exec_env::KnownCartTupleEqualShape;

    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a set = (1, 2)").is_failed());

    let entries = &runtime
        .top_exec_env()
        .facts
        .known_cart_tuple_equal
        .by_other_side;
    let mut tuple_hits = 0;
    for values in entries.values() {
        for (shape, _) in values {
            if matches!(shape, KnownCartTupleEqualShape::Tuple(_)) {
                tuple_hits += 1;
            }
        }
    }
    assert_eq!(tuple_hits, 1, "have a set = (1, 2) must index one tuple shape");

    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "(1, 2) = (1, 2)").is_failed());
    assert!(
        runtime
            .top_exec_env()
            .facts
            .known_cart_tuple_equal
            .by_other_side
            .is_empty(),
        "both-side cart/tuple equality must not index known_cart_tuple_equal"
    );
}

#[test]
fn store_equality_indexes_equal_to_obj_with_free_params() {
    use crate::new_pipeline::exec_env::KnownEqualToObjWithFreeParamsShape;

    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "let f = fn(x R) R").is_failed());
    let fn_set_hits = runtime
        .top_exec_env()
        .facts
        .known_equal_to_obj_with_free_params
        .by_other_side
        .values()
        .flat_map(|v| v.iter())
        .filter(|(s, _)| matches!(s, KnownEqualToObjWithFreeParamsShape::FnSet(_)))
        .count();
    assert_eq!(fn_set_hits, 1, "let f = fn(x R) R must index FnSet on f");

    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "let g = fn(x R) R {x}").is_failed());
    let anon_hits = runtime
        .top_exec_env()
        .facts
        .known_equal_to_obj_with_free_params
        .by_other_side
        .values()
        .flat_map(|v| v.iter())
        .filter(|(s, _)| matches!(s, KnownEqualToObjWithFreeParamsShape::AnonymousFn(_)))
        .count();
    assert_eq!(
        anon_hits, 1,
        "let g = fn(x R) R {{x}} must index AnonymousFn on g"
    );

    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "let s = {x R: x > 0}").is_failed());
    let sb_hits = runtime
        .top_exec_env()
        .facts
        .known_equal_to_obj_with_free_params
        .by_other_side
        .values()
        .flat_map(|v| v.iter())
        .filter(|(s, _)| matches!(s, KnownEqualToObjWithFreeParamsShape::SetBuilder(_)))
        .count();
    assert_eq!(
        sb_hits, 1,
        "let s = {{x R: x > 0}} must index SetBuilder on s"
    );
}

fn closed_numeric_equal_rewrite_proves_subterm_goal() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R = 10").is_failed());
    assert!(!exec_one(&mut runtime, "have b R = 20").is_failed());
    assert!(
        !exec_one(&mut runtime, "a + b = 30").is_failed(),
        "multi-subterm ClosedNumericEqual rewrite then calculation"
    );
}


#[test]
fn known_rewrite_reflexivity_registers_and_proves() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(
        &mut runtime,
        "prop same(x set, y set):\n    x = y"
    )
    .is_failed());
    assert!(
        !exec_one(
            &mut runtime,
            "by reflexive_prop:\n    ? forall x set:\n        $same(x, x)"
        )
        .is_failed(),
        "by reflexive_prop must register"
    );
    assert!(!exec_one(&mut runtime, "have a set").is_failed());
    assert!(
        !exec_one(&mut runtime, "$same(a, a)").is_failed(),
        "reflexive goal must succeed after registration"
    );
}

#[test]
fn known_rewrite_reflexivity_search_on_abstract_prop() {
    use crate::new_pipeline::exec_env::exec_env::PropRewriteProperty;

    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "abstract_prop P(x, y)").is_failed());
    let cite = runtime.atomic_name_for_file_root_symbol("P".to_string());
    runtime
        .top_exec_env_mut()
        .prop_rewrite_properties
        .insert(cite, vec![PropRewriteProperty::Reflexive]);
    assert!(!exec_one(&mut runtime, "have a set").is_failed());
    assert!(
        !exec_one(&mut runtime, "$P(a, a)").is_failed(),
        "KnownRewrite Reflexivity must prove $P(a, a) for abstract prop"
    );
    assert!(!exec_one(&mut runtime, "have b set").is_failed());
    assert!(
        exec_one(&mut runtime, "$P(a, b)").is_failed(),
        "reflexivity must not prove $P(a, b)"
    );
}

#[test]
fn known_rewrite_symmetry_proves_swapped_args() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(
        &mut runtime,
        "prop same(x set, y set):\n    x = y"
    )
    .is_failed());
    assert!(
        !exec_one(
            &mut runtime,
            "by symmetric_prop:\n    ? forall x, y set:\n        $same(x, y)\n        =>:\n            $same(y, x)"
        )
        .is_failed(),
        "by symmetric_prop must register"
    );
    assert!(!exec_one(&mut runtime, "have a set, b set").is_failed());
    assert!(!exec_one(&mut runtime, "trust $same(a, b)").is_failed());
    assert!(
        !exec_one(&mut runtime, "$same(b, a)").is_failed(),
        "symmetry must prove swapped args"
    );
}

#[test]
fn known_rewrite_unregistered_reflexive_soft_fails_on_abstract() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "abstract_prop P(x, y)").is_failed());
    assert!(!exec_one(&mut runtime, "have a set").is_failed());
    assert!(
        exec_one(&mut runtime, "$P(a, a)").is_failed(),
        "without registration, abstract reflexive goal must soft-fail"
    );
}

#[test]
fn ambient_by_definition_expands_user_prop() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "prop above_zero(x R):\n    x > 0").is_failed());
    assert!(
        !exec_one(&mut runtime, "$above_zero(1)").is_failed(),
        "ByDefinition must expand file-root WithExportFileId props"
    );
}

#[test]
fn fn_obj_application_requires_in_function_set() {
    use crate::new_pipeline::exec_env::SpecialObjectPropertyByDefinition;

    // No registration → soft fail.
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R = 1").is_failed());
    assert!(!exec_one(&mut runtime, "have f R").is_failed());
    assert!(
        exec_one(&mut runtime, "f(a) = f(a)").is_failed(),
        "f R must not make f(a) well-defined"
    );

    // AnonymousFn registration via let.
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "let f = fn(x R) R {x}").is_failed());
    assert!(
        runtime
            .top_exec_env()
            .special_object_properties
            .values()
            .flatten()
            .any(|p| matches!(p, SpecialObjectPropertyByDefinition::InFunctionSet(_))),
        "let f = anon must store InFunctionSet"
    );
    assert!(!exec_one(&mut runtime, "have a R = 1").is_failed());
    assert!(!exec_one(&mut runtime, "f(a) = f(a)").is_failed());

    // Curried FnSet signature registration.
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "let f = fn(p R) fn(q R) R").is_failed());
    assert!(!exec_one(&mut runtime, "have u R = 2").is_failed());
    assert!(!exec_one(&mut runtime, "have a R = 1").is_failed());
    assert!(!exec_one(&mut runtime, "f(u)(a) = f(u)(a)").is_failed());
}

#[test]
fn fn_arrow_sugar_desugars_to_fn_set() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "let S = R -> R").is_failed(),
        "R -> R must parse and WD as FnSet"
    );
    assert!(!exec_one(&mut runtime, "S = S").is_failed());
    assert!(
        !exec_one(&mut runtime, "let T = R -> R -> Z").is_failed(),
        "right-associative arrow must WD"
    );
    assert!(!exec_one(&mut runtime, "T = T").is_failed());
    assert!(
        !exec_one(&mut runtime, "let U = R × R -> R").is_failed(),
        "cart must bind tighter than arrow"
    );
    assert!(!exec_one(&mut runtime, "U = U").is_failed());
}

#[test]
fn binder_obj_well_definedness_keeps_local_env() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "let S = fn(x R: x > 0) R").is_failed(),
        "FnSet with dom_fact must WD"
    );
    assert!(
        !exec_one(&mut runtime, "let f = fn(x R: x > 0) R {x}").is_failed(),
        "AnonymousFn with dom_fact must WD"
    );
    assert!(
        !exec_one(&mut runtime, "let A = {x R: x > 0}").is_failed(),
        "SetBuilder with fact must WD"
    );

    let mut runtime = runtime_with_file_env();
    assert!(
        exec_one(&mut runtime, "let S = fn(x R: 1 / 0 = x) R").is_failed(),
        "ill-defined FnSet dom_fact must soft-fail"
    );
    let mut runtime = runtime_with_file_env();
    assert!(
        exec_one(&mut runtime, "let A = {x R: 1 / 0 = x}").is_failed(),
        "ill-defined SetBuilder fact must soft-fail"
    );
}

#[test]
fn have_fn_equal_and_by_exist_slice1() {
    use crate::new_pipeline::exec_env::SpecialObjectPropertyByDefinition;

    let mut runtime = runtime_with_file_env();
    let r = exec_one(&mut runtime, "have left_greater R:\n    left_greater > 100");
    assert!(!r.is_failed(), "have by exist should succeed");

    let mut runtime = runtime_with_file_env();
    let r = exec_one(&mut runtime, "have fn id(x R) R = x");
    assert!(!r.is_failed(), "have fn id should succeed");
    assert!(
        runtime
            .top_exec_env()
            .special_object_properties
            .values()
            .flatten()
            .any(|p| matches!(p, SpecialObjectPropertyByDefinition::InFunctionSet(_))),
        "have fn must store InFunctionSet"
    );
    assert!(!exec_one(&mut runtime, "have a R = 1").is_failed());
    assert!(
        !exec_one(&mut runtime, "id(a) = id(a)").is_failed(),
        "id(a)=id(a) after have fn"
    );
}

#[test]
fn have_fn_by_cases_slice2() {
    use crate::new_pipeline::exec_env::SpecialObjectPropertyByDefinition;
    use crate::new_pipeline::execute::execute_have_fn_equal_case_by_case_stmt::{
        ExecHaveFnEqualCaseByCaseStmtFailed, ExecHaveFnEqualCaseByCaseStmtResult,
    };
    use crate::new_pipeline::execute::ExecDefinitionStmtResult;
    use crate::new_pipeline::execute::ExecStmtResult;

    let mut runtime = runtime_with_file_env();
    let code = "have fn nonzero_flag(x R) R by cases:\n    case x = 0: 0\n    case x != 0: 1";
    let r = exec_one(&mut runtime, code);
    match &r {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqualCaseByCase(
            ExecHaveFnEqualCaseByCaseStmtResult::Success(_),
        )) => {}
        ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqualCaseByCase(
            ExecHaveFnEqualCaseByCaseStmtResult::Failed(f),
        )) => {
            let msg = match f {
                ExecHaveFnEqualCaseByCaseStmtFailed::CaseCountMismatch => "CaseCountMismatch",
                ExecHaveFnEqualCaseByCaseStmtFailed::EmptyCases => "EmptyCases",
                ExecHaveFnEqualCaseByCaseStmtFailed::FnSetWellDefined(_) => "FnSetWellDefined",
                ExecHaveFnEqualCaseByCaseStmtFailed::Coverage(_) => "Coverage",
                ExecHaveFnEqualCaseByCaseStmtFailed::Disjoint { i, j } => {
                    panic!("Disjoint {i},{j}")
                }
                ExecHaveFnEqualCaseByCaseStmtFailed::CaseBodyWellDefined(i, _) => {
                    panic!("CaseBodyWellDefined {i}")
                }
                ExecHaveFnEqualCaseByCaseStmtFailed::CaseBodyInRetSet(i, _) => {
                    panic!("CaseBodyInRetSet {i}")
                }
            };
            panic!("have fn by cases failed: {msg}");
        }
        _other => panic!("unexpected result shape for by cases"),
    }
    assert!(
        runtime
            .top_exec_env()
            .special_object_properties
            .values()
            .flatten()
            .any(|p| matches!(p, SpecialObjectPropertyByDefinition::InFunctionSet(_))),
        "by cases must store InFunctionSet"
    );
    assert!(!exec_one(&mut runtime, "have a R = 2").is_failed());
    assert!(
        !exec_one(&mut runtime, "nonzero_flag(a) = nonzero_flag(a)").is_failed(),
        "nonzero_flag(a)=nonzero_flag(a) after by cases"
    );
}

#[test]
fn have_fn_by_exist_stores_membership_and_properties() {
    use crate::new_pipeline::execute::execute_have_fn_by_forall_exist_unique_stmt::ExecHaveFnByForallExistUniqueStmtResult;
    use crate::new_pipeline::execute::ExecDefinitionStmtResult;
    use crate::new_pipeline::execute::ExecStmtResult;
    use crate::new_pipeline::exec_env::SpecialObjectPropertyByDefinition;

    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "abstract_prop F(x, y)").is_failed());
    assert!(!exec_one(&mut runtime, "have A set").is_failed());
    assert!(!exec_one(&mut runtime, "have B set").is_failed());
    assert!(
        !exec_one(
            &mut runtime,
            "trust:\n    forall x A:\n        exist! y B st {$F(x, y)}"
        )
        .is_failed()
    );

    let code = "have fn f by exist!:\n    ? forall x A:\n        exist! y B st {$F(x, y)}";
    let r = exec_one(&mut runtime, code);
    match &r {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByForallExistUnique(
            ExecHaveFnByForallExistUniqueStmtResult::Success(ok),
        )) => {
            assert!(
                !ok.source_forall.is_failed(),
                "source forall must be proven"
            );
            assert!(
                !ok.fn_set_well_defined.is_failed(),
                "FnSet must be well-defined"
            );
        }
        other => panic!(
            "expected Success for by exist!, got failed={}",
            other.is_failed()
        ),
    }

    let props_ok = runtime
        .top_exec_env()
        .special_object_properties
        .values()
        .flatten()
        .any(|p| matches!(p, SpecialObjectPropertyByDefinition::InFunctionSet(_)));
    assert!(props_ok, "by exist! must store InFunctionSet");
}

#[test]
fn have_fn_by_exist_fails_when_forall_unproven() {
    use crate::new_pipeline::execute::execute_have_fn_by_forall_exist_unique_stmt::{
        ExecHaveFnByForallExistUniqueStmtFailed, ExecHaveFnByForallExistUniqueStmtResult,
    };
    use crate::new_pipeline::execute::ExecDefinitionStmtResult;
    use crate::new_pipeline::execute::ExecStmtResult;

    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "abstract_prop F(x, y)").is_failed());
    assert!(!exec_one(&mut runtime, "have A set").is_failed());
    assert!(!exec_one(&mut runtime, "have B set").is_failed());
    // No trust of the forall — selection must soft-fail.
    let code = "have fn f by exist!:\n    ? forall x A:\n        exist! y B st {$F(x, y)}";
    let r = exec_one(&mut runtime, code);
    match &r {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByForallExistUnique(
            ExecHaveFnByForallExistUniqueStmtResult::Failed(
                ExecHaveFnByForallExistUniqueStmtFailed::SourceForall(_),
            ),
        )) => {}
        other => panic!(
            "expected SourceForall soft fail, got failed={}",
            other.is_failed()
        ),
    }
}

#[test]
fn have_fn_by_exist_rejects_proof_body() {
    let mut runtime = runtime_with_file_env();
    let code = "have fn f by exist!:\n    ? forall x R:\n        exist! y R st {y = x}\n    x = x";
    let tokens = Tokenizer::new()
        .tokenize(code, runtime.current_file.clone())
        .expect("tokenize");
    assert!(
        runtime.parse(&tokens).is_err(),
        "by exist! with proof body must fail parse"
    );
}

#[test]
fn have_fn_by_exist_rejects_non_obj_forall_param() {
    let mut runtime = runtime_with_file_env();
    let code = "have fn f by exist!:\n    ? forall S set:\n        exist! y R st {y = 0}";
    let tokens = Tokenizer::new()
        .tokenize(code, runtime.current_file.clone())
        .expect("tokenize");
    assert!(
        runtime.parse(&tokens).is_err(),
        "forall set param must fail parse"
    );
}

#[test]
fn have_fn_by_exist_rejects_plain_exist_then() {
    let mut runtime = runtime_with_file_env();
    let code = "have fn f by exist!:\n    ? forall x R:\n        exist y R st {y = x}";
    let tokens = Tokenizer::new()
        .tokenize(code, runtime.current_file.clone())
        .expect("tokenize");
    assert!(
        runtime.parse(&tokens).is_err(),
        "plain exist then must fail parse"
    );
}

#[test]
fn have_fn_by_exist_rejects_two_then_facts() {
    let mut runtime = runtime_with_file_env();
    let code = "have fn f by exist!:\n    ? forall x R:\n        exist! y R st {y = x}\n        exist! z R st {z = x}";
    let tokens = Tokenizer::new()
        .tokenize(code, runtime.current_file.clone())
        .expect("tokenize");
    assert!(
        runtime.parse(&tokens).is_err(),
        "two then facts must fail parse"
    );
}

#[test]
fn have_fn_by_exist_rejects_exist_in_dom() {
    let mut runtime = runtime_with_file_env();
    let code = "have fn f by exist!:\n    ? forall x R:\n        exist y R st {y = x}\n        =>:\n            exist! z R st {z = x}";
    let tokens = Tokenizer::new()
        .tokenize(code, runtime.current_file.clone())
        .expect("tokenize");
    assert!(
        runtime.parse(&tokens).is_err(),
        "exist in forall dom must fail parse"
    );
}

#[test]
fn have_fn_by_exist_rejects_two_exist_bang_witnesses() {
    let mut runtime = runtime_with_file_env();
    let code = "have fn f by exist!:\n    ? forall x R:\n        exist! y, z R st {y = x, z = x}";
    let tokens = Tokenizer::new()
        .tokenize(code, runtime.current_file.clone())
        .expect("tokenize");
    assert!(
        runtime.parse(&tokens).is_err(),
        "exist! with two witnesses must fail parse"
    );
}

#[test]
fn have_fn_by_exist_rejects_set_typed_witness() {
    let mut runtime = runtime_with_file_env();
    let code = "have fn f by exist!:\n    ? forall x R:\n        exist! S set st {x = x}";
    let tokens = Tokenizer::new()
        .tokenize(code, runtime.current_file.clone())
        .expect("tokenize");
    assert!(
        runtime.parse(&tokens).is_err(),
        "set-typed exist! witness must fail parse"
    );
}

#[test]
fn have_fn_by_cases_sign_trichotomy_slice() {
    let mut runtime = runtime_with_file_env();
    let code = "have fn sign(x R) Z by cases:\n    case x > 0: 1\n    case x = 0: 0\n    case x < 0: (-1)";
    assert!(
        !exec_one(&mut runtime, code).is_failed(),
        "sign by cases (trichotomy) must succeed"
    );
    assert!(!exec_one(&mut runtime, "have a R = 2").is_failed());
    assert!(
        !exec_one(&mut runtime, "sign(a) = sign(a)").is_failed(),
        "sign(a)=sign(a)"
    );
}

#[test]
fn have_fn_by_induc_countdown_slice() {
    use crate::new_pipeline::execute::execute_have_fn_by_induc_stmt::{
        ExecHaveFnByInducStmtFailed, ExecHaveFnByInducStmtResult,
    };
    use crate::new_pipeline::execute::ExecDefinitionStmtResult;
    use crate::new_pipeline::execute::ExecStmtResult;

    let mut runtime = runtime_with_file_env();
    let code = "have fn countdown(n N) N by induc n from 0:\n    case n = 0: 0\n    case n >= 1: countdown(n - 1)";
    let r = exec_one(&mut runtime, code);
    match &r {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
            ExecHaveFnByInducStmtResult::Success(_),
        )) => {}
        ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
            ExecHaveFnByInducStmtResult::Failed(f),
        )) => {
            let msg = match f {
                ExecHaveFnByInducStmtFailed::EmptyCases => "EmptyCases".to_string(),
                ExecHaveFnByInducStmtFailed::FnSetWellDefined(_) => "FnSetWellDefined".to_string(),
                ExecHaveFnByInducStmtFailed::MeasureWellDefined(_) => {
                    "MeasureWellDefined".to_string()
                }
                ExecHaveFnByInducStmtFailed::LowerBoundWellDefined(_) => {
                    "LowerBoundWellDefined".to_string()
                }
                ExecHaveFnByInducStmtFailed::MeasureNotInteger(_) => {
                    "MeasureNotInteger".to_string()
                }
                ExecHaveFnByInducStmtFailed::LowerBoundNotInteger(_) => {
                    "LowerBoundNotInteger".to_string()
                }
                ExecHaveFnByInducStmtFailed::MeasureBelowLower(_) => {
                    "MeasureBelowLower".to_string()
                }
                ExecHaveFnByInducStmtFailed::Coverage(_) => "Coverage".to_string(),
                ExecHaveFnByInducStmtFailed::Disjoint { i, j } => format!("Disjoint {i},{j}"),
                ExecHaveFnByInducStmtFailed::CaseBodyWellDefined(i, _) => {
                    format!("CaseBodyWellDefined {i}")
                }
                ExecHaveFnByInducStmtFailed::CaseBodyInRetSet(i, _) => {
                    format!("CaseBodyInRetSet {i}")
                }
                ExecHaveFnByInducStmtFailed::Shape(s) => format!("Shape({s})"),
            };
            panic!("countdown by induc failed: {msg}");
        }
        other => panic!("unexpected result for induc: failed={}", other.is_failed()),
    }
    assert!(
        !exec_one(&mut runtime, "forall n N:\n    countdown(n) $in N").is_failed(),
        "countdown(n) $in N"
    );
}

#[test]
fn auto_open_point_forall_field_reflexive() {
    use crate::new_pipeline::execute::execute_fact_stmt::ExecFactStmtResult;
    use crate::new_pipeline::execute::execute_fact_stmt::{
        FailToVerifyForallFactWellDefinedResult, VerifyFactResult, VerifyForallFactFailed,
        VerifyForallFactResult,
    };

    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "struct Point:\n    x R\n    y R\n").is_failed(),
        "def struct Point"
    );
    let result = exec_one(&mut runtime, "forall p &Point:\n    p.x = p.x\n");
    match result {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(_)) => {}
        ExecStmtResult::Fact(ExecFactStmtResult::Failed(VerifyFactResult::ForallFact(boxed))) => {
            match *boxed {
                VerifyForallFactResult::Failed(VerifyForallFactFailed::FailToVerifyWellDefined(
                    FailToVerifyForallFactWellDefinedResult::AutoOpenStructLayer(failed),
                )) => panic!("auto-open soft fail: {}", failed.reason),
                VerifyForallFactResult::Failed(VerifyForallFactFailed::FailToVerifyWellDefined(
                    _,
                )) => panic!("forall WD fail (not auto-open)"),
                VerifyForallFactResult::Failed(VerifyForallFactFailed::FailToSearchProof {
                    failed_then_index,
                    ..
                }) => panic!("forall then fail at {failed_then_index}"),
                VerifyForallFactResult::Success(_) => panic!("unexpected"),
            }
        }
        other => panic!("unexpected failed={}", other.is_failed()),
    }
}

#[test]
fn group_struct_def_with_forall_law_succeeds() {
    use crate::new_pipeline::execute::exec_stmt_result::{
        ExecDefinitionStmtResult, ExecStmtResult as ESR,
    };
    use crate::new_pipeline::execute::execute_def_struct_stmt::ExecDefStructStmtResult;

    let code = r#"
struct Group<s nonempty_set>:
    mul fn(x, y s) s
    one s
    inv fn(x s) s
    <=>:
        forall x, y, z s:
            mul(mul(x, y), z) = mul(x, mul(y, z))
        forall x s:
            mul(x, one) = x
            mul(one, x) = x
            mul(inv(x), x) = one
"#;
    let mut runtime = runtime_with_file_env();
    match exec_one(&mut runtime, code) {
        ESR::Definition(ExecDefinitionStmtResult::DefStruct(
            ExecDefStructStmtResult::Success(_),
        )) => {}
        ESR::Definition(ExecDefinitionStmtResult::DefStruct(
            ExecDefStructStmtResult::Failed(fail),
        )) => panic!("struct Group failed: {:?}", std::mem::discriminant(&fail)),
        other => panic!("unexpected {:?}", std::mem::discriminant(&other)),
    }
}


#[test]
fn forall_specialize_field_access_mul() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(
            &mut runtime,
            r#"
struct Group<s nonempty_set>:
    mul fn(x, y s) s
    one s
    <=>:
        forall x s:
            mul(x, one) = x
            mul(one, x) = x
"#
        )
        .is_failed(),
        "def Group"
    );
    assert!(
        !exec_one(
            &mut runtime,
            r#"forall s nonempty_set, G &Group<s>, identity s:
    forall a s:
        G.mul(a, identity) = a
    =>:
        G.mul(G.one, identity) = G.one
"#
        )
        .is_failed(),
        "specialize G.mul(a, identity)=a"
    );
}


#[test]
fn group_identity_unique_via_auto_open() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(
            &mut runtime,
            r#"
struct Group<s nonempty_set>:
    mul fn(x, y s) s
    one s
    inv fn(x s) s
    <=>:
        forall x, y, z s:
            mul(mul(x, y), z) = mul(x, mul(y, z))
        forall x s:
            mul(x, one) = x
            mul(one, x) = x
            mul(inv(x), x) = one
"#
        )
        .is_failed(),
        "def Group"
    );
    assert!(
        !exec_one(
            &mut runtime,
            r#"forall s nonempty_set, G &Group<s>, identity s:
    forall a s:
        G.mul(identity, a) = a
        G.mul(a, identity) = a
    =>:
        identity = G.mul(G.one, identity) = G.one
"#
        )
        .is_failed(),
        "Group identity uniqueness"
    );
}

#[test]
fn release_struct_def_opens_nested_struct_field_layer() {
    use crate::new_pipeline::execute::execute_release_struct_def_stmt::ExecReleaseStructDefStmtResult;
    use crate::new_pipeline::execute::ExecStmtResult as ESR;

    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(
            &mut runtime,
            r#"
struct Coordinates:
    x R
    y R
    <=>:
        x = 0
"#
        )
        .is_failed(),
        "def Coordinates"
    );
    assert!(
        !exec_one(
            &mut runtime,
            r#"
struct TaggedPoint:
    point &Coordinates
    tag N
"#
        )
        .is_failed(),
        "def TaggedPoint"
    );
    // Outer bind auto-opens TaggedPoint only; Coordinates laws stay closed.
    assert!(
        !exec_one(&mut runtime, "trust have p &TaggedPoint").is_failed(),
        "trust have p &TaggedPoint"
    );
    assert!(
        exec_one(&mut runtime, "p.point.x = 0").is_failed(),
        "inner law must miss before release"
    );
    match exec_one(&mut runtime, "release struct def p.point") {
        ESR::ReleaseStructDef(ExecReleaseStructDefStmtResult::Success(_)) => {}
        other => panic!("expected nested release success, got failed={}", other.is_failed()),
    }
    assert!(
        !exec_one(&mut runtime, "p.point.x = 0").is_failed(),
        "inner law after release struct def p.point"
    );
}

#[test]
fn cart_membership_literal_tuple_succeeds() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "(1, 2) $in cart(R, Z)").is_failed(),
        "(1, 2) $in cart(R, Z)"
    );
    assert!(
        exec_one(&mut runtime, "(1, 2, 3) $in cart(R, Z)").is_failed(),
        "arity mismatch must miss"
    );
}

#[test]
fn cart_membership_literal_tuple_succeeds_via_run_eval() {
    use crate::new_pipeline::launch_command::LaunchCommand;
    use crate::new_pipeline::run::run_eval::run_eval;
    let cmd = LaunchCommand::Eval {
        code: "(1, 2) $in cart(R, Z)".to_string(),
        session: false,
        strict: false,
    };
    let result = run_eval(cmd).expect("run_eval");
    assert!(
        !result.process_failed(),
        "run_eval cart membership should succeed"
    );
}

#[test]
fn struct_obj_membership_literal_tuple_succeeds() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(
            &mut runtime,
            r#"
struct Point:
    x R
    y R
"#
        )
        .is_failed(),
        "def Point"
    );
    assert!(
        !exec_one(&mut runtime, "(1, 2) $in &Point").is_failed(),
        "(1, 2) $in &Point"
    );
}

#[test]
fn struct_obj_membership_checks_equivalent_laws() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(
            &mut runtime,
            r#"
struct PosPoint:
    x R
    y R
    <=>:
        x > 0
"#
        )
        .is_failed(),
        "def PosPoint"
    );
    assert!(
        exec_one(&mut runtime, "(0, 2) $in &PosPoint").is_failed(),
        "(0, 2) must miss x > 0"
    );
    assert!(
        !exec_one(&mut runtime, "(1, 2) $in &PosPoint").is_failed(),
        "(1, 2) $in &PosPoint"
    );
}

#[test]
fn release_struct_def_without_carrier_soft_fails() {
    use crate::new_pipeline::execute::execute_release_struct_def_stmt::{
        ExecReleaseStructDefStmtFailed, ExecReleaseStructDefStmtResult,
    };
    use crate::new_pipeline::execute::ExecStmtResult as ESR;

    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have x R").is_failed(), "have x R");
    match exec_one(&mut runtime, "release struct def x") {
        ESR::ReleaseStructDef(ExecReleaseStructDefStmtResult::Failed(
            ExecReleaseStructDefStmtFailed::NoDefinitionOwnedCarrier { .. },
        )) => {}
        other => panic!(
            "expected NoDefinitionOwnedCarrier, got failed={}",
            other.is_failed()
        ),
    }
}

#[test]
fn release_obj_def_smoke() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "let x = 1").is_failed(), "let");
    assert!(!exec_one(&mut runtime, "release obj def x").is_failed(), "release let");
    assert!(!exec_one(&mut runtime, "x = 1").is_failed(), "check let");

    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R = 2").is_failed(), "have equal");
    assert!(!exec_one(&mut runtime, "release obj def a").is_failed(), "release have equal");
    assert!(!exec_one(&mut runtime, "a $in R").is_failed(), "check in");
    assert!(!exec_one(&mut runtime, "a = 2").is_failed(), "check equal");

    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have c R:\n    c > 10").is_failed(), "have by exist");
    assert!(!exec_one(&mut runtime, "release obj def c").is_failed(), "release have by exist");
    assert!(!exec_one(&mut runtime, "c $in R").is_failed(), "check c in");
    assert!(!exec_one(&mut runtime, "c > 10").is_failed(), "check c body");

    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "trust have b R:\n    b > 0").is_failed(),
        "trust have"
    );
    assert!(!exec_one(&mut runtime, "release obj def b").is_failed(), "release trust have");
    assert!(!exec_one(&mut runtime, "b $in R").is_failed(), "check b in");
    assert!(!exec_one(&mut runtime, "b > 0").is_failed(), "check b body");

    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have fn f(t R) R = t").is_failed(), "have fn");
    assert!(!exec_one(&mut runtime, "release obj def f").is_failed(), "release have fn");
    assert!(!exec_one(&mut runtime, "f(1) = 1").is_failed(), "check f application");

    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "abstract_prop F(x, y)").is_failed());
    assert!(!exec_one(&mut runtime, "have A set").is_failed());
    assert!(!exec_one(&mut runtime, "have B set").is_failed());
    assert!(
        !exec_one(
            &mut runtime,
            "trust:\n    forall x A:\n        exist! y B st {$F(x, y)}"
        )
        .is_failed()
    );
    assert!(
        !exec_one(
            &mut runtime,
            "have fn choose by exist!:\n    ? forall x A:\n        exist! y B st {$F(x, y)}"
        )
        .is_failed(),
        "have fn by exist!"
    );
    // Assert the release *kind*, not only a fact that already held before release.
    {
        use crate::new_pipeline::exec_env::StoredIdentifierDefinition;
        use crate::new_pipeline::execute::execute_release_obj_def_stmt::{
            ExecReleaseObjDefStmtResult, ReleaseObjDefByKind,
        };
        use crate::new_pipeline::execute::ExecStmtResult;
        match exec_one(&mut runtime, "release obj def choose") {
            ExecStmtResult::ReleaseObjDef(ExecReleaseObjDefStmtResult::Success(ok)) => {
                assert!(
                    matches!(
                        ok.looked_up,
                        StoredIdentifierDefinition::HaveFnByForallExistUnique(_)
                    ),
                    "def-table row must be HaveFnByForallExistUnique"
                );
                assert!(
                    matches!(
                        ok.released,
                        ReleaseObjDefByKind::HaveFnByForallExistUnique { .. }
                    ),
                    "release kind must rebuild membership+property+uniqueness"
                );
                assert_eq!(
                    ok.store_and_infer.len(),
                    3,
                    "release stores exactly three facts"
                );
            }
            other => panic!(
                "expected release Success for by exist!, got failed={}",
                other.is_failed()
            ),
        }
    }
    assert!(
        !exec_one(
            &mut runtime,
            "forall x A:\n    $F(x, choose(x))"
        )
        .is_failed(),
        "property forall still holds after release"
    );
}


#[test]
fn template_have_fn_by_cases_object_definition_unfold() {
    let mut runtime = runtime_with_file_env();
    let def = "template<a R>:
    have fn above_a(x R) Z by cases:
        case x > a: 1
        case x = a: 0
        case x < a: (-1)";
    assert!(!exec_one(&mut runtime, def).is_failed(), "def");
    for code in [
        "\\above_a<0>(-2) = (-1)",
        "\\above_a<0>(0) = 0",
        "\\above_a<0>(3) = 1",
    ] {
        assert!(!exec_one(&mut runtime, code).is_failed(), "failed: {code}");
    }
}




#[test]
fn template_have_fn_by_induc_object_definition_unfold() {
    let mut runtime = runtime_with_file_env();
    let def = "template<_S set>:
    have fn countdown_t(n N) N by induc n from 0:
        case n = 0: 0
        case n >= 1: countdown_t(n - 1)";
    assert!(!exec_one(&mut runtime, def).is_failed(), "template induc def");
    assert!(
        !exec_one(&mut runtime, "\\countdown_t<{0}>(0) = 0").is_failed(),
        "template induc unfold 0"
    );
    assert!(
        !exec_one(&mut runtime, "\\countdown_t<{0}>(1) = 0").is_failed(),
        "template induc unfold 1"
    );
}

#[test]
fn template_have_fn_by_exist_wires_body() {
    use crate::new_pipeline::execute::execute_def_template_stmt::{
        ExecDefTemplateStmtResult, ExecTemplateDefBodyResult,
    };
    use crate::new_pipeline::execute::ExecDefinitionStmtResult;
    use crate::new_pipeline::execute::ExecStmtResult;

    // Def-time body check + instance release of membership/property/uniqueness.
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "abstract_prop F(x, y)").is_failed());
    assert!(!exec_one(&mut runtime, "have A set").is_failed());
    assert!(!exec_one(&mut runtime, "have B set").is_failed());
    assert!(
        !exec_one(
            &mut runtime,
            "trust:\n    forall x A:\n        exist! y B st {$F(x, y)}"
        )
        .is_failed()
    );
    let def = "template<_S set>:
    have fn choose_t by exist!:
        ? forall x A:
            exist! y B st {$F(x, y)}";
    match exec_one(&mut runtime, def) {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
            ExecDefTemplateStmtResult::Success(ok),
        )) => {
            assert!(
                matches!(
                    ok.body,
                    ExecTemplateDefBodyResult::HaveFnByForallExistUnique(_)
                ),
                "template body must be HaveFnByForallExistUnique"
            );
        }
        other => panic!(
            "expected template Success, got failed={}",
            other.is_failed()
        ),
    }
    assert!(
        !exec_one(&mut runtime, "\\choose_t<{0}> = \\choose_t<{0}>").is_failed(),
        "template instance reflexive equality"
    );
    assert!(
        !exec_one(
            &mut runtime,
            "forall x A:\n    $F(x, \\choose_t<{0}>(x))"
        )
        .is_failed(),
        "template instance property forall"
    );
}



#[test]
fn obtain_from_exist_introduces_witness_and_body() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "witness exist u R st {u = 0} from 0").is_failed(),
        "witness exist"
    );
    assert!(
        !exec_one(&mut runtime, "obtain w from exist u R st {u = 0}").is_failed(),
        "obtain from exist"
    );
    assert!(!exec_one(&mut runtime, "w = 0").is_failed(), "body fact after obtain");
    assert!(!exec_one(&mut runtime, "w $in R").is_failed(), "type fact after obtain");
}

#[test]
fn obtain_from_exist_unique_succeeds_with_trust() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "trust exist! z R st {z = 1}").is_failed(),
        "trust exist!"
    );
    assert!(
        !exec_one(&mut runtime, "obtain uniq from exist! z R st {z = 1}").is_failed(),
        "obtain from exist!"
    );
    assert!(!exec_one(&mut runtime, "uniq = 1").is_failed(), "exist! body after obtain");
}

#[test]
fn obtain_arity_mismatch_soft_fails() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "witness exist u R st {u = 0} from 0").is_failed());
    assert!(
        exec_one(&mut runtime, "obtain a, b from exist u R st {u = 0}").is_failed(),
        "arity mismatch must soft-fail"
    );
}

#[test]
fn template_body_obtain_from_exist_wires() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "witness exist t R st {t = 2} from 2").is_failed(),
        "parent exist for template obtain"
    );
    let code = "template<_S set>:\n    obtain tw from exist t R st {t = 2}";
    assert!(
        !exec_one(&mut runtime, code).is_failed(),
        "template body obtain from exist"
    );
}

#[test]
fn obtain_from_atomic_fact_introduces_witness_and_body() {
    let mut runtime = runtime_with_file_env();
    let prop = "prop has_copy(a R):\n    exist x R st {x = a}";
    assert!(!exec_one(&mut runtime, prop).is_failed(), "def prop has_copy");
    assert!(
        !exec_one(&mut runtime, "$has_copy(2)").is_failed(),
        "$has_copy(2) must verify"
    );
    assert!(
        !exec_one(&mut runtime, "obtain copy from $has_copy(2)").is_failed(),
        "obtain from $P"
    );
    assert!(!exec_one(&mut runtime, "copy = 2").is_failed(), "body after obtain from $P");
    assert!(!exec_one(&mut runtime, "copy $in R").is_failed(), "type after obtain from $P");
}

#[test]
fn obtain_from_thm_introduces_witness_and_body() {
    let mut runtime = runtime_with_file_env();
    let thm = "thm self_exists:\n    ? forall a R:\n        exist x R st {x = a}";
    assert!(!exec_one(&mut runtime, thm).is_failed(), "def thm self_exists");
    assert!(
        !exec_one(&mut runtime, "obtain theorem_copy from thm self_exists(3)").is_failed(),
        "obtain from thm"
    );
    assert!(
        !exec_one(&mut runtime, "theorem_copy = 3").is_failed(),
        "body after obtain from thm"
    );
    assert!(
        !exec_one(&mut runtime, "theorem_copy $in R").is_failed(),
        "type after obtain from thm"
    );
}

#[test]
fn template_body_obtain_from_atomic_fact_wires() {
    let mut runtime = runtime_with_file_env();
    let prop = "prop has_copy(a R):\n    exist x R st {x = a}";
    assert!(!exec_one(&mut runtime, prop).is_failed(), "def prop for template");
    assert!(!exec_one(&mut runtime, "$has_copy(2)").is_failed(), "$has_copy for template");
    let code = "template<_S set>:\n    obtain tw from $has_copy(2)";
    assert!(
        !exec_one(&mut runtime, code).is_failed(),
        "template body obtain from $P"
    );
}

#[test]
fn template_body_obtain_from_thm_wires() {
    let mut runtime = runtime_with_file_env();
    let thm = "thm self_exists:\n    ? forall a R:\n        exist x R st {x = a}";
    assert!(!exec_one(&mut runtime, thm).is_failed(), "def thm for template");
    let code = "template<_S set>:\n    obtain tw from thm self_exists(2)";
    assert!(
        !exec_one(&mut runtime, code).is_failed(),
        "template body obtain from thm"
    );
}

#[test]
fn trust_stored_equality_proves_alpha_equal_fn_set_via_free_params_lookup() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have f set").is_failed());
    assert!(!exec_one(&mut runtime, "trust f = fn(x R) R").is_failed());
    assert!(
        !exec_one(&mut runtime, "f = fn(y R) R").is_failed(),
        "known_equal_to_obj_with_free_params lookup + ByFnSetAlphaEqual shape match"
    );
}

#[test]
fn have_obj_equal_unfolds_like_let_for_alpha_equal_bridge() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have f set = fn(x R) R").is_failed());
    assert!(
        !exec_one(&mut runtime, "f = fn(y R) R").is_failed(),
        "have T = rhs stores RHS in definition table for unfold"
    );
}

#[test]
fn membership_in_identifier_fn_set_via_trust_stored_free_params_lookup() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have fn f(x R) R = x").is_failed());
    assert!(!exec_one(&mut runtime, "have g set").is_failed());
    assert!(!exec_one(&mut runtime, "trust g = fn(y R) R").is_failed());
    assert!(
        !exec_one(&mut runtime, "f $in g").is_failed(),
        "known f $in fn(x R) R and g indexed to fn(y R) R via trust"
    );
}

#[test]
fn membership_in_named_fn_set_from_known_membership_in_alpha_equal_fn_set() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "let R_TO_R = fn(x R) R").is_failed());
    assert!(!exec_one(&mut runtime, "have f set").is_failed());
    assert!(!exec_one(&mut runtime, "trust f $in fn(y R) R").is_failed());
    assert!(
        !exec_one(&mut runtime, "f $in R_TO_R").is_failed(),
        "f $in R_TO_R from known f $in fn(y R) R and R_TO_R = fn(x R) R"
    );
}

#[test]
#[test]
fn anonymous_fn_alpha_equal_and_free_params_lookup_builtins() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "fn(x R) R {x} = fn(y R) R {y}").is_failed(),
        "literal AnonymousFns must be alpha-equal"
    );
    assert!(!exec_one(&mut runtime, "let h = fn(x R) R {x}").is_failed());
    assert!(!exec_one(&mut runtime, "have fn k(x R) R = x").is_failed());
    assert!(
        !exec_one(&mut runtime, "k = h").is_failed(),
        "have-fn name = let-bound anon via free-params lookup"
    );
}

#[test]
fn fn_set_and_set_builder_alpha_equal_builtins() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "R -> R = R -> R").is_failed(),
        "two literal FnSets must be alpha-equal"
    );
    assert!(
        !exec_one(&mut runtime, "{x R: x > 0} = {y R: y > 0}").is_failed(),
        "SetBuilders must be alpha-equal under binder rename"
    );
    assert!(
        !exec_one(
            &mut runtime,
            "forall f R -> R:\n    f $in R -> R"
        )
        .is_failed(),
        "forall membership must bridge via FnSet alpha equality"
    );

    let mut runtime = runtime_with_file_env();
    assert!(
        exec_one(&mut runtime, "R -> N = R -> R").is_failed(),
        "different FnSet return sets must not alpha-equal"
    );
    assert!(
        exec_one(&mut runtime, "{x R: x > 0} = {x R: x > 1}").is_failed(),
        "different SetBuilder bodies must not alpha-equal"
    );
}
