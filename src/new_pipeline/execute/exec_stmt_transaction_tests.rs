//! Transactional exec_stmt + WD-memory regression tests.

use crate::new_pipeline::ast::obj::{Number, Obj, ArithmeticOperator, Literal};
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
    Obj::Literal(Literal::Number(Number {
        normalized_value: "1".to_string(),
    }))
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
    use crate::new_pipeline::ast::obj::{Add, Number, Obj, ArithmeticOperator, Literal};
    use crate::new_pipeline::rational_expression::{
        evaluate_obj_to_normalized_decimal_number, two_objs_equal_by_closed_decimal_calculation,
    };
    let one = Obj::Literal(Literal::Number(Number {
        normalized_value: "1".into(),
    }));
    let two = Obj::Literal(Literal::Number(Number {
        normalized_value: "2".into(),
    }));
    let add = Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
        left: Box::new(one.clone()),
        right: Box::new(one.clone()),
    }));
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
    // Store keeps only the two direction foralls (not ForallFactWithIff itself).
    // Later proof search uses ordinary known-forall on those two facts.
    let mut runtime = runtime_with_file_env();
    let outcome = exec_one(
        &mut runtime,
        "forall x, y R:\n    =>:\n        x = y\n    <=>:\n        y = x",
    );
    assert!(
        !outcome.is_failed(),
        "expected Success for forall <=> equality symmetry"
    );
    let facts = &runtime.top_exec_env().facts.facts_by_id;
    assert!(
        !facts
            .values()
            .any(|f| matches!(
                f,
                crate::new_pipeline::ast::fact::Fact::ForallFactWithIff(_)
            )),
        "ForallFactWithIff itself is not stored; only the two direction foralls"
    );
    let forall_count = facts
        .values()
        .filter(|f| matches!(f, crate::new_pipeline::ast::fact::Fact::ForallFact(_)))
        .count();
    assert!(
        forall_count >= 2,
        "expected both then⇒iff and iff⇒then foralls stored, got {forall_count}"
    );

    // Reverse direction is usable via ordinary known-forall instantiate.
    assert!(!exec_one(&mut runtime, "abstract_prop Pp(x)").is_failed());
    assert!(!exec_one(&mut runtime, "abstract_prop Qq(x)").is_failed());
    assert!(
        !exec_one(
            &mut runtime,
            "trust:\n    forall x R:\n        =>:\n            $Pp(x)\n        <=>:\n            $Qq(x)",
        )
        .is_failed()
    );
    assert!(!exec_one(&mut runtime, "trust $Pp(2)").is_failed());
    assert!(
        !exec_one(&mut runtime, "$Qq(2)").is_failed(),
        "stored iff⇒then forall should prove $Qq(2) from $Pp(2)"
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
fn subset_trust_infers_elementwise_forall() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have S set").is_failed());
    assert!(!exec_one(&mut runtime, "have T set").is_failed());
    assert!(!exec_one(&mut runtime, "trust S $subset T").is_failed());
    assert!(
        !exec_one(
            &mut runtime,
            "forall x S:\n    =>:\n        x $in T",
        )
        .is_failed(),
        "subset infer must expose elementwise membership forall"
    );
}

#[test]
fn order_sign_infers_from_literal_bound() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R").is_failed());
    assert!(!exec_one(&mut runtime, "trust a >= 1").is_failed());
    assert!(
        !exec_one(&mut runtime, "0 < a").is_failed(),
        "a >= 1 must infer 0 < a"
    );
}

#[test]
fn order_flip_mul_minus_one_from_less_zero() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R").is_failed());
    assert!(!exec_one(&mut runtime, "trust a < 0").is_failed());
    assert!(
        !exec_one(&mut runtime, "(-1) * a >= 0").is_failed(),
        "a < 0 must infer (-1)*a >= 0"
    );
}

#[test]
fn natural_membership_infers_nonnegative() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have k N").is_failed());
    assert!(
        !exec_one(&mut runtime, "k >= 0").is_failed(),
        "k $in N must infer k >= 0"
    );
}

#[test]
fn positive_standard_set_membership_infers_positive() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R+").is_failed());
    assert!(
        !exec_one(&mut runtime, "0 < a").is_failed(),
        "a $in R+ must infer 0 < a"
    );
}

#[test]
fn list_set_singleton_membership_infers_equality() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have x {2}").is_failed());
    assert!(
        !exec_one(&mut runtime, "x = 2").is_failed(),
        "x $in {{2}} must infer x = 2"
    );
}

#[test]
fn list_set_membership_infers_or_equalities() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a {1, 2}").is_failed());
    assert!(
        !exec_one(&mut runtime, "a = 1 or a = 2").is_failed(),
        "a $in {{1,2}} must infer a=1 or a=2"
    );
}

#[test]
fn union_membership_infers_or() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have A set").is_failed());
    assert!(!exec_one(&mut runtime, "have B set").is_failed());
    assert!(!exec_one(&mut runtime, "have x set").is_failed());
    assert!(!exec_one(&mut runtime, "trust x $in union(A, B)").is_failed());
    assert!(
        !exec_one(&mut runtime, "x $in A or x $in B").is_failed(),
        "union membership must infer or of component memberships"
    );
}

#[test]
fn intersect_membership_infers_both() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have A set").is_failed());
    assert!(!exec_one(&mut runtime, "have B set").is_failed());
    assert!(!exec_one(&mut runtime, "have x set").is_failed());
    assert!(!exec_one(&mut runtime, "trust x $in intersect(A, B)").is_failed());
    assert!(!exec_one(&mut runtime, "x $in A").is_failed());
    assert!(!exec_one(&mut runtime, "x $in B").is_failed());
}

#[test]
fn set_minus_membership_infers_split() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have x set").is_failed());
    assert!(!exec_one(&mut runtime, "trust x $in set_minus({1, 2}, {2})").is_failed());
    assert!(!exec_one(&mut runtime, "x $in {1, 2}").is_failed());
    assert!(!exec_one(&mut runtime, "not x $in {2}").is_failed());
    assert!(!exec_one(&mut runtime, "x != 2").is_failed());
}

#[test]
fn cart_membership_infers_coordinate_membership() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have u set").is_failed());
    assert!(!exec_one(&mut runtime, "trust u $in cart(R, Z)").is_failed());
    assert!(!exec_one(&mut runtime, "$is_tuple(u)").is_failed());
    assert!(!exec_one(&mut runtime, "tuple_dim(u) = 2").is_failed());
    assert!(!exec_one(&mut runtime, "u[1] $in R").is_failed());
    assert!(!exec_one(&mut runtime, "u[2] $in Z").is_failed());
}

#[test]
fn range_membership_infers_integer_bounds() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have i1 Z").is_failed());
    assert!(!exec_one(&mut runtime, "trust i1 $in range(2, 6)").is_failed());
    assert!(!exec_one(&mut runtime, "i1 $in Z").is_failed());
    assert!(!exec_one(&mut runtime, "2 <= i1").is_failed());
    assert!(!exec_one(&mut runtime, "i1 < 6").is_failed());
}

#[test]


fn subtraction_equals_zero_infers_equality() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R").is_failed());
    assert!(!exec_one(&mut runtime, "have b R").is_failed());
    assert!(!exec_one(&mut runtime, "trust a - b = 0").is_failed());
    assert!(
        !exec_one(&mut runtime, "a = b").is_failed(),
        "a - b = 0 must infer a = b"
    );
}

#[test]
fn normal_atomic_param_type_projection() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(
            &mut runtime,
            "prop same(x set, y set):\n    x = y",
        )
        .is_failed()
    );
    assert!(!exec_one(&mut runtime, "have a set").is_failed());
    assert!(!exec_one(&mut runtime, "have b set").is_failed());
    assert!(!exec_one(&mut runtime, "trust $same(a, b)").is_failed());
    assert!(
        !exec_one(&mut runtime, "$is_set(a)").is_failed(),
        "param-type projection must store $is_set(a)"
    );
    assert!(
        !exec_one(&mut runtime, "a = b").is_failed(),
        "expand definition must store a = b"
    );
}

#[test]
fn is_cart_trust_infers_dimension_lower_bound() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "have s set").is_failed(),
        "introduce s"
    );
    assert!(
        !exec_one(&mut runtime, "trust $is_cart(s)").is_failed(),
        "trust is_cart"
    );
    assert!(
        !exec_one(&mut runtime, "cart_dim(s) >= 2").is_failed(),
        "is_cart infer must store cart_dim(s) >= 2"
    );
}

#[test]
fn exist_unique_trust_infers_uniqueness_forall() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "trust exist! x R st {x = 0}").is_failed(),
        "trust exist! must store"
    );
    let facts = &runtime.top_exec_env().facts;
    assert!(
        facts
            .facts_by_id
            .values()
            .any(|f| matches!(f, crate::new_pipeline::ast::fact::Fact::ForallFact(_))),
        "exist! infer must store uniqueness forall"
    );
    assert!(
        !facts.known_forall_conclusions.equal_conclusions.is_empty(),
        "uniqueness forall equal conclusion must be indexed"
    );
    assert!(
        !exec_one(
            &mut runtime,
            "forall a R, b R:\n    a = 0\n    b = 0\n    =>:\n        a = b",
        )
        .is_failed(),
        "uniqueness forall must prove two witnesses equal"
    );
}

#[test]
fn not_exist_trust_infers_demorgan_forall() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "trust not exist y R st {y > 0, y < 0}").is_failed(),
        "trust not exist must store"
    );
    let facts = &runtime.top_exec_env().facts;
    assert!(
        facts
            .facts_by_id
            .values()
            .any(|f| matches!(f, crate::new_pipeline::ast::fact::Fact::ForallFact(_))),
        "not exist infer must store De Morgan forall"
    );
    assert!(
        !facts.known_forall_conclusions.by_or.is_empty(),
        "De Morgan forall or-conclusion must be indexed"
    );
    assert!(
        !exec_one(
            &mut runtime,
            "forall z R:\n    =>:\n        not z > 0 or not z < 0",
        )
        .is_failed(),
        "De Morgan forall must prove the disjunction of negations"
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
fn by_fn_extension_proves_named_fn_equality() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "have fn f(x R) R = x").is_failed(),
        "define f"
    );
    assert!(
        !exec_one(&mut runtime, "have fn g(x R) R = x").is_failed(),
        "define g"
    );
    assert!(
        !exec_one(&mut runtime, "by fn_extension f = g").is_failed(),
        "by fn_extension must prove f = g"
    );
    assert!(
        !exec_one(&mut runtime, "f = g").is_failed(),
        "stored equality must remain known"
    );
}

#[test]
fn by_fn_extension_fails_without_fn_set() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have f set, g set").is_failed());
    assert!(
        exec_one(&mut runtime, "by fn_extension f = g").is_failed(),
        "plain sets must not get fn_extension"
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
fn fn_eq_in_is_removed_parse_error() {
    let mut runtime = runtime_with_file_env();
    for code in ["$fn_eq_in(0, 1, R)", "not $fn_eq_in(0, 1, R)"] {
        let tokens = Tokenizer::new()
            .tokenize(code, runtime.current_file.clone())
            .expect("tokenize");
        let err = runtime
            .parse(&tokens)
            .expect_err("`$fn_eq_in` must be a parse error");
        let msg = format!("{err:?}");
        assert!(
            msg.contains("`$fn_eq_in` is removed") || msg.contains("is removed"),
            "expected removal message, got: {msg} for {code}"
        );
    }
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
fn store_equality_infers_cart_and_tuple_shape() {
    // `s = cart(R, R)` ⇒ `$is_cart(s)` and `cart_dim(s) = 2`.
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have s set = cart(R, R)").is_failed());
    assert!(
        !exec_one(&mut runtime, "$is_cart(s)").is_failed(),
        "expected $is_cart(s) after equality to a literal cart"
    );
    assert!(
        !exec_one(&mut runtime, "cart_dim(s) = 2").is_failed(),
        "expected cart_dim(s) = 2 after equality to cart(R, R)"
    );

    // `t = (1, 2)` ⇒ `$is_tuple(t)` and `tuple_dim(t) = 2`.
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have t set = (1, 2)").is_failed());
    assert!(
        !exec_one(&mut runtime, "$is_tuple(t)").is_failed(),
        "expected $is_tuple(t) after equality to a literal tuple"
    );
    assert!(
        !exec_one(&mut runtime, "tuple_dim(t) = 2").is_failed(),
        "expected tuple_dim(t) = 2 after equality to (1, 2)"
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
            "register reflexive:\n    ? forall x set:\n        $same(x, x)"
        )
        .is_failed(),
        "register reflexive must register"
    );
    assert!(!exec_one(&mut runtime, "have a set").is_failed());
    assert!(
        !exec_one(&mut runtime, "$same(a, a)").is_failed(),
        "reflexive goal must succeed after registration"
    );
}

#[test]
fn register_prop_rejects_proof_body() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(
        &mut runtime,
        "prop same(x set, y set):\n    x = y"
    )
    .is_failed());
    for (label, code) in [
        (
            "reflexive",
            "register reflexive:\n    ? forall x set:\n        $same(x, x)\n    x = x",
        ),
        (
            "symmetric",
            "register symmetric:\n    ? forall x, y set:\n        $same(x, y)\n        =>:\n            $same(y, x)\n    x = y",
        ),
        (
            "transitive",
            "register transitive:\n    ? forall x, y, z set:\n        $same(x, y)\n        $same(y, z)\n        =>:\n            $same(x, z)\n    x = z",
        ),
    ] {
        let tokens = Tokenizer::new()
            .tokenize(code, runtime.current_file.clone())
            .expect("tokenize");
        assert!(
            runtime.parse(&tokens).is_err(),
            "register {label} with proof body must fail parse"
        );
    }
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
            "register symmetric:\n    ? forall x, y set:\n        $same(x, y)\n        =>:\n            $same(y, x)"
        )
        .is_failed(),
        "register symmetric must register"
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
fn fn_set_obj_param_domain_must_not_cite_earlier_binder() {
    use crate::new_pipeline::execute::execute_fact_stmt::well_defined_results::{
        FailToVerifyFnSetObjWellDefined, FailToVerifyFunctionSpaceObjWellDefinedResult,
        FailToVerifyObjWellDefinedResult, VerifyObjWellDefinedResult,
    };
    use crate::new_pipeline::execute::execute_let_stmt::ExecLetObjStmtResult;
    use crate::new_pipeline::execute::exec_stmt_result::{ExecDefinitionStmtResult, ExecDefineObjStmtResult};
    use crate::new_pipeline::execute::ExecStmtResult;

    // Flat dependent obj carriers are rejected: domain sets must be fixed up front.
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have S fn(x R) power_set(R)").is_failed());
    match exec_one(&mut runtime, "let F = fn(x R, y S(x)) R") {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Failed(
                VerifyObjWellDefinedResult::Failed(
                    FailToVerifyObjWellDefinedResult::FunctionSpace(
                        FailToVerifyFunctionSpaceObjWellDefinedResult::FnSet(
                            FailToVerifyFnSetObjWellDefined::ParamTypeCitesEarlierBinder {
                                failed_index: 1,
                            },
                        ),
                    ),
                ),
            )),
        )) => {}
        other => panic!(
            "expected ParamTypeCitesEarlierBinder at group 1, got failed={}",
            other.is_failed()
        ),
    }
    assert!(
        exec_one(&mut runtime, "let g = fn(x R, y S(x)) R {y}").is_failed(),
        "anonymous fn with dependent obj carrier must soft-fail"
    );

    // Non-dependent multi-arg and curried return-set dependence remain OK.
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "let F = fn(x R, y Z) R").is_failed(),
        "fn(x R, y Z) must WD"
    );
    assert!(
        !exec_one(&mut runtime, "let G = fn(S power_set(R)) fn(x S) R").is_failed(),
        "curried return may cite earlier parameter"
    );
    assert!(
        !exec_one(&mut runtime, "let H = fn(x R, y Z: y > x) R").is_failed(),
        "dom_facts may cite earlier parameters"
    );
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
    use crate::new_pipeline::execute::{ExecDefinitionStmtResult, ExecDefineObjStmtResult};
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
    use crate::new_pipeline::execute::{ExecDefinitionStmtResult, ExecDefineObjStmtResult};
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
    use crate::new_pipeline::execute::{ExecDefinitionStmtResult, ExecDefineObjStmtResult};
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
    use crate::new_pipeline::execute::{ExecDefinitionStmtResult, ExecDefineObjStmtResult};
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
        ExecDefinitionStmtResult, ExecDefineObjStmtResult, ExecStmtResult as ESR,
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
        ESR::ReleaseAndExpand(crate::new_pipeline::execute::ExecReleaseAndExpandStmtResult::StructDef(
            ExecReleaseStructDefStmtResult::Success(_),
        )) => {}
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
        ESR::ReleaseAndExpand(crate::new_pipeline::execute::ExecReleaseAndExpandStmtResult::StructDef(
            ExecReleaseStructDefStmtResult::Failed(
                ExecReleaseStructDefStmtFailed::NoDefinitionOwnedCarrier { .. },
            ),
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
            ExecStmtResult::ReleaseAndExpand(crate::new_pipeline::execute::ExecReleaseAndExpandStmtResult::ObjDef(
                ExecReleaseObjDefStmtResult::Success(ok),
            )) => {
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
    use crate::new_pipeline::execute::{ExecDefinitionStmtResult, ExecDefineObjStmtResult};
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

#[test]
fn builtin_prop_by_definition_fork() {
    // Standard-set subset / superset: forall obligation via standard-set chain.
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "by def N $subset R").is_failed(),
        "N subset R by definition"
    );
    assert!(
        !exec_one(&mut runtime, "by def R $superset N").is_failed(),
        "R superset N by definition"
    );

    // User prop fork still works.
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(
        &mut runtime,
        "prop above_zero(x R):
    x > 0"
    )
    .is_failed());
    assert!(
        !exec_one(&mut runtime, "by def $above_zero(1)").is_failed(),
        "user prop by definition"
    );

    // Coprime / dvd: concrete obligations already closed-numeric.
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "by def $coprime(14, 25)").is_failed(),
        "coprime by definition"
    );
    assert!(!exec_one(&mut runtime, "4 % 2 = 0").is_failed());
    assert!(!exec_one(
        &mut runtime,
        "witness exist a Z st {4 = a * 2} from 2"
    )
    .is_failed());
    assert!(
        !exec_one(&mut runtime, "by def $dvd(4, 2)").is_failed(),
        "dvd by definition"
    );

    // Proper_* needs both inclusion and inequality; trust only the atoms.
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have A, B set").is_failed());
    assert!(!exec_one(&mut runtime, "trust A $subset B").is_failed());
    assert!(!exec_one(&mut runtime, "trust A != B").is_failed());
    assert!(
        !exec_one(&mut runtime, "by def $proper_subset(A, B)").is_failed(),
        "proper_subset by definition"
    );
    assert!(
        !exec_one(&mut runtime, "by def $proper_superset(B, A)").is_failed(),
        "proper_superset by definition"
    );
}

#[test]
fn builtin_prop_by_definition_finite_list_subset_is_not_by_def() {
    // Finite list-set inclusion is `by enumerate finite_set`, not by-def forall.
    let mut runtime = runtime_with_file_env();
    assert!(
        exec_one(&mut runtime, "by def {1} $subset {1, 2}").is_failed(),
        "list-set subset must soft-fail on by-def"
    );
}



#[test]
fn not_in_and_set_algebra_builtin_rules() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "not (-1) $in N").is_failed(),
        "closed numeric not-in"
    );
    assert!(
        !exec_one(&mut runtime, "not 4 $in {1, 2, 3}").is_failed(),
        "list-set exhaustive not-in"
    );
    assert!(
        !exec_one(&mut runtime, "1 $in union({1}, {2})").is_failed(),
        "union membership from left"
    );
    assert!(
        !exec_one(&mut runtime, "2 $in intersect({1, 2}, {2, 3})").is_failed(),
        "intersect membership"
    );
    assert!(
        !exec_one(&mut runtime, "2 $in set_minus({1, 2}, {1})").is_failed(),
        "set_minus membership"
    );
    assert!(
        !exec_one(&mut runtime, "not 0 $in union({1}, {2})").is_failed(),
        "union non-membership"
    );
    assert!(
        !exec_one(&mut runtime, "0 <= abs(0)").is_failed(),
        "abs nonnegative on closed 0"
    );
    assert!(!exec_one(&mut runtime, "have a R").is_failed());
    assert!(
        !exec_one(&mut runtime, "0 <= abs(a)").is_failed(),
        "abs nonnegative on free real"
    );
    assert!(!exec_one(&mut runtime, "have x R").is_failed());
    assert!(!exec_one(&mut runtime, "0 <= 1").is_failed());
    assert!(
        !exec_one(&mut runtime, "x <= x + 1").is_failed(),
        "add right nonnegative"
    );
    assert!(
        !exec_one(&mut runtime, "x <= 1 + x").is_failed(),
        "add left nonnegative"
    );
    assert!(!exec_one(&mut runtime, "have y R").is_failed());
    assert!(!exec_one(&mut runtime, "trust x <= y").is_failed());
    assert!(
        !exec_one(&mut runtime, "x + 1 <= y + 1").is_failed(),
        "add right congruence"
    );
    assert!(
        !exec_one(&mut runtime, "2 * x <= 2 * y").is_failed(),
        "mul left nonnegative monotone"
    );
    assert!(!exec_one(&mut runtime, "trust x <= 3").is_failed());
    assert!(!exec_one(&mut runtime, "trust 0 - x <= 3").is_failed());
    assert!(
        !exec_one(&mut runtime, "abs(x) <= 3").is_failed(),
        "abs le from symmetric bounds"
    );
    assert!(!exec_one(&mut runtime, "trust x + y $in R").is_failed());
    assert!(
        !exec_one(&mut runtime, "abs(x + y) <= abs(x) + abs(y)").is_failed(),
        "abs triangle inequality"
    );
    assert!(
        !exec_one(&mut runtime, "abs(x) - abs(y) <= abs(x + y)").is_failed(),
        "abs reverse triangle add"
    );
    assert!(
        !exec_one(&mut runtime, "abs(x) - abs(y) <= abs(x - y)").is_failed(),
        "abs reverse triangle sub"
    );
    assert!(
        !exec_one(&mut runtime, "x + y $in R").is_failed(),
        "real arithmetic closure"
    );
    assert!(!exec_one(&mut runtime, "trust x < 0").is_failed());
    assert!(
        !exec_one(&mut runtime, "0 > x").is_failed(),
        "greater from known less"
    );
    assert!(
        !exec_one(&mut runtime, "{1, 2} $subset N").is_failed(),
        "list-set subset from members"
    );
    assert!(
        !exec_one(&mut runtime, "union({1}, {2}) $subset N").is_failed(),
        "union subset from both operands"
    );
    assert!(
        !exec_one(&mut runtime, "intersect({1, 2}, {2, 3}) $subset N").is_failed(),
        "intersect subset from left upper bound"
    );
    assert!(!exec_one(&mut runtime, "1 $in {1}").is_failed());
    assert!(!exec_one(&mut runtime, "{1} $in {{1}}").is_failed());
    assert!(
        !exec_one(&mut runtime, "1 $in family_union({{1}})").is_failed(),
        "family_union membership"
    );
    assert!(!exec_one(&mut runtime, "2 $in {1, 2}").is_failed());
    assert!(
        !exec_one(&mut runtime, "exist t {1, 2} st {t = 2}").is_failed(),
        "exist equality witness from membership"
    );
    assert!(!exec_one(&mut runtime, "$is_nonempty_set({1})").is_failed());
    assert!(
        !exec_one(&mut runtime, "exist t {1} st {t $in {1}}").is_failed(),
        "exist nonempty-set member witness"
    );

    // Common builtin wave: sign cone, interval membership, N closure, nonzero, infinite set_minus.
    assert!(!exec_one(&mut runtime, "have u R").is_failed());
    assert!(!exec_one(&mut runtime, "have v R").is_failed());
    assert!(!exec_one(&mut runtime, "trust 0 <= u").is_failed());
    assert!(!exec_one(&mut runtime, "trust 0 <= v").is_failed());
    assert!(
        !exec_one(&mut runtime, "0 <= u + v").is_failed(),
        "sum of nonnegatives"
    );
    assert!(
        !exec_one(&mut runtime, "0 <= u * v").is_failed(),
        "product of nonnegatives"
    );
    assert!(!exec_one(&mut runtime, "trust 0 < u").is_failed());
    assert!(!exec_one(&mut runtime, "trust 0 < v").is_failed());
    assert!(
        !exec_one(&mut runtime, "0 < u + v").is_failed(),
        "sum both positive"
    );
    assert!(
        !exec_one(&mut runtime, "0 < u * v").is_failed(),
        "product both positive"
    );
    assert!(!exec_one(&mut runtime, "have x_iv R").is_failed());
    assert!(!exec_one(&mut runtime, "trust x_iv $in R").is_failed());
    assert!(!exec_one(&mut runtime, "trust 0 <= x_iv").is_failed());
    assert!(!exec_one(&mut runtime, "trust x_iv < 1").is_failed());
    assert!(
        !exec_one(&mut runtime, "x_iv $in '[0, 1)").is_failed(),
        "closed-open interval membership"
    );
    assert!(!exec_one(&mut runtime, "trust 2 < x_iv").is_failed());
    assert!(
        !exec_one(&mut runtime, "x_iv $in '(2,)").is_failed(),
        "left-open ray membership"
    );
    assert!(!exec_one(&mut runtime, "have a_pow R").is_failed());
    assert!(
        !exec_one(&mut runtime, "0 <= a_pow^2").is_failed(),
        "even power nonnegative"
    );
    assert!(!exec_one(&mut runtime, "have n_pos N+").is_failed());
    assert!(
        !exec_one(&mut runtime, "1 <= n_pos").is_failed(),
        "N+ implies at least one"
    );
    assert!(!exec_one(&mut runtime, "have s_arg R").is_failed());
    assert!(!exec_one(&mut runtime, "trust 0 <= s_arg").is_failed());
    assert!(
        !exec_one(&mut runtime, "0 <= sqrt(s_arg)").is_failed(),
        "sqrt nonnegative"
    );

    assert!(!exec_one(&mut runtime, "have m N").is_failed());
    assert!(!exec_one(&mut runtime, "have n N").is_failed());
    assert!(
        !exec_one(&mut runtime, "m + n $in N").is_failed(),
        "add in natural"
    );
    assert!(
        !exec_one(&mut runtime, "m * n $in N").is_failed(),
        "mul in natural"
    );
    assert!(!exec_one(&mut runtime, "have z R").is_failed());
    assert!(!exec_one(&mut runtime, "trust z != 0").is_failed());
    assert!(
        !exec_one(&mut runtime, "abs(z) != 0").is_failed(),
        "abs nonzero from arg"
    );
    assert!(!exec_one(&mut runtime, "have p R").is_failed());
    assert!(!exec_one(&mut runtime, "have q R").is_failed());
    assert!(!exec_one(&mut runtime, "trust p != q").is_failed());
    assert!(
        !exec_one(&mut runtime, "p - q != 0").is_failed(),
        "diff nonzero from inequality"
    );
    assert!(!exec_one(&mut runtime, "trust not $is_finite_set(N)").is_failed());
    assert!(
        !exec_one(&mut runtime, "not $is_finite_set(set_minus(N, {0}))").is_failed(),
        "set_minus infinite of infinite finite"
    );
}

#[test]
fn infer_positive_real_power_equal_transfers_r_pos_membership() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have base R+").is_failed());
    assert!(!exec_one(&mut runtime, "have pow_val R").is_failed());
    // Pow WD currently accepts C×N (and C×Z×base≠0), not yet R+×R.
    assert!(!exec_one(&mut runtime, "trust base^2 = pow_val").is_failed());
    assert!(
        !exec_one(&mut runtime, "pow_val $in R+").is_failed(),
        "a^n = y with 0 < a and n in N must infer y $in R+"
    );
}

#[test]
fn trust_in_fn_set_registers_in_function_set_for_application_wd() {
    let mut runtime = runtime_with_file_env();
    use crate::new_pipeline::exec_env::SpecialObjectPropertyByDefinition;
    assert!(!exec_one(&mut runtime, "have f set").is_failed());
    assert!(!exec_one(&mut runtime, "trust f $in fn(t R) R").is_failed());
    assert!(
        runtime
            .top_exec_env()
            .special_object_properties
            .values()
            .flatten()
            .any(|p| matches!(p, SpecialObjectPropertyByDefinition::InFunctionSet(_))),
        "trust f $in fn(...) must register InFunctionSet"
    );
    assert!(!exec_one(&mut runtime, "have arg R").is_failed());
    assert!(!exec_one(&mut runtime, "trust arg = 1").is_failed());
    assert!(
        !exec_one(&mut runtime, "f(arg) $in R").is_failed(),
        "application WD after trust InFunctionSet"
    );
}

#[test]
fn infer_fn_range_membership_projects_codomain() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have fn g(t R) R = t").is_failed());
    assert!(!exec_one(&mut runtime, "have z R").is_failed());
    assert!(!exec_one(&mut runtime, "trust z $in fn_range(g)").is_failed());
    assert!(
        !exec_one(&mut runtime, "z $in R").is_failed(),
        "z $in fn_range(g) must infer z $in R"
    );
}

#[test]
fn infer_finite_seq_and_seq_expand_to_fn_set_for_application() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have s set").is_failed());
    assert!(!exec_one(&mut runtime, "trust s $in finite_seq(R, 3)").is_failed());
    assert!(
        !exec_one(&mut runtime, "s(1) $in R").is_failed(),
        "finite_seq membership must expand to FnSet"
    );
    assert!(!exec_one(&mut runtime, "have seq_s set").is_failed());
    assert!(!exec_one(&mut runtime, "trust seq_s $in seq(R)").is_failed());
    assert!(
        !exec_one(&mut runtime, "seq_s(1) $in R").is_failed(),
        "seq membership must expand to FnSet"
    );
}

#[test]
fn infer_family_union_membership_emits_exist_member() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have F set").is_failed());
    assert!(!exec_one(&mut runtime, "trust F = {{1}}").is_failed());
    assert!(!exec_one(&mut runtime, "have w set").is_failed());
    assert!(!exec_one(&mut runtime, "trust w $in family_union(F)").is_failed());
    assert!(
        !exec_one(&mut runtime, "exist item F st {w $in item}").is_failed(),
        "family_union membership must infer exist member"
    );
}


#[test]
fn order_div_mod_bridge_smoke() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a Z").is_failed(), "have a Z");
    assert!(!exec_one(&mut runtime, "have b N+").is_failed(), "have b N+");
    assert!(!exec_one(&mut runtime, "trust b != 0").is_failed(), "trust b != 0");
    assert!(!exec_one(&mut runtime, "0 <= a % b").is_failed(), "0 <= a % b");
    assert!(!exec_one(&mut runtime, "a % b < b").is_failed(), "a % b < b");

    assert!(!exec_one(&mut runtime, "have x R").is_failed());
    assert!(!exec_one(&mut runtime, "have y R").is_failed());
    assert!(!exec_one(&mut runtime, "have c R").is_failed());
    assert!(!exec_one(&mut runtime, "trust 0 < c").is_failed());
    assert!(!exec_one(&mut runtime, "trust c != 0").is_failed());
    assert!(!exec_one(&mut runtime, "trust x <= y").is_failed());
    assert!(!exec_one(&mut runtime, "x / c <= y / c").is_failed(), "div monotone");
    assert!(!exec_one(&mut runtime, "trust 0 < x").is_failed());
    assert!(!exec_one(&mut runtime, "trust 1 < c").is_failed());
    assert!(!exec_one(&mut runtime, "x / c < x").is_failed(), "div shrink");
}

#[test]
fn factorial_keyword_and_postfix_bang_parse_and_eval() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "factorial(3) = 6").is_failed(),
        "factorial(3) = 6"
    );
    assert!(!exec_one(&mut runtime, "3! = 6").is_failed(), "3! = 6");
    assert!(
        !exec_one(&mut runtime, "factorial(3) = 3!").is_failed(),
        "factorial(3) = 3!"
    );
    assert!(!exec_one(&mut runtime, "2 != 3").is_failed(), "2 != 3 still works");
}


// Stage A remainder order builtins: see `order_stage_a_remainder_tests.rs`.

#[test]
fn claim_stores_goal_and_sketch_checks_body() {
    use crate::new_pipeline::execute::execute_proof_block_stmt::ExecProofBlockStmtResult;

    let mut runtime = runtime_with_file_env();
    let claim = exec_one(&mut runtime, "claim:\n    ? 1 = 1\n");
    assert!(!claim.is_failed(), "claim should succeed");
    assert!(matches!(claim, ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(_))));
    assert!(!exec_one(&mut runtime, "1 = 1").is_failed(), "claim goal must be stored");

    let mut runtime = runtime_with_file_env();
    let sketch = exec_one(&mut runtime, "sketch:\n    1 = 1\n");
    assert!(!sketch.is_failed(), "sketch should succeed");
    assert!(matches!(sketch, ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Sketch(_))));
}

#[test]
fn sketch_soft_fail_fails_whole_sketch() {
    let mut runtime = runtime_with_file_env();
    // 1 = 2 is a soft-fail fact; sketch must Failed, not SessionError.
    let sketch = exec_one(&mut runtime, "sketch:\n    1 = 2\n");
    assert!(sketch.is_failed(), "sketch body soft-fail must fail the sketch");
}
