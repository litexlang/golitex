//! Stage A remainder order-builtin gates.
//!
//! Mirrors the one-lit-per-rule tracers under
//! `examples/proof_nodes/atomic/by_builtin_rule/` for:
//! neg-divisor flip, div↔product bridges, numeric bound chase, integer
//! successor/adjacency/predecessor, positive even `1 < i`, finite-set max/min
//! member bounds, union card, and surjection card.

use crate::execute::ExecStmtResult;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime_with_file_env() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: false,
        language: OutputLanguage::English,
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

#[test]
fn order_stage_a_neg_divisor_flip() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R").is_failed());
    assert!(!exec_one(&mut runtime, "have b R").is_failed());
    assert!(!exec_one(&mut runtime, "have c R").is_failed());
    assert!(!exec_one(&mut runtime, "trust c < 0").is_failed());
    assert!(!exec_one(&mut runtime, "trust c != 0").is_failed());
    assert!(!exec_one(&mut runtime, "trust b <= a").is_failed());
    assert!(
        !exec_one(&mut runtime, "a / c <= b / c").is_failed(),
        "weak neg-divisor flip"
    );
    assert!(!exec_one(&mut runtime, "trust b < a").is_failed());
    assert!(
        !exec_one(&mut runtime, "a / c < b / c").is_failed(),
        "strict neg-divisor flip"
    );
}

#[test]
fn order_stage_a_div_product_bridges() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R").is_failed());
    assert!(!exec_one(&mut runtime, "have b R").is_failed());
    assert!(!exec_one(&mut runtime, "have c R").is_failed());
    assert!(!exec_one(&mut runtime, "trust 0 < c").is_failed());
    assert!(!exec_one(&mut runtime, "trust c != 0").is_failed());
    assert!(!exec_one(&mut runtime, "trust c * a <= b").is_failed());
    assert!(
        !exec_one(&mut runtime, "a <= b / c").is_failed(),
        "product → quotient bridge"
    );

    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R").is_failed());
    assert!(!exec_one(&mut runtime, "have b R").is_failed());
    assert!(!exec_one(&mut runtime, "have c R").is_failed());
    assert!(!exec_one(&mut runtime, "trust 0 < c").is_failed());
    assert!(!exec_one(&mut runtime, "trust c != 0").is_failed());
    assert!(!exec_one(&mut runtime, "trust a / c <= b").is_failed());
    assert!(
        !exec_one(&mut runtime, "a <= b * c").is_failed(),
        "quotient → product bridge"
    );
}

#[test]
fn order_stage_a_numeric_bound_chase() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have x R").is_failed());
    assert!(!exec_one(&mut runtime, "trust 4 < x").is_failed());
    assert!(
        !exec_one(&mut runtime, "2 <= x").is_failed(),
        "weaken lower bound to weak"
    );
    assert!(
        !exec_one(&mut runtime, "2 < x").is_failed(),
        "weaken lower bound to strict"
    );

    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have x Z").is_failed());
    assert!(!exec_one(&mut runtime, "trust 4 < x").is_failed());
    assert!(
        !exec_one(&mut runtime, "5 <= x").is_failed(),
        "strict predecessor → weak successor lower bound"
    );

    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have x R").is_failed());
    assert!(!exec_one(&mut runtime, "trust x < 4").is_failed());
    assert!(
        !exec_one(&mut runtime, "x <= 6").is_failed(),
        "weaken upper bound to weak"
    );
    assert!(
        !exec_one(&mut runtime, "x < 6").is_failed(),
        "weaken upper bound to strict"
    );
}

#[test]
fn order_stage_a_integer_successor_adjacency_predecessor() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a Z").is_failed());
    assert!(!exec_one(&mut runtime, "have b Z").is_failed());
    assert!(!exec_one(&mut runtime, "trust a < b").is_failed());
    assert!(
        !exec_one(&mut runtime, "a + 1 <= b").is_failed(),
        "integer successor"
    );
    assert!(
        !exec_one(&mut runtime, "a <= b - 1").is_failed(),
        "integer predecessor"
    );
    assert!(
        !exec_one(&mut runtime, "1 <= b - a").is_failed(),
        "integer difference at least one"
    );

    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a Z").is_failed());
    assert!(!exec_one(&mut runtime, "have b Z").is_failed());
    assert!(!exec_one(&mut runtime, "trust a < b + 1").is_failed());
    assert!(
        !exec_one(&mut runtime, "a <= b").is_failed(),
        "integer adjacency"
    );
}

#[test]
fn order_stage_a_positive_even_gt_one() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have count Z").is_failed());
    assert!(!exec_one(&mut runtime, "trust count $in N+").is_failed());
    assert!(!exec_one(&mut runtime, "trust 2 != 0").is_failed());
    assert!(!exec_one(&mut runtime, "trust count % 2 = 0").is_failed());
    assert!(
        !exec_one(&mut runtime, "1 < count").is_failed(),
        "positive even exceeds one"
    );
}

#[test]
fn order_stage_a_finite_set_max_min_members() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "1 $in {1, 3}").is_failed());
    assert!(
        !exec_one(&mut runtime, "1 <= finite_set_max({1, 3})").is_failed(),
        "member <= max"
    );
    assert!(!exec_one(&mut runtime, "3 $in {1, 3}").is_failed());
    assert!(
        !exec_one(&mut runtime, "finite_set_min({1, 3}) <= 3").is_failed(),
        "min <= member"
    );
}

#[test]
fn order_stage_a_finite_set_size_union_and_surjection() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "$is_finite_set({1})").is_failed());
    assert!(!exec_one(&mut runtime, "$is_finite_set({2})").is_failed());
    assert!(!exec_one(&mut runtime, "trust $is_finite_set(union({1}, {2}))").is_failed());
    assert!(
        !exec_one(
            &mut runtime,
            "finite_set_size(union({1}, {2})) <= finite_set_size({1}) + finite_set_size({2})"
        )
        .is_failed(),
        "union card <= sum"
    );

    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have A set = {1, 2}").is_failed());
    assert!(!exec_one(&mut runtime, "have B set = {1}").is_failed());
    assert!(!exec_one(&mut runtime, "have fn f(x A) B = 1").is_failed());
    assert!(!exec_one(&mut runtime, "trust $surjective(A, B, f)").is_failed());
    assert!(!exec_one(&mut runtime, "$is_finite_set(A)").is_failed());
    assert!(!exec_one(&mut runtime, "$is_finite_set(B)").is_failed());
    assert!(
        !exec_one(&mut runtime, "finite_set_size(B) <= finite_set_size(A)").is_failed(),
        "surjection codomain card <= domain"
    );
}
