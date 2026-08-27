//! Tests for non-equational atomic verification.

use crate::common::defaults::default_line_file;
use crate::fact::{AtomicFact, Fact, InFact};
use crate::infer::SuccessInferResult;
use crate::obj::{Add, Number, Obj, StandardSet};
use crate::parse::Tokenizer;
use crate::result::{
    BuiltinRuleEvidence, EvaluateBinaryObjOperator, StmtResult, SuccessEvaluateObjStepResult,
    SuccessFactProofResult, SuccessFactStmtResult, SuccessStmtResult,
};
use crate::runtime::Runtime;
use crate::stmt::Stmt;
use crate::test_support::execute_source;
use std::rc::Rc;

#[test]
fn direct_numeric_membership_retains_recursive_evaluation_evidence() {
    let expression: Obj = Add::new(
        Number::new("2".to_string()).into(),
        Number::new("3".to_string()).into(),
    )
    .into();
    let fact: AtomicFact =
        InFact::new(expression, StandardSet::N.into(), default_line_file()).into();

    let result = Runtime::default().verify_non_equational_atomic_fact_by_direct_evaluation(&fact);
    let StmtResult::Success(SuccessStmtResult::Fact(success)) = result else {
        panic!("2 + 3 in N should be a successful fact result");
    };
    let SuccessFactProofResult::BuiltinRule(builtin) = success.proof() else {
        panic!("direct membership should select one builtin proof");
    };
    let Some(BuiltinRuleEvidence::ClosedNumericMembership(evidence)) = builtin.evidence.typed()
    else {
        panic!("direct membership should retain its numeric evaluation");
    };

    assert_eq!(evidence.expected_target.to_string(), "2 + 3 $in N");
    assert_eq!(evidence.target_set, StandardSet::N);
    assert_eq!(evidence.evaluation.expression.to_string(), "2 + 3");
    assert_eq!(evidence.evaluation.value.normalized_value, "5");
    let SuccessEvaluateObjStepResult::Binary(binary) = &evidence.evaluation.step else {
        panic!("2 + 3 should retain the addition node");
    };
    assert_eq!(binary.operator, EvaluateBinaryObjOperator::Add);
    assert!(matches!(
        binary.left.step,
        SuccessEvaluateObjStepResult::Literal(_)
    ));
    assert!(matches!(
        binary.right.step,
        SuccessEvaluateObjStepResult::Literal(_)
    ));
}

#[test]
fn anonymous_function_membership_is_not_dispatched_by_the_generic_orchestrator() {
    let source = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/verify/atomic/non_equational.rs"
    ));
    let implementation = source.split("#[cfg(test)]").next().unwrap_or(source);

    assert!(!implementation.contains("Obj::AnonymousFn"));
    assert!(!implementation.contains("verify_in_fact_anonymous_fn_signature_matches_fn_set"));
}

#[test]
fn registered_symmetric_predicate_verifier_wraps_the_exact_reordered_child_result() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("registered_symmetric_result_test.lit");
    let (_, setup_error) = execute_source("prop any_set(x set, y set):\n    x = x", &mut runtime);
    assert!(setup_error.is_none(), "{setup_error:?}");
    let mut parse_atomic = |source: &str| {
        let mut blocks = Tokenizer::new()
            .parse_blocks(source, Rc::from("registered_symmetric_result_test.lit"))
            .expect("property fact tokenizes");
        let statement = runtime
            .parse_statement(&mut blocks[0])
            .expect("property fact parses");
        let Stmt::Fact(Fact::AtomicFact(fact)) = statement else {
            panic!("property fact should be atomic")
        };
        fact
    };
    let target = parse_atomic("$any_set(C, R)");
    let alternate = parse_atomic("$any_set(R, C)");
    let alternate_result: StmtResult = SuccessFactStmtResult::new(
        alternate.clone().into(),
        SuccessInferResult::new(),
        SuccessFactProofResult::builtin_rule_with_evidence(
            "fixture child",
            BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TestFixture),
            Vec::new(),
        ),
    )
    .into();
    let result = Runtime::wrap_registered_symmetric_prop_result(
        &target,
        "any_set".to_string(),
        vec![1, 0],
        alternate,
        alternate_result,
    );
    let success = result
        .factual_success()
        .expect("registered symmetry proves its target");
    let SuccessFactProofResult::BuiltinRule(builtin) = success.proof() else {
        panic!("registered symmetry should be an explicit builtin wrapper")
    };
    let Some(BuiltinRuleEvidence::RegisteredSymmetricPredicate(evidence)) =
        builtin.evidence.typed()
    else {
        panic!("registered symmetry should retain typed evidence")
    };
    assert_eq!(evidence.expected_target.to_string(), "$any_set(C, R)");
    assert_eq!(evidence.expected_alternate.to_string(), "$any_set(R, C)");
    assert_eq!(evidence.gather, vec![1, 0]);
    let [child] = builtin.subgoals.as_slice() else {
        panic!("registered symmetry should retain exactly one child Result")
    };
    assert_eq!(
        child
            .factual_success()
            .expect("symmetry child is factual")
            .fact()
            .to_string(),
        "$any_set(R, C)"
    );
}
