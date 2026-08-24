use crate::parse::Tokenizer;
use crate::prelude::*;
use std::rc::Rc;

fn parse_fact(runtime: &mut Runtime, source: &str) -> Fact {
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks(source, Rc::from("registered_antisymmetric_result_test.lit"))
        .expect("test fact should tokenize");
    assert_eq!(blocks.len(), 1);
    runtime
        .parse_fact(&mut blocks[0])
        .expect("test fact should parse")
}

fn fixture_child(fact: Fact) -> StmtResult {
    SuccessFactStmtResult::new(
        fact,
        SuccessInferResult::new(),
        SuccessFactProofResult::builtin_rule("fixture child"),
    )
    .into()
}

#[test]
fn registered_antisymmetric_predicate_verifier_combines_two_ordered_child_results() {
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("registered_antisymmetric_result_test.lit");
    let Fact::AtomicFact(AtomicFact::EqualFact(equal_fact)) = parse_fact(&mut runtime, "R = C")
    else {
        panic!("fixture target should be an equality")
    };
    let left_to_right = fixture_child(parse_fact(&mut runtime, "$rel(R, C)"));
    let right_to_left = fixture_child(parse_fact(&mut runtime, "$rel(C, R)"));

    let result = Runtime::wrap_registered_antisymmetric_predicate_result(
        &equal_fact,
        "rel".to_string(),
        left_to_right,
        right_to_left,
    );
    let success = result
        .factual_success()
        .expect("registered antisymmetry proves its equality target");
    let SuccessFactProofResult::BuiltinRule(builtin) = success.proof() else {
        panic!("registered antisymmetry should be an explicit builtin combine")
    };
    let Some(BuiltinRuleEvidence::RegisteredAntisymmetricPredicate(evidence)) =
        builtin.evidence.typed()
    else {
        panic!("registered antisymmetry should retain typed evidence")
    };
    assert_eq!(evidence.expected_target.to_string(), "R = C");
    assert_eq!(evidence.predicate_name, "rel");
    let [left_to_right, right_to_left] = builtin.subgoals.as_slice() else {
        panic!("registered antisymmetry should retain two ordered child Results")
    };
    assert_eq!(
        left_to_right
            .factual_success()
            .expect("first antisymmetry child is factual")
            .fact()
            .to_string(),
        "$rel(R, C)"
    );
    assert_eq!(
        right_to_left
            .factual_success()
            .expect("second antisymmetry child is factual")
            .fact()
            .to_string(),
        "$rel(C, R)"
    );
}
