use crate::parsing::Tokenizer;
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

fn fixture_child(runtime: &mut Runtime, fact: Fact) -> VerifyFactResult {
    let proof = SuccessProveFactResult::new(
        fact.clone(),
        SuccessInferResult::new(),
        SuccessFactProofResult::builtin_rule_with_evidence(
            "fixture child",
            BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TestFixture),
            Vec::new(),
        ),
    )
    .into();
    runtime
        .complete_fact_proof_result(&fact, proof, &VerifyState::initial())
        .expect("fixture child WD verifies")
}

#[test]
fn registered_antisymmetric_predicate_verifier_combines_two_ordered_child_results() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("registered_antisymmetric_result_test.lit");
    let Fact::AtomicFact(AtomicFact::EqualFact(equal_fact)) = parse_fact(&mut runtime, "R = C")
    else {
        panic!("fixture target should be an equality")
    };
    let left_to_right_fact = parse_fact(&mut runtime, "$rel(R, C)");
    let right_to_left_fact = parse_fact(&mut runtime, "$rel(C, R)");
    let left_to_right = fixture_child(&mut runtime, left_to_right_fact);
    let right_to_left = fixture_child(&mut runtime, right_to_left_fact);

    let result = Runtime::wrap_registered_antisymmetric_predicate_result(
        &equal_fact,
        "rel".to_string(),
        left_to_right,
        right_to_left,
    );
    let target_fact: Fact = equal_fact.clone().into();
    let success = runtime
        .complete_fact_proof_result(&target_fact, result, &VerifyState::initial())
        .expect("registered antisymmetry target WD verifies");
    let VerifyFactResult::Verified(success) = success else {
        panic!("registered antisymmetry proves its equality target")
    };
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
            .verified()
            .expect("first antisymmetry child is factual")
            .fact()
            .to_string(),
        "$rel(R, C)"
    );
    assert_eq!(
        right_to_left
            .verified()
            .expect("second antisymmetry child is factual")
            .fact()
            .to_string(),
        "$rel(C, R)"
    );
}
