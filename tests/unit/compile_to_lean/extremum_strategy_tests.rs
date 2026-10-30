use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_builtin_strategy_result::ExtremumEqualityStrategySingleStep;

const SOURCE: &str = include_str!("../../../lean/examples/extremum_order_strategy/statement.lit");

fn selected(result: &mut RunLitexCodeResult) -> &mut ExtremumEqualityStrategySingleStep {
    let proof = original(result);
    let EqualFactSearchedProof::ByBuiltinStrategy(
        EqualitySearchProofByBuiltinStrategy::ExtremumEquality(proof),
    ) = &mut proof.searched_proof
    else {
        panic!("the real source must select ExtremumEquality")
    };
    proof
}

fn original(result: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    original_at(result, 0)
}

fn original_at(result: &mut RunLitexCodeResult, index: usize) -> &mut VerifyEqualitySuccess {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(fact)) =
        &mut result.statement_results[index]
    else {
        panic!("a verified forall statement")
    };
    let VerifyFactResult::ForallFact(forall) = &mut fact.verify_result else {
        panic!("forall verification")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(forall)) =
        forall.as_mut()
    else {
        panic!("the actual introduced forall")
    };
    super::equality_proof_mut(&mut forall.proved_then_facts[0].verify_result)
}

#[test]
fn extremum_strategy_replays_actual_antisymmetry_children() {
    let (mut result, compiler) = super::execute(SOURCE);
    let proof = selected(&mut result);
    assert_eq!(proof.requirement_facts.len(), 2);
    assert_eq!(proof.proof_of_requirement_facts.len(), 2);
    assert!(matches!(
        original_at(&mut result, 1).searched_proof,
        EqualFactSearchedProof::ByBuiltinStrategy(
            EqualitySearchProofByBuiltinStrategy::ExtremumEquality(_)
        )
    ));
    let output = super::compile_run(&result, &compiler, "extremum_strategy").unwrap();
    assert!(output.contains("Litex.sameOfLeAntisymm"));
    assert!(!output.contains("sorry") && !output.contains("admit"));
}

#[test]
fn extremum_strategy_rejects_missing_reordered_and_mismatched_evidence() {
    for change in [
        "missing_fact",
        "missing_proof",
        "swapped_facts",
        "swapped_proofs",
        "wrong_id",
    ] {
        let (mut result, compiler) = super::execute(SOURCE);
        let proof = selected(&mut result);
        match change {
            "missing_fact" => {
                proof.requirement_facts.pop();
            }
            "missing_proof" => {
                proof.proof_of_requirement_facts.pop();
            }
            "swapped_facts" => proof.requirement_facts.swap(0, 1),
            "swapped_proofs" => proof.proof_of_requirement_facts.swap(0, 1),
            "wrong_id" => {
                let Fact::AtomicFact(AtomicFact::LessEqualFact(fact)) =
                    &mut proof.requirement_facts[0]
                else {
                    unreachable!()
                };
                fact.fact_id = FactId::new(u64::MAX);
            }
            _ => unreachable!(),
        }
        super::phase2_rejected(&result, &compiler, change, &["ExtremumEquality/"]);
    }
}

#[test]
fn extremum_strategy_does_not_certify_another_equality() {
    let (mut result, compiler) = super::execute(SOURCE);
    selected(&mut result);
    let proof = original(&mut result);
    proof.fact.right = proof.fact.left.clone();
    assert!(super::compile_run(&result, &compiler, "changed_extremum").is_err());
}

#[test]
fn extremum_strategy_does_not_hide_a_missing_source_premise() {
    let source = SOURCE.replace("    max(p, q) <= p\n", "");
    let command =
        parse_launch_command(&["-strict".to_string(), "-e".to_string(), source.clone()]).unwrap();
    let mut runtime =
        Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
    assert!(!runtime.run_litex_code(&source).unwrap().success);
}
