use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_builtin_rewrite_result::EqualitySearchProofByBuiltinRewrite;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_builtin_strategy_result::ArithmeticCongruenceStrategySingleStep;
use crate::prelude::*;

const SOURCE: &str =
    include_str!("../../../../lean/examples/real_shift_square_quotient/statement.lit");

fn arithmetic(result: &mut VerifyFactResult) -> Option<&mut VerifyEqualitySuccess> {
    let VerifyFactResult::Equality(result) = result else {
        return None;
    };
    let VerifyEqualityResult::Success(proof) = result.as_mut() else {
        return None;
    };
    if matches!(
        &proof.searched_proof,
        EqualFactSearchedProof::ByBuiltinStrategy(
            EqualitySearchProofByBuiltinStrategy::ArithmeticCongruence(_)
        )
    ) {
        return Some(proof);
    }
    match &mut proof.searched_proof {
        EqualFactSearchedProof::ByBuiltinRewrite(
            EqualitySearchProofByBuiltinRewrite::FnApplicationUnfoldSubstitution(proof),
        ) => arithmetic(&mut proof.residual_equal),
        EqualFactSearchedProof::ByMatchingOneArgByOne(proof) => proof
            .corresponding_arg_equal_proofs
            .iter_mut()
            .find_map(arithmetic),
        _ => None,
    }
}

fn original(result: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let ExecDefThmBodyProof::Forall(body) =
        &mut super::named_theorem_mut(&mut result.statement_results[1]).body
    else {
        panic!("the original scalar theorem body")
    };
    arithmetic(&mut body.conclusion_proofs[0])
        .expect("the original residual selected ArithmeticCongruence")
}

fn strategy(result: &mut RunLitexCodeResult) -> &mut ArithmeticCongruenceStrategySingleStep {
    let EqualFactSearchedProof::ByBuiltinStrategy(
        EqualitySearchProofByBuiltinStrategy::ArithmeticCongruence(proof),
    ) = &mut original(result).searched_proof
    else {
        unreachable!()
    };
    proof
}

#[test]
fn arithmetic_congruence_strategy_replays_actual_ordered_operand_requirements() {
    let (mut result, compiler) = super::execute(SOURCE);
    let proof = strategy(&mut result);
    assert_eq!(proof.requirement_facts.len(), 2);
    assert_eq!(proof.proof_of_requirement_facts.len(), 2);
    for (requirement, checked) in proof
        .requirement_facts
        .iter()
        .zip(&proof.proof_of_requirement_facts)
    {
        assert_eq!(
            requirement.fact_id(),
            super::equality_proof(checked).fact.fact_id
        );
        assert_eq!(requirement.ir(), super::equality_proof(checked).fact.ir());
    }
    let output = super::compile_run(&result, &compiler, "arithmetic_congruence_actual")
        .expect("the exact selected strategy compiles");
    assert!(output.contains("congrArg₂ M.divValue"));
    assert!(!output.contains("sorry") && !output.contains("admit"));
}

#[test]
fn arithmetic_congruence_strategy_rejects_deleted_requirements_and_proofs() {
    for change in ["requirements", "proofs"] {
        let (mut result, compiler) = super::execute(SOURCE);
        let proof = strategy(&mut result);
        match change {
            "requirements" => proof.requirement_facts.clear(),
            "proofs" => {
                proof.proof_of_requirement_facts.pop();
            }
            _ => unreachable!(),
        }
        super::phase2_rejected(
            &result,
            &compiler,
            change,
            &["ArithmeticCongruence/Requirements"],
        );
    }
}

#[test]
fn arithmetic_congruence_strategy_rejects_wrong_exact_id_subject_and_order() {
    for change in [
        "id",
        "subject",
        "requirements_order",
        "proof_order",
        "both_orders",
    ] {
        let (mut result, compiler) = super::execute(SOURCE);
        let proof = strategy(&mut result);
        match change {
            "id" => {
                let Fact::AtomicFact(AtomicFact::EqualFact(requirement)) =
                    &mut proof.requirement_facts[0]
                else {
                    panic!("operand equality requirement")
                };
                requirement.fact_id = FactId::new(u64::MAX);
            }
            "subject" => {
                let Fact::AtomicFact(AtomicFact::EqualFact(requirement)) =
                    &mut proof.requirement_facts[0]
                else {
                    panic!("operand equality requirement")
                };
                requirement.left = super::number_object("7");
            }
            "requirements_order" => proof.requirement_facts.swap(0, 1),
            "proof_order" => proof.proof_of_requirement_facts.swap(0, 1),
            "both_orders" => {
                proof.requirement_facts.swap(0, 1);
                proof.proof_of_requirement_facts.swap(0, 1);
            }
            _ => unreachable!(),
        }
        super::phase2_rejected(
            &result,
            &compiler,
            change,
            &["ArithmeticCongruence/RequirementSubject"],
        );
    }
}

#[test]
fn arithmetic_congruence_strategy_rejects_a_different_successful_child() {
    let (mut result, compiler) = super::execute(&format!("{SOURCE}\n7=7\n"));
    let unrelated = match result.statement_results.pop().unwrap() {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) => proof.verify_result,
        _ => panic!("actual unrelated identity result"),
    };
    strategy(&mut result).proof_of_requirement_facts[0] = unrelated;
    super::phase2_rejected(
        &result,
        &compiler,
        "unrelated_child",
        &["ArithmeticCongruence/RequirementSubject"],
    );
}

#[test]
fn arithmetic_congruence_strategy_rejects_a_wrong_parent_constructor() {
    let (mut result, compiler) = super::execute(&format!("{SOURCE}\n1=1\n"));
    let last = result.statement_results.pop().unwrap();
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(mut identity)) = last else {
        panic!("actual numeric identity result")
    };
    std::mem::swap(
        &mut original(&mut result).searched_proof,
        &mut super::equality_proof_mut(&mut identity.verify_result).searched_proof,
    );
    result.statement_results.remove(1);
    result
        .statement_results
        .push(ExecStmtResult::Fact(ExecFactStmtResult::Success(identity)));
    super::phase2_rejected(
        &result,
        &compiler,
        "wrong_constructor",
        &["ArithmeticCongruence/Constructor"],
    );
}
