use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_builtin_strategy_result::CosZeroIntegerOffsetStrategySingleStep;
use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_equal::NotEqualFactSearchProofByBuiltinRule;

const SOURCE: &str = r#"# Replay the actual integer offset under the original real parameter.
forall angle R:
    (angle - pi / 2) / pi $in Z
    =>:
        cos(angle) = 0
"#;
const REVERSED: &str = r#"# Equality to a source integer supplies the reversed cosine-zero conclusion.
forall angle R, offset Z:
    (angle - pi / 2) / pi = offset
    =>:
        0 = cos(angle)
"#;

fn original(result: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        &mut result.statement_results[0]
    else {
        panic!("verified source forall")
    };
    let VerifyFactResult::ForallFact(forall) = &mut statement.verify_result else {
        panic!("source forall result")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(forall)) =
        forall.as_mut()
    else {
        panic!("actual local introduction")
    };
    super::equality_proof_mut(&mut forall.proved_then_facts[0].verify_result)
}

fn selected(result: &mut RunLitexCodeResult) -> &mut CosZeroIntegerOffsetStrategySingleStep {
    let EqualFactSearchedProof::ByBuiltinStrategy(
        EqualitySearchProofByBuiltinStrategy::CosZeroIntegerOffset(proof),
    ) = &mut original(result).searched_proof
    else {
        panic!("real source must select CosZeroIntegerOffset")
    };
    proof
}

#[test]
fn cosine_replays_the_actual_integer_offset_and_reversed_conclusion() {
    for source in [SOURCE, REVERSED] {
        let (mut result, compiler) = super::execute(source);
        let proof = selected(&mut result);
        assert_eq!(proof.requirement_facts.len(), 1);
        assert_eq!(proof.proof_of_requirement_facts.len(), 1);
        let output = super::compile_run(&result, &compiler, "cos_offset").unwrap();
        assert!(output.contains("M.integer_members"));
        assert!(output.contains("Real.cos_eq_zero_iff.mpr"));
        assert!(!output.contains("sorry") && !output.contains("admit"));
    }
}

#[test]
fn cosine_rejects_missing_and_mismatched_integer_evidence() {
    for change in [
        "missing_fact",
        "missing_proof",
        "wrong_id",
        "wrong_carrier",
        "wrong_offset",
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
            "wrong_id" | "wrong_carrier" | "wrong_offset" => {
                let Fact::AtomicFact(AtomicFact::InFact(member)) = &mut proof.requirement_facts[0]
                else {
                    unreachable!()
                };
                match change {
                    "wrong_id" => member.fact_id = FactId::new(u64::MAX),
                    "wrong_carrier" => member.set = Obj::StandardSet(StandardSet::R),
                    "wrong_offset" => member.element = member.set.clone(),
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        }
        super::phase2_rejected(&result, &compiler, change, &["CosIntegerOffset/"]);
    }
}

#[test]
fn cosine_rejects_an_unrelated_conclusion() {
    let (mut result, compiler) = super::execute(SOURCE);
    selected(&mut result);
    original(&mut result).fact.right = Obj::StandardSet(StandardSet::R);
    assert!(super::compile_run(&result, &compiler, "changed_cosine").is_err());
}

#[test]
fn cosine_does_not_invent_integer_membership() {
    for source in [
        "forall angle R:\n    cos(angle) = 0\n",
        "forall angle R:\n    (angle - pi / 2) / pi $in R\n    =>:\n        cos(angle) = 0\n",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        assert!(!runtime.run_litex_code(source).unwrap().success);
    }
}

#[test]
fn pi_nonzero_replays_the_actual_rule_in_both_orientations() {
    for source in ["pi != 0", "0 != pi"] {
        let (mut result, compiler) = super::execute(source);
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
            &mut result.statement_results[0]
        else {
            panic!("verified pi inequality")
        };
        let proof = super::atomic_proof_mut(&mut statement.verify_result);
        assert!(matches!(
            proof.searched_proof,
            AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(
                    NotEqualFactSearchProofByBuiltinRule::PiNonzero(_)
                )
            )
        ));
        let output = super::compile_run(&result, &compiler, "pi_nonzero").unwrap();
        assert!(output.contains("Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)"));
    }
}

#[test]
fn pi_nonzero_does_not_certify_another_constant() {
    let (mut result, compiler) = super::execute("pi != 0");
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        &mut result.statement_results[0]
    else {
        unreachable!()
    };
    let proof = super::atomic_proof_mut(&mut statement.verify_result);
    let AtomicFact::NotEqualFact(fact) = &mut proof.fact else {
        unreachable!()
    };
    fact.left = fact.right.clone();
    assert!(super::compile_run(&result, &compiler, "changed_pi").is_err());
}
