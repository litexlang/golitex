use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_builtin_strategy_result::ComplexWithNonzeroPremisesStrategySingleStep;

const SOURCE: &str =
    include_str!("../../../lean/examples/complex_guarded_normalization/statement.lit");

fn selected(result: &mut RunLitexCodeResult) -> &mut ComplexWithNonzeroPremisesStrategySingleStep {
    selected_at(result, 0)
}

fn selected_at(
    result: &mut RunLitexCodeResult,
    index: usize,
) -> &mut ComplexWithNonzeroPremisesStrategySingleStep {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(fact)) =
        &mut result.statement_results[index]
    else {
        panic!("forall fact")
    };
    let VerifyFactResult::ForallFact(forall) = &mut fact.verify_result else {
        panic!("forall verification")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(forall)) =
        forall.as_mut()
    else {
        panic!("local forall")
    };
    let proof = super::equality_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByBuiltinStrategy(
        EqualitySearchProofByBuiltinStrategy::ComplexWithNonzeroPremises(proof),
    ) = &mut proof.searched_proof
    else {
        panic!("the real source must select ComplexWithNonzeroPremises")
    };
    proof
}

#[test]
fn complex_strategy_replays_whole_product_guards_in_original_order() {
    let (mut result, compiler) = super::execute(SOURCE);
    let proof = selected_at(&mut result, 1);
    assert_eq!(proof.requirement_facts.len(), 2);
    assert_eq!(proof.proof_of_requirement_facts.len(), 2);
    assert!(
        matches!(&proof.requirement_facts[0], Fact::AtomicFact(AtomicFact::NotEqualFact(p))
        if matches!(p.left, Obj::ArithmeticOperator(ArithmeticOperator::Mul(_))))
    );
    let output = super::compile_run(&result, &compiler, "complex_product_guard").unwrap();
    assert!(output.contains("mul_ne_zero_iff.mp _litex_nz_0"));
    selected_at(&mut result, 1).requirement_facts.swap(0, 1);
    super::phase2_rejected(
        &result,
        &compiler,
        "swapped whole guards",
        &["Arithmetic/NonzeroSubject"],
    );
}

#[test]
fn complex_strategy_replays_actual_nonzero_evidence() {
    let (mut result, compiler) = super::execute(SOURCE);
    let proof = selected(&mut result);
    assert_eq!(proof.requirement_facts.len(), 1);
    assert_eq!(proof.proof_of_requirement_facts.len(), 1);
    let output = super::compile_run(&result, &compiler, "guarded_complex").unwrap();
    assert!(output.contains("litex_normalize_guarded_complex"));
    assert!(output.contains("nativeNonzeroOfDenote"));
    assert!(!output.contains("sorry") && !output.contains("admit"));
}

#[test]
fn complex_strategy_rejects_deleted_guard_and_mismatched_exact_id() {
    for change in ["missing_fact", "missing_proof", "wrong_id"] {
        let (mut result, compiler) = super::execute(SOURCE);
        let proof = selected(&mut result);
        match change {
            "missing_fact" => proof.requirement_facts.clear(),
            "missing_proof" => proof.proof_of_requirement_facts.clear(),
            "wrong_id" => {
                let Fact::AtomicFact(AtomicFact::NotEqualFact(f)) = &mut proof.requirement_facts[0]
                else {
                    unreachable!()
                };
                f.fact_id = FactId::new(u64::MAX);
            }
            _ => unreachable!(),
        }
        super::phase2_rejected(&result, &compiler, change, &["ComplexNormalization/"]);
    }
}

#[test]
fn complex_strategy_preserves_the_original_nonzero_citation() {
    let (mut result, compiler) = super::execute(SOURCE);
    let proof = super::atomic_proof_mut(&mut selected(&mut result).proof_of_requirement_facts[0]);
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) = &mut proof.searched_proof
    else {
        panic!("the real denominator guard cites its original premise")
    };
    cite.cite_fact_id = FactId::new(u64::MAX);
    super::phase2_rejected(&result, &compiler, "wrong guard producer", &["FactId/"]);
}

#[test]
fn complex_strategy_rejects_missing_source_guard() {
    let source = SOURCE.replace("    z != 0\n", "");
    let command =
        parse_launch_command(&["-strict".to_string(), "-e".to_string(), source.clone()]).unwrap();
    let mut runtime =
        Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
    assert!(!runtime.run_litex_code(&source).unwrap().success);
}
