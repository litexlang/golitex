use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_builtin_strategy_result::ModCongruenceStrategySingleStep;
use crate::prelude::*;

const SOURCE: &str = r#"# Replay modulus identity followed by the two original residue equalities.
forall a, b, c, d, modulus Z:
    modulus != 0
    a % modulus = c % modulus
    b % modulus = d % modulus
    =>:
        (a + b) % modulus = (c + d) % modulus
        (a - b) % modulus = (c - d) % modulus
        (a * b) % modulus = (c * d) % modulus
"#;
const DISTINCT: &str = r#"# Keep the checked transport between the two original modulus objects.
forall a, b, c, d, m, n Z:
    m != 0
    m = n
    a % m = c % n
    b % m = d % n
    =>:
        (a + b) % m = (c + d) % n
        (a - b) % m = (c - d) % n
        (a * b) % m = (c * d) % n
"#;
const NESTED: &str = r#"# Some original operands already have their residue wrappers.
forall a, b, c, d, m Z:
    m != 0
    a % m = c % m
    b % m = d % m
    =>:
        ((a % m) + b) % m = (c + (d % m)) % m
        (a - (b % m)) % m = ((c % m) - d) % m
        ((a % m) * (b % m)) % m = (c * d) % m
        ((a % m) + (b % m)) % m = ((c % m) + (d % m)) % m
"#;
const NEGATIVE: &str = r#"# Modulo congruence retains signed integer moduli.
forall a, b, c, d Z:
    a % (-3) = c % (-3)
    b % (-3) = d % (-3)
    =>:
        (a + b) % (-3) = (c + d) % (-3)
        (a - b) % (-3) = (c - d) % (-3)
        (a * b) % (-3) = (c * d) % (-3)
"#;

fn original(result: &mut RunLitexCodeResult, index: usize) -> &mut VerifyEqualitySuccess {
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
        panic!("actual introduced forall")
    };
    super::equality_proof_mut(&mut forall.proved_then_facts[index].verify_result)
}

fn selected(result: &mut RunLitexCodeResult, index: usize) -> &mut ModCongruenceStrategySingleStep {
    let EqualFactSearchedProof::ByBuiltinStrategy(
        EqualitySearchProofByBuiltinStrategy::ModCongruence(proof),
    ) = &mut original(result, index).searched_proof
    else {
        panic!("the real source must select ModCongruence at conclusion {index}")
    };
    proof
}

fn compile_actual(source: &str) -> String {
    let (mut result, compiler) = super::execute(source);
    for index in 0..3 {
        let proof = selected(&mut result, index);
        assert_eq!(proof.requirement_facts.len(), 3);
        assert_eq!(proof.proof_of_requirement_facts.len(), 3);
    }
    let output = super::compile_run(&result, &compiler, "mod_congruence").unwrap();
    for law in [
        "integerModAddCongr",
        "integerModSubCongr",
        "integerModMulCongr",
    ] {
        assert!(output.contains(law));
    }
    assert!(!output.contains("sorry") && !output.contains("admit"));
    output
}

#[test]
fn mod_congruence_replays_all_three_actual_operations() {
    compile_actual(SOURCE);
}

#[test]
fn mod_congruence_keeps_the_original_modulus_transport() {
    compile_actual(DISTINCT);
}

#[test]
fn mod_congruence_preserves_elided_residue_wrappers() {
    let output = compile_actual(NESTED);
    assert!(output.contains("integerModValueIdempotent"));
}

#[test]
fn already_reduced_factors_keep_their_earlier_selected_route() {
    let (mut result, compiler) = super::execute(NESTED);
    assert!(!matches!(
        original(&mut result, 3).searched_proof,
        EqualFactSearchedProof::ByBuiltinStrategy(
            EqualitySearchProofByBuiltinStrategy::ModCongruence(_)
        )
    ));
    super::compile_run(&result, &compiler, "already_reduced_factors").unwrap();
}

#[test]
fn mod_congruence_retains_negative_integer_moduli() {
    compile_actual(NEGATIVE);
}

#[test]
fn mod_congruence_rejects_missing_extra_swapped_and_wrong_id_evidence() {
    for change in [
        "missing_fact",
        "missing_proof",
        "extra_fact",
        "swap_facts",
        "swap_proofs",
        "wrong_id",
    ] {
        let (mut result, compiler) = super::execute(SOURCE);
        let proof = selected(&mut result, 0);
        match change {
            "missing_fact" => {
                proof.requirement_facts.pop();
            }
            "missing_proof" => {
                proof.proof_of_requirement_facts.pop();
            }
            "extra_fact" => proof
                .requirement_facts
                .push(proof.requirement_facts[0].clone()),
            "swap_facts" => proof.requirement_facts.swap(1, 2),
            "swap_proofs" => proof.proof_of_requirement_facts.swap(1, 2),
            "wrong_id" => {
                let Fact::AtomicFact(AtomicFact::EqualFact(equal)) =
                    &mut proof.requirement_facts[1]
                else {
                    unreachable!()
                };
                equal.fact_id = FactId::new(u64::MAX);
            }
            _ => unreachable!(),
        }
        super::phase2_rejected(&result, &compiler, change, &["ModCongruence/"]);
    }
}

#[test]
fn mod_congruence_rejects_reordered_valid_proofs_of_other_subjects() {
    for pair in [(0, 1), (1, 2)] {
        let (mut result, compiler) = super::execute(DISTINCT);
        let proof = selected(&mut result, 0);
        proof.requirement_facts.swap(pair.0, pair.1);
        proof.proof_of_requirement_facts.swap(pair.0, pair.1);
        super::phase2_rejected(
            &result,
            &compiler,
            "reordered subjects",
            &["ModCongruence/"],
        );
    }
}

#[test]
fn mod_congruence_does_not_certify_another_conclusion() {
    let (mut result, compiler) = super::execute(SOURCE);
    selected(&mut result, 0);
    let proof = original(&mut result, 0);
    proof.fact.right = proof.fact.left.clone();
    assert!(super::compile_run(&result, &compiler, "changed_mod_conclusion").is_err());
}

#[test]
fn mod_congruence_cannot_borrow_a_missing_or_future_modulus_proof() {
    for future in [false, true] {
        let source = format!("{DISTINCT}        m = n\n");
        let (mut result, compiler) = super::execute(&source);
        let unavailable = if future {
            original(&mut result, 3).fact.fact_id
        } else {
            FactId::new(u64::MAX)
        };
        let proof = selected(&mut result, 0);
        let path = super::equality_path_mut(&mut proof.proof_of_requirement_facts[0]);
        assert_eq!(path.path.len(), 1);
        path.path[0].2 = unavailable;
        let error = super::compile_run(&result, &compiler, "unavailable_modulus_proof")
            .expect_err("an unavailable citation cannot supply modulus identity");
        assert_eq!(
            error.route,
            if future {
                "FactId/Producer"
            } else {
                "FactId/Resolution"
            },
            "{error:?}"
        );
        if future {
            assert!(error.message.contains("no prior producer"), "{error:?}");
        }
    }
}

#[test]
fn mod_congruence_requires_the_source_guards_and_both_residues() {
    for omitted in [
        "    modulus != 0\n",
        "    a % modulus = c % modulus\n",
        "    b % modulus = d % modulus\n",
    ] {
        let source = SOURCE.replace(omitted, "");
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.clone()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        assert!(!runtime.run_litex_code(&source).unwrap().success);
    }
}
