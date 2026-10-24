use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{not_in_fact::NotInFactSearchProofByBuiltinRule as NotIn, not_equal::NotEqualFactSearchProofByBuiltinRule as Ne};

#[test]
fn nonmembership_examples_replay_numeric_finite_and_contradiction_routes() {
    for source in [
        include_str!("../../../lean/examples/numeric_nonmembership/statement.lit"),
        include_str!("../../../lean/examples/finite_nonmembership/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "nonmembership").unwrap();
        assert_eq!(output, compiler.compile_run(&run, "nonmembership").unwrap());
    }
}

#[test]
fn closed_nonmembership_rejects_forged_values_and_target_sets() {
    for source in ["not 0 $in Q*", "not 1 / 3 $in Z", "not i $in R"] {
        for target in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let atomic = super::atomic_proof_mut(
                &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
            );
            let AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(
                ClosedAtomicExceptEqualityCalculationProof::NotIn(
                    ClosedMembershipCalculationProof::StandardSet { value, set },
                ),
            ) = &mut atomic.searched_proof
            else {
                panic!("closed nonmember certificate")
            };
            if target {
                *set = StandardSet::C;
            } else {
                *value = ClosedScalarValue::Decimal("42".into());
            }
            assert!(compiler.compile_run(&run, "forged_nonmembership").is_err());
        }
    }
}

#[test]
fn finite_nonmembership_requires_every_ordered_disequality() {
    for fault in 0..3 {
        let (mut run, compiler) = super::execute("not 4 $in {1, 2, 3}");
        let atomic = super::atomic_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
        );
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInFact(
                NotIn::ListSetExhaustiveDisequality(p),
            ),
        ) = &mut atomic.searched_proof
        else {
            panic!("finite exclusion")
        };
        match fault {
            0 => {
                p.disequality_proofs.pop();
            }
            1 => p.disequality_proofs.swap(0, 1),
            _ => {
                let AtomicFact::NotEqualFact(f) =
                    &mut super::atomic_proof_mut(&mut p.disequality_proofs[0]).fact
                else {
                    panic!("disequality child")
                };
                f.left = f.right.clone();
            }
        }
        assert!(compiler
            .compile_run(&run, "forged_finite_exclusion")
            .is_err());
    }
}

#[test]
fn membership_contradiction_checks_both_children_and_common_set() {
    for change_set in [false, true] {
        let (mut run, compiler) = super::execute(
            "forall A set, x R, y R:\n    x $in A\n    not y $in A\n    =>:\n        x != y\n",
        );
        let body = super::forall_proof_mut(&mut run.statement_results[0]);
        let atomic = super::atomic_proof_mut(&mut body.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(
                Ne::MembershipContradiction(p),
            ),
        ) = &mut atomic.searched_proof
        else {
            panic!("membership contradiction")
        };
        let AtomicFact::NotInFact(f) = &mut super::atomic_proof_mut(&mut p.not_in_proof).fact
        else {
            panic!("nonmembership child")
        };
        if change_set {
            f.set = Obj::StandardSet(StandardSet::R);
        } else {
            f.element = Obj::Literal(Literal::Number(Number {
                normalized_value: "0".into(),
            }));
        }
        assert!(compiler.compile_run(&run, "forged_contradiction").is_err());
    }
}

#[test]
fn builtin_nonmembership_keeps_its_actual_decimal_certificate() {
    for corrupt in [false, true] {
        let (mut run, mut compiler) = super::execute("not 1.5 $in Z\n");
        let atomic = super::atomic_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
        );
        let AtomicFact::NotInFact(fact) = &atomic.fact else {
            panic!("nonmembership")
        };
        let mut selected = compiler
            .runtime
            .search_not_in_fact_proof_by_builtin_rule(fact, VerifyState::top_level())
            .unwrap()
            .unwrap();
        let NotIn::ClosedNumericNonMembership(p) = &mut selected else {
            panic!("actual builtin numeric calculation")
        };
        if corrupt {
            p.normal = "2".into();
        }
        atomic.searched_proof = AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInFact(selected),
        );
        let output = compiler.compile_run(&run, "builtin_nonmembership");
        if corrupt {
            assert!(output.is_err());
        } else {
            let output = output.unwrap();
            if let Some(directory) = std::env::var_os("LITEX_LEAN_PHASE2_OUTPUT_DIR") {
                std::fs::write(
                    std::path::Path::new(&directory).join("builtin_nonmembership.lean"),
                    output,
                )
                .unwrap();
            }
        }
    }
}

#[test]
fn false_nonmembership_still_rejects_at_source() {
    for source in [
        "not 1 $in N",
        "not 1.5 $in Q",
        "not i $in C",
        "not 0 $in {0, 1}",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime = Runtime::new(command);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success, "{source}");
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_exclusion")
            .is_err());
    }
}
