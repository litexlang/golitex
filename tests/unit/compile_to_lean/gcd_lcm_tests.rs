use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::IntegerOperatorObjWellDefinedProofByDef as IntegerWd;
use crate::prelude::*;

#[test]
fn gcd_lcm_selected_rules_reject_an_unrelated_subject() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::{
        by_elementary_definitions::GcdEuclideanStepProof,
        by_equality_identities_wave8::LcmGcdProductAbsBuiltinRuleProof,
    };
    for product in [true, false] {
        let (mut run, compiler) = super::execute("forall a Z:\n    a = a\n");
        let universal = super::forall_proof_mut(&mut run.statement_results[0]);
        let equality = super::equality_proof_mut(&mut universal.proved_then_facts[0].verify_result);
        equality.searched_proof = EqualFactSearchedProof::ByBuiltinRule(if product {
            EqualitySearchProofByBuiltinRule::LcmGcdProductAbs(LcmGcdProductAbsBuiltinRuleProof {})
        } else {
            EqualitySearchProofByBuiltinRule::GcdEuclideanStep(GcdEuclideanStepProof {})
        });
        assert_eq!(
            compiler.compile_run(&run, "wrong_rule").unwrap_err().route,
            if product {
                "GcdLcm/ProductSubject"
            } else {
                "Gcd/EuclideanSubject"
            }
        );
    }
}

#[test]
fn gcd_congruence_requires_each_original_argument_proof() {
    for missing in [true, false] {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/gcd_lcm_functions/statement.lit"
        ));
        let equality = super::equality_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[8]).verify_result,
        );
        let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &mut equality.searched_proof else {
            panic!("original gcd congruence")
        };
        if missing {
            p.corresponding_arg_equal_proofs.pop();
        } else {
            p.corresponding_arg_equal_proofs.swap(0, 1);
        }
        assert_eq!(
            compiler
                .compile_run(&run, "bad_gcd_congruence")
                .unwrap_err()
                .route,
            if missing {
                "ArithmeticCongruence/Children"
            } else {
                "ArithmeticCongruence/ChildSubject"
            }
        );
    }
}

#[test]
fn gcd_lcm_examples_replay_original_results_deterministically() {
    for source in [
        include_str!("../../../lean/examples/gcd_lcm_values/statement.lit"),
        include_str!("../../../lean/examples/gcd_lcm_identities/statement.lit"),
        include_str!("../../../lean/examples/gcd_euclidean_step/statement.lit"),
        include_str!("../../../lean/examples/gcd_lcm_functions/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "gcd_lcm").unwrap();
        assert!(output.contains("Litex.gcd"));
        assert_eq!(output, compiler.compile_run(&run, "gcd_lcm").unwrap());
    }
}

#[test]
fn gcd_lcm_product_preserves_factor_order_and_equality_orientation() {
    for first in [true, false] {
        for reversed_arguments in [true, false] {
            for reversed_equality in [true, false] {
                let product = if first {
                    "gcd(a, b) * lcm(a, b)"
                } else {
                    "lcm(a, b) * gcd(a, b)"
                };
                let target = if reversed_arguments {
                    "abs(b * a)"
                } else {
                    "abs(a * b)"
                };
                let equality = if reversed_equality {
                    format!("{target} = {product}")
                } else {
                    format!("{product} = {target}")
                };
                let (run, compiler) = super::execute(&format!(
                    "forall a, b Z:\n    a != 0 or b != 0\n    =>:\n        {equality}\n"
                ));
                let output = compiler.compile_run(&run, "product").unwrap();
                assert!(output.contains("Litex.gcdLcmProduct"));
            }
        }
    }
}

#[test]
fn gcd_lcm_wd_rejects_missing_reordered_and_wrong_domain_evidence() {
    for name in ["gcd", "lcm"] {
        for mutation in 0..3 {
            let (mut run, compiler) =
                super::execute(&format!("have a Z\nhave b N+\n$is_set({name}(a, b))\n"));
            let p = super::atomic_proof_mut(
                &mut super::fact_statement_mut(&mut run.statement_results[2]).verify_result,
            );
            let DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::IntegerOperator(p),
                ..
            } = (&mut p
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .well_defined_of_each_parameter[0])
                .as_detailed_mut()
                .unwrap()
            else {
                panic!("integer WD")
            };
            let (children, requirements) = match p {
                IntegerWd::Gcd(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                IntegerWd::Lcm(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                _ => panic!("gcd/lcm WD"),
            };
            match mutation {
                0 => {
                    requirements.pop();
                }
                1 => children.swap(0, 1),
                _ => {
                    let AtomicFact::InFact(member) =
                        &mut super::atomic_proof_mut(&mut requirements[0]).fact
                    else {
                        panic!("integer membership")
                    };
                    member.set = Obj::StandardSet(StandardSet::R);
                }
            }
            assert!(compiler.compile_run(&run, "bad_gcd_lcm_wd").is_err());
        }
    }
}

#[test]
fn gcd_rejects_guard_with_missing_or_duplicated_nonzero_branch() {
    use crate::execute::execute_fact_stmt::verify_or_fact::VerifyOrFactResult;
    for missing in [true, false] {
        let (mut run, compiler) = super::execute(
            "forall a, b Z:\n    a != 0 or b != 0\n    =>:\n        $is_set(gcd(a, b))\n",
        );
        let universal = super::forall_proof_mut(&mut run.statement_results[0]);
        let p = super::atomic_proof_mut(&mut universal.proved_then_facts[0].verify_result);
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::IntegerOperator(IntegerWd::Gcd(p)),
            ..
        } = (&mut p
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .well_defined_of_each_parameter[0])
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("gcd WD")
        };
        let VerifyFactResult::OrFact(guard) = &mut p.requirement_fact_verified[2] else {
            panic!("original Or guard")
        };
        let VerifyOrFactResult::Success(guard) = guard.as_mut() else {
            panic!("successful Or")
        };
        if missing {
            guard.fact.facts.pop();
        } else {
            guard.fact.facts[1] = guard.fact.facts[0].clone();
        }
        assert_eq!(
            compiler.compile_run(&run, "bad_guard").unwrap_err().route,
            "WD/GcdNonzeroPair"
        );
    }
}

#[test]
fn gcd_zero_identity_requires_its_original_nonzero_premise() {
    for expression in ["gcd(a, 0)", "gcd(0, a)"] {
        let (mut run, compiler) = super::execute(&format!(
            "forall a Z:\n    a != 0\n    =>:\n        {expression} = abs(a)\n"
        ));
        let universal = super::forall_proof_mut(&mut run.statement_results[0]);
        let equality = super::equality_proof_mut(&mut universal.proved_then_facts[0].verify_result);
        match &mut equality.searched_proof {
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::GcdRightZeroAbs(p),
            ) => p.proof_of_requirement_facts.clear(),
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::GcdLeftZeroAbs(p),
            ) => p.proof_of_requirement_facts.clear(),
            _ => panic!("original gcd zero rule"),
        }
        assert_eq!(
            compiler
                .compile_run(&run, "missing_nonzero")
                .unwrap_err()
                .route,
            "Gcd/ZeroIdentityPremise"
        );
    }
}

#[test]
fn gcd_modulus_reuses_original_constructor_and_derives_nonzero_from_wd() {
    let (run, compiler) =
        super::execute("have a Z\nhave b N+\n$is_set(gcd(a, b))\n$is_set(a % gcd(a, b))\n");
    let output = compiler.compile_run(&run, "gcd_modulus").unwrap();
    assert_eq!(output.matches("Litex.gcd ").count(), 1);
    assert!(output.contains("Litex.gcdNonzero"));
    assert!(output.contains("Litex.mod "));
}

#[test]
fn gcd_lcm_rejects_zero_pair_noninteger_and_forged_calculation() {
    for source in [
        "$is_set(gcd(0, 0))",
        "$is_set(gcd(1 / 2, 2))",
        "$is_set(lcm(1 / 2, 2))",
        "gcd(-6, 15) = -3",
        "lcm(0, 0) = 1",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success, "{source}");
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_gcd_lcm")
            .is_err());
    }
    let (mut run, compiler) = super::execute("gcd(54, -24) = 6\n");
    let p = super::equality_proof_mut(
        &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
    );
    let EqualFactSearchedProof::ByClosedCalculation(p) = &mut p.searched_proof else {
        panic!("closed gcd")
    };
    let ClosedValuePair::Decimal { left, .. } = &mut p.values else {
        panic!("integer result")
    };
    *left = "-6".into();
    assert_eq!(
        compiler.compile_run(&run, "forged_gcd").unwrap_err().route,
        "ClosedEquality/Values"
    );
}

#[test]
fn gcd_euclidean_step_handles_negative_nonzero_divisors_and_both_orientations() {
    for equality in ["gcd(a, b) = gcd(b, a % b)", "gcd(b, a % b) = gcd(a, b)"] {
        let (run, compiler) = super::execute(&format!(
            "forall a, b Z:\n    b != 0\n    =>:\n        {equality}\n"
        ));
        assert!(compiler
            .compile_run(&run, "euclidean")
            .unwrap()
            .contains("Litex.gcdEuclideanStep"));
    }
}
