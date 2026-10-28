use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::IntegerOperatorObjWellDefinedProofByDef;
use crate::prelude::*;

#[test]
fn integer_division_examples_replay_original_results() {
    for source in [
        include_str!("../../../lean/examples/signed_integer_division/statement.lit"),
        include_str!("../../../lean/examples/quotient_remainder_decomposition/statement.lit"),
        include_str!("../../../lean/examples/integer_division_functions/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "integer_division").unwrap();
        assert!(output.contains("Litex.quot"));
        assert_eq!(
            output,
            compiler.compile_run(&run, "integer_division").unwrap()
        );
    }
}

#[test]
fn integer_division_decomposition_preserves_product_order_and_equality_orientation() {
    for first in [true, false] {
        for reversed in [true, false] {
            let product = if first {
                "quot(a, d) * d"
            } else {
                "d * quot(a, d)"
            };
            let sum = format!("{product} + a % d");
            let equality = if reversed {
                format!("{sum} = a")
            } else {
                format!("a = {sum}")
            };
            let (run, compiler) = super::execute(&format!("forall a Z, d N+:\n    {equality}\n"));
            let output = compiler.compile_run(&run, "decomposition").unwrap();
            assert!(output.contains("Litex.quotDecomposition"));
        }
    }
}

#[test]
fn integer_division_rejects_decomposition_rule_on_another_shape() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave8::QuotEuclideanDecompositionBuiltinRuleProof;
    let (mut run, compiler) = super::execute("forall a Z:\n    a = a\n");
    let universal = super::forall_proof_mut(&mut run.statement_results[0]);
    let p = super::equality_proof_mut(&mut universal.proved_then_facts[0].verify_result);
    p.searched_proof = EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::QuotEuclideanDecomposition(
            QuotEuclideanDecompositionBuiltinRuleProof {},
        ),
    );
    assert_eq!(
        compiler
            .compile_run(&run, "bad_decomposition")
            .unwrap_err()
            .route,
        "Quot/DecompositionSubject"
    );
}

#[test]
fn integer_division_wd_rejects_missing_reordered_and_wrong_domain_evidence() {
    for expression in ["quot(a, d)", "a % d"] {
        for mutation in 0..3 {
            let (mut run, compiler) =
                super::execute(&format!("have a Z\nhave d N+\n$is_set({expression})\n"));
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
                panic!("integer WD");
            };
            let (children, requirements) = match p {
                IntegerOperatorObjWellDefinedProofByDef::Mod(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                IntegerOperatorObjWellDefinedProofByDef::Quot(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                _ => panic!("selected integer operation"),
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
                        panic!("integer membership");
                    };
                    member.set = Obj::StandardSet(StandardSet::R);
                }
            }
            assert!(compiler.compile_run(&run, "bad_integer_wd").is_err());
        }
    }
}

#[test]
fn integer_division_self_identity_requires_original_positive_domain() {
    for missing in [true, false] {
        let (mut run, compiler) = super::execute("forall n N+:\n    quot(n, n) = 1\n");
        let universal = super::forall_proof_mut(&mut run.statement_results[0]);
        let p = super::equality_proof_mut(&mut universal.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::QuotSelfOne(p)) =
            &mut p.searched_proof
        else {
            panic!("quot self");
        };
        if missing {
            p.proof_of_requirement_facts.clear();
        } else {
            let AtomicFact::InFact(member) =
                &mut super::atomic_proof_mut(&mut p.proof_of_requirement_facts[0]).fact
            else {
                panic!("positive domain");
            };
            member.set = Obj::StandardSet(StandardSet::Z);
        }
        assert_eq!(
            compiler
                .compile_run(&run, "bad_quot_self")
                .unwrap_err()
                .route,
            "Quot/IdentityPremise"
        );
    }
}

#[test]
fn integer_division_bounds_reject_changed_original_premises() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{less::LessFactSearchProofByBuiltinRule as Lt, less_equal::LessEqualFactSearchProofByBuiltinRule as Le};
    for goal in ["0 <= a % d", "a % d < d"] {
        let (mut run, compiler) = super::execute(&format!("forall a Z, d N+:\n    {goal}\n"));
        let universal = super::forall_proof_mut(&mut run.statement_results[0]);
        let p = super::atomic_proof_mut(&mut universal.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(rule) = &mut p.searched_proof
        else {
            panic!("mod bound");
        };
        let domain = match rule {
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
                Lt::ModRemainderStrictUpperBound(p),
            ) => &mut p.modulus_in_n_pos_proof,
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
                Le::ModRemainderNonnegative(p),
            ) => &mut p.modulus_in_n_pos_proof,
            _ => panic!("selected mod bound"),
        };
        let AtomicFact::InFact(member) = &mut super::atomic_proof_mut(domain).fact else {
            panic!("positive modulus");
        };
        member.set = Obj::StandardSet(StandardSet::Z);
        assert_eq!(
            compiler
                .compile_run(&run, "bad_mod_bound")
                .unwrap_err()
                .route,
            "Mod/BoundPremises"
        );
    }
}

#[test]
fn integer_division_reuses_children_and_checks_closed_certificates() {
    for expression in ["quot(a, d)", "a % d"] {
        let (run, compiler) = super::execute(&format!(
            "have a Z\nhave d N+\n$is_set(({expression}) + 1)\n$is_set({expression})\n"
        ));
        let output = compiler.compile_run(&run, "integer_reuse").unwrap();
        let name = if expression.starts_with("quot") {
            "quot"
        } else {
            "mod"
        };
        assert_eq!(output.matches(&format!("Litex.{name} ")).count(), 1);
    }
    let (mut run, compiler) = super::execute("(-7) % (-3) = 2\n");
    let p = super::equality_proof_mut(
        &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
    );
    let EqualFactSearchedProof::ByClosedCalculation(p) = &mut p.searched_proof else {
        panic!("closed remainder");
    };
    let ClosedValuePair::Decimal { left, .. } = &mut p.values else {
        panic!("integer result");
    };
    *left = "-1".into();
    assert_eq!(
        compiler
            .compile_run(&run, "bad_mod_value")
            .unwrap_err()
            .route,
        "ClosedEquality/Values"
    );
}

#[test]
fn integer_division_rejects_zero_noninteger_and_wrong_sign_domains() {
    for source in [
        "$is_set(1 % 0)",
        "$is_set(quot(1, 0))",
        "$is_set(quot(1, -2))",
        "$is_set((1 / 2) % 3)",
        "quot(-7, 3) = -2",
        "(-7) % (-3) = -1",
        "have fn q(n Z, d N+) Z = quot(n, d)\nq(4, 0) = 0",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success, "{source}");
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_integer")
            .is_err());
    }
}

#[test]
fn integer_division_congruence_requires_each_original_argument_proof() {
    for missing in [true, false] {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/integer_division_functions/statement.lit"
        ));
        let equality = super::equality_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[8]).verify_result,
        );
        let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &mut equality.searched_proof else {
            panic!("original quotient congruence");
        };
        if missing {
            p.corresponding_arg_equal_proofs.pop();
        } else {
            p.corresponding_arg_equal_proofs.swap(0, 1);
        }
        assert_eq!(
            compiler
                .compile_run(&run, "bad_quot_congruence")
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
