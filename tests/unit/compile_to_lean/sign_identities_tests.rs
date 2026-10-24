use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave7::SignOfProductBuiltinRuleProof;
use crate::prelude::*;

#[test]
fn sign_identity_examples_replay_functions_and_named_proofs() {
    for source in [
        include_str!("../../../lean/examples/sign_product/statement.lit"),
        include_str!("../../../lean/examples/sign_negation/statement.lit"),
        include_str!("../../../lean/examples/signed_magnitude/statement.lit"),
        include_str!("../../../lean/examples/direction_magnitude_functions/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "sign_identities").unwrap();
        assert_eq!(
            output,
            compiler.compile_run(&run, "sign_identities").unwrap()
        );
    }
}

#[test]
fn sign_negation_replays_all_producer_spellings_and_orientations() {
    let forms = [
        "-@",
        "0 - @",
        "(-1) * @",
        "@ * (-1)",
        "(0 - 1) * @",
        "@ * (0 - 1)",
    ];
    for first in forms {
        for second in forms {
            for reverse in [false, true] {
                let left = format!("sign({})", first.replace('@', "x"));
                let right = second.replace('@', "sign(x)");
                let equality = if reverse {
                    format!("{right} = {left}")
                } else {
                    format!("{left} = {right}")
                };
                let (mut run, compiler) = super::execute(&format!("forall x R:\n    {equality}\n"));
                let universal = super::forall_proof_mut(&mut run.statement_results[0]);
                let p =
                    super::equality_proof_mut(&mut universal.proved_then_facts[0].verify_result);
                assert!(
                    matches!(
                        p.searched_proof,
                        EqualFactSearchedProof::ByBuiltinRule(
                            EqualitySearchProofByBuiltinRule::SignOfNegation(_)
                        )
                    ),
                    "{equality}"
                );
                let output = compiler.compile_run(&run, "sign_negation").unwrap();
                assert!(output.contains("Litex.signNegation"));
            }
        }
    }
}

#[test]
fn sign_product_replays_argument_permutations_and_equality_orientations() {
    for input in ["x * y", "y * x"] {
        for output in ["sign(x) * sign(y)", "sign(y) * sign(x)"] {
            for reverse in [false, true] {
                let equality = if reverse {
                    format!("{output} = sign({input})")
                } else {
                    format!("sign({input}) = {output}")
                };
                let (mut run, compiler) =
                    super::execute(&format!("forall x R, y R:\n    {equality}\n"));
                let universal = super::forall_proof_mut(&mut run.statement_results[0]);
                let p =
                    super::equality_proof_mut(&mut universal.proved_then_facts[0].verify_result);
                assert!(
                    matches!(
                        p.searched_proof,
                        EqualFactSearchedProof::ByBuiltinRule(
                            EqualitySearchProofByBuiltinRule::SignOfProduct(_)
                        )
                    ),
                    "{equality}"
                );
                assert!(compiler
                    .compile_run(&run, "sign_product")
                    .unwrap()
                    .contains("Litex.signProduct"));
            }
        }
    }
}

#[test]
fn sign_magnitude_replays_both_identities_and_all_orientations() {
    for (other, target, abs_target) in [("abs(x)", "x", false), ("x", "abs(x)", true)] {
        for first in [false, true] {
            for reverse in [false, true] {
                let product = if first {
                    format!("sign(x) * {other}")
                } else {
                    format!("{other} * sign(x)")
                };
                let equality = if reverse {
                    format!("{target} = {product}")
                } else {
                    format!("{product} = {target}")
                };
                let (mut run, compiler) = super::execute(&format!("forall x R:\n    {equality}\n"));
                let universal = super::forall_proof_mut(&mut run.statement_results[0]);
                let p =
                    super::equality_proof_mut(&mut universal.proved_then_facts[0].verify_result);
                let selected = match &p.searched_proof {
                    EqualFactSearchedProof::ByBuiltinRule(
                        EqualitySearchProofByBuiltinRule::AbsEqualsSignTimesArg(_),
                    ) => abs_target,
                    EqualFactSearchedProof::ByBuiltinRule(
                        EqualitySearchProofByBuiltinRule::SignTimesAbsEqualsArg(_),
                    ) => !abs_target,
                    _ => false,
                };
                assert!(selected, "{equality}");
                compiler.compile_run(&run, "sign_magnitude").unwrap();
            }
        }
    }
}

#[test]
fn sign_identities_reject_changed_subjects_and_mismatched_selected_rules() {
    for source in [
        "sign(-x) = -sign(x)",
        "sign(x) * abs(x) = x",
        "abs(x) = sign(x) * x",
    ] {
        for wrong_rule in [false, true] {
            let (mut run, compiler) = super::execute(&format!("forall x R:\n    {source}\n"));
            let universal = super::forall_proof_mut(&mut run.statement_results[0]);
            let p = super::equality_proof_mut(&mut universal.proved_then_facts[0].verify_result);
            if wrong_rule {
                p.searched_proof = EqualFactSearchedProof::ByBuiltinRule(
                    EqualitySearchProofByBuiltinRule::SignOfProduct(
                        SignOfProductBuiltinRuleProof {},
                    ),
                );
            } else {
                p.fact.right = Obj::Literal(Literal::Number(Number::new("42".into())));
            }
            assert!(compiler.compile_run(&run, "forged_sign_identity").is_err());
        }
    }
}

#[test]
fn sign_identities_require_the_original_real_domain_wd() {
    for missing in [false, true] {
        let (mut run, compiler) = super::execute("forall x R:\n    sign(-x) = -sign(x)\n");
        let universal = super::forall_proof_mut(&mut run.statement_results[0]);
        let p = super::equality_proof_mut(&mut universal.proved_then_facts[0].verify_result);
        let ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::ArithmeticOperator(
                    ArithmeticOperatorObjWellDefinedProofByDef::Sign(wd),
                ),
            ..
        } = &mut p.well_defined_proof.left
        else {
            panic!("original sign construction")
        };
        if missing {
            wd.requirement_fact_verified.clear();
        } else {
            let fact = super::atomic_proof_mut(&mut wd.requirement_fact_verified[0]);
            let AtomicFact::InFact(member) = &mut fact.fact else {
                panic!("original real domain")
            };
            member.set = Obj::StandardSet(StandardSet::C);
        }
        assert!(compiler.compile_run(&run, "forged_sign_domain").is_err());
    }
}

#[test]
fn sign_identity_false_sources_still_reject() {
    for source in [
        "forall x C:\n    sign(-x) = -sign(x)\n",
        "forall x R:\n    sign(-x) = sign(x)\n",
        "forall x R:\n    sign(x) * abs(x) = abs(x)\n",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime = Runtime::new(command);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success, "{source}");
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "false_sign_identity")
            .is_err());
    }
}
