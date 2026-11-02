use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::VerifyEqualitySuccess;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_exponential_logarithm_identities::ExponentialLogarithmIdentityProof as Rule;
use crate::prelude::*;

const CASES: [(&str, &str, &str); 7] = [
    (
        include_str!("../../../lean/examples/exponential_difference/statement.lit"),
        "ExpDifference",
        "exponentialDifferenceValue",
    ),
    (
        include_str!("../../../lean/examples/logarithm_product/statement.lit"),
        "LnProduct",
        "logarithmProductValue",
    ),
    (
        include_str!("../../../lean/examples/logarithm_quotient/statement.lit"),
        "LnQuotient",
        "logarithmQuotientValue",
    ),
    (
        include_str!("../../../lean/examples/exponential_injective/statement.lit"),
        "ExpInjective",
        "exponentialInjectiveValue",
    ),
    (
        include_str!("../../../lean/examples/logarithm_injective/statement.lit"),
        "LnInjective",
        "logarithmInjectiveValue",
    ),
    (
        include_str!("../../../lean/examples/log_from_known_power/statement.lit"),
        "LogFromKnownPower",
        "logarithmFromPowerValue",
    ),
    (
        include_str!("../../../lean/examples/power_from_known_log/statement.lit"),
        "PowerFromKnownLog",
        "powerFromLogarithmValue",
    ),
];

fn equality(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let forall = super::forall_proof_mut(&mut run.statement_results[0]);
    super::equality_proof_mut(&mut forall.proved_then_facts[0].verify_result)
}
fn rule(proof: &mut VerifyEqualitySuccess) -> &mut Rule {
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::ExponentialLogarithmIdentity(p),
    ) = &mut proof.searched_proof
    else {
        panic!("original exponential/logarithm variant")
    };
    p
}
fn image(rule: &mut Rule) -> &mut EqualFactSearchedProof {
    match rule {
        Rule::ExpInjective(p) => &mut p.image_equality,
        Rule::LnInjective(p) => &mut p.image_equality,
        Rule::LogFromKnownPower(p) => &mut p.power_equality,
        Rule::PowerFromKnownLog(p) => &mut p.logarithm_equality,
        _ => panic!(),
    }
}

#[test]
fn all_seven_exponential_logarithm_variants_replay_the_actual_selected_route() {
    for (source, variant, law) in CASES {
        let (mut run, compiler) = super::execute(source);
        assert_eq!(rule(equality(&mut run)).rule_id(), variant);
        let output = compiler
            .compile_run(&run, "exp_log")
            .unwrap_or_else(|e| panic!("{variant}: {e}"));
        assert!(output.contains(&format!("Litex.{law}")));
        assert_eq!(output, compiler.compile_run(&run, "exp_log").unwrap());
    }
}

#[test]
fn exponential_logarithm_equalities_keep_the_original_orientation() {
    for index in [0, 1, 2, 5, 6] {
        let (source, _, law) = CASES[index];
        let (prefix, last) = source.trim_end().rsplit_once('\n').unwrap();
        let (left, right) = last.trim().split_once('=').unwrap();
        let source = format!(
            "{prefix}\n{}{}={}\n",
            if index < 3 { "    " } else { "        " },
            right,
            left
        );
        let (run, compiler) = super::execute(&source);
        let output = compiler
            .compile_run(&run, "exp_log_reverse")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        assert!(output.contains(&format!("Litex.{law}")));
    }
}

#[test]
fn injectivity_needs_the_two_original_membership_children_and_image_citation() {
    for index in [3, 4] {
        for change in ["children", "image_future", "wd"] {
            let (mut run, compiler) = super::execute(CASES[index].0);
            let p = equality(&mut run);
            let future = p.fact.fact_id;
            if change == "wd" {
                let p = p.well_defined_proof.as_detailed_mut().unwrap();
                std::mem::swap(&mut p.left, &mut p.right);
            } else {
                let p = rule(p);
                if change == "children" {
                    match p {
                        Rule::ExpInjective(p) => {
                            std::mem::swap(&mut p.left_real, &mut p.right_real)
                        }
                        Rule::LnInjective(p) => {
                            std::mem::swap(&mut p.left_positive, &mut p.right_positive)
                        }
                        _ => panic!(),
                    }
                } else {
                    let EqualFactSearchedProof::ByEquivalenceClass(
                        EqualFactSearchedProofByEquivalenceClass::KnownPath(p),
                    ) = image(p)
                    else {
                        panic!("original image path")
                    };
                    assert!(!p.path.is_empty());
                    p.path[0].2 = future;
                }
            }
            compiler.compile_run(&run, change).expect_err(
                "original endpoint membership, constructor evidence and prior image citation",
            );
        }
    }
}

#[test]
fn inverse_power_log_rules_retain_integer_guard_and_image_evidence() {
    for index in [5, 6] {
        for change in ["integer_subject", "image_future", "base_subject"] {
            let (mut run, compiler) = super::execute(CASES[index].0);
            let p = equality(&mut run);
            let future = p.fact.fact_id;
            let r = rule(p);
            if change == "image_future" {
                let EqualFactSearchedProof::ByEquivalenceClass(
                    EqualFactSearchedProofByEquivalenceClass::KnownPath(p),
                ) = image(r)
                else {
                    panic!("original inverse image path")
                };
                assert!(!p.path.is_empty());
                p.path[0].2 = future;
            } else if change == "integer_subject" {
                let child = match r {
                    Rule::LogFromKnownPower(p) => &mut p.exponent_integer,
                    Rule::PowerFromKnownLog(p) => &mut p.exponent_integer,
                    _ => panic!(),
                };
                let AtomicFact::InFact(f) = &mut super::atomic_proof_mut(child).fact else {
                    panic!()
                };
                f.set = Obj::StandardSet(StandardSet::R);
            } else {
                use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::log_algebra_base_proof::LogAlgebraBaseProof;
                let base = match r {
                    Rule::LogFromKnownPower(p) => &mut p.base_proof,
                    Rule::PowerFromKnownLog(p) => &mut p.base_proof,
                    _ => panic!(),
                };
                let LogAlgebraBaseProof::PositiveNonunit(p) = base else {
                    panic!("original positive nonunit guard")
                };
                let AtomicFact::NotEqualFact(f) =
                    &mut super::atomic_proof_mut(&mut p.nonunit_proof).fact
                else {
                    panic!()
                };
                f.left = Obj::Literal(Literal::Number(Number::new("2".into())));
            }
            compiler
                .compile_run(&run, change)
                .expect_err("original integer, base and exact selected image proof");
        }
    }
}

#[test]
fn exponential_logarithm_domains_do_not_accept_invalid_neighbors() {
    for source in [
        "forall a,b R:\n    ln(a*b)=ln(a)+ln(b)\n",
        "forall a,x R+,n Z:\n    a^n=x\n    =>:\n        log(a,x)=n\n",
        "forall a,b C:\n    exp(a)=exp(b)\n    =>:\n        a=b\n",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        assert!(
            !Runtime::new(command)
                .run_litex_code(source)
                .unwrap()
                .success
        );
    }
}

#[test]
fn inverse_power_log_rules_use_each_original_legal_base_guard() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::log_algebra_base_proof::LogAlgebraBaseProof;
    for index in [5, 6] {
        for (guard, kind) in [("1<a", 0), ("a<1", 1), ("a!=1", 2)] {
            let source = CASES[index].0.replace("a!=1", guard);
            let (mut run, compiler) = super::execute(&source);
            let base = match rule(equality(&mut run)) {
                Rule::LogFromKnownPower(p) => &p.base_proof,
                Rule::PowerFromKnownLog(p) => &p.base_proof,
                _ => panic!(),
            };
            assert!(matches!(
                (base, kind),
                (LogAlgebraBaseProof::GreaterThanOne(_), 0)
                    | (LogAlgebraBaseProof::BelowOne(_), 1)
                    | (LogAlgebraBaseProof::PositiveNonunit(_), 2)
            ));
            compiler
                .compile_run(&run, "original_log_base_guard")
                .unwrap_or_else(|e| panic!("{source}: {e}"));
        }
    }
}
