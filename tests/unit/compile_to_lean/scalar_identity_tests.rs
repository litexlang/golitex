use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::VerifyEqualitySuccess;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_scalar_identities::ScalarIdentityBuiltinRuleProof as Rule;
use crate::prelude::*;

const CASES: [(&str, &str, &str); 10] = [
    (
        include_str!("../../../lean/examples/absolute_difference_symmetry/statement.lit"),
        "AbsDifferenceSymmetry",
        "absDifferenceSymmetryValue",
    ),
    (
        include_str!("../../../lean/examples/floor_negation/statement.lit"),
        "FloorNegation",
        "roundingNegationValue",
    ),
    (
        include_str!("../../../lean/examples/ceil_negation/statement.lit"),
        "CeilNegation",
        "roundingNegationValue",
    ),
    (
        include_str!("../../../lean/examples/floor_integer_translation/statement.lit"),
        "FloorIntegerTranslation",
        "roundingIntegerTranslationValue",
    ),
    (
        include_str!("../../../lean/examples/ceil_integer_translation/statement.lit"),
        "CeilIntegerTranslation",
        "roundingIntegerTranslationValue",
    ),
    (
        include_str!("../../../lean/examples/minimum_maximum_absorption/statement.lit"),
        "MinMaxAbsorption",
        "minMaxAbsorptionValue",
    ),
    (
        include_str!("../../../lean/examples/maximum_minimum_absorption/statement.lit"),
        "MaxMinAbsorption",
        "minMaxAbsorptionValue",
    ),
    (
        include_str!("../../../lean/examples/least_common_multiple_zero/statement.lit"),
        "LcmZero",
        "lcmZeroValue",
    ),
    (
        include_str!("../../../lean/examples/sign_zero_reflection/statement.lit"),
        "SignZeroReflection",
        "signZeroReflectionValue",
    ),
    (
        include_str!("../../../lean/examples/absolute_zero_reflection/statement.lit"),
        "AbsZeroArgument",
        "absoluteZeroReflectionValue",
    ),
];
fn target(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let root = super::forall_proof_mut(&mut run.statement_results[0]);
    super::equality_proof_mut(&mut root.proved_then_facts[0].verify_result)
}
fn selected(proof: &mut VerifyEqualitySuccess) -> &mut Rule {
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::ScalarIdentity(p)) =
        &mut proof.searched_proof
    else {
        panic!("original selected scalar identity");
    };
    p
}
#[test]
fn scalar_identities_replay_the_exact_selected_rule_in_both_equation_orientations() {
    for (source, rule, law) in CASES {
        let (prefix, last) = source.trim_end().rsplit_once('\n').unwrap();
        let (left, right) = last.trim().split_once('=').unwrap();
        let indent = &last[..last.len() - last.trim_start().len()];
        let reversed = format!("{prefix}\n{indent}{right}={left}\n");
        for source in [source, &reversed] {
            let (mut run, compiler) = super::execute(source);
            assert_eq!(selected(target(&mut run)).rule_id(), rule, "{source}");
            let output = compiler
                .compile_run(&run, "scalar_identity")
                .unwrap_or_else(|e| panic!("{source}: {e}"));
            assert!(output.contains(&format!("Litex.{law}")));
            assert_eq!(
                output,
                compiler.compile_run(&run, "scalar_identity").unwrap()
            );
        }
    }
}
#[test]
fn scalar_identities_support_original_negation_and_commuted_argument_profiles() {
    let mut cases = Vec::new();
    for (round, opposite) in [("floor", "ceil"), ("ceil", "floor")] {
        for input in ["-x", "0-x"] {
            for negative in [format!("-{opposite}(x)"), format!("0-{opposite}(x)")] {
                cases.push(format!("forall x R:\n    {round}({input})={negative}\n"));
            }
        }
        for input in ["x+n", "n+x"] {
            for output in [format!("{round}(x)+n"), format!("n+{round}(x)")] {
                cases.push(format!("forall x R, n Z:\n    {round}({input})={output}\n"));
            }
        }
    }
    for (outer, inner) in [("min", "max"), ("max", "min")] {
        for nested in [format!("{inner}(x,y)"), format!("{inner}(y,x)")] {
            for expression in [
                format!("{outer}(x,{nested})"),
                format!("{outer}({nested},x)"),
            ] {
                cases.push(format!("forall x,y R:\n    {expression}=x\n"));
            }
        }
    }
    cases.push("forall n Z:\n    lcm(0,n)=0\n".to_string());
    for source in cases {
        let (mut run, compiler) = super::execute(&source);
        selected(target(&mut run));
        compiler
            .compile_run(&run, "scalar_identity_profile")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
    }
}
#[test]
fn scalar_identities_cannot_retag_the_rule_or_exchange_original_endpoint_constructors() {
    for (source, _, _) in CASES {
        for mutation in ["variant", "wd"] {
            let (mut run, compiler) = super::execute(source);
            let p = target(&mut run);
            if mutation == "wd" {
                let wd = p.well_defined_proof.as_detailed_mut().unwrap();
                std::mem::swap(&mut wd.left, &mut wd.right);
            } else {
                let p = selected(p);
                *p = if matches!(p, Rule::AbsDifferenceSymmetry(_)) {
                    Rule::LcmZero(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_scalar_identities::LcmZeroBuiltinRuleProof {})
                } else {
                    Rule::AbsDifferenceSymmetry(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_scalar_identities::AbsDifferenceSymmetryProof::new())
                };
            }
            compiler
                .compile_run(&run, mutation)
                .expect_err("exact selected rule and original endpoint WD");
        }
    }
}
#[test]
fn rounding_translation_keeps_original_integer_domain_and_scoped_citation() {
    for index in [3, 4] {
        for mutation in ["carrier", "future"] {
            let (mut run, compiler) = super::execute(CASES[index].0);
            let p = target(&mut run);
            let future = p.fact.fact_id;
            let child = match selected(p) {
                Rule::FloorIntegerTranslation(p) => &mut p.integer_proof,
                Rule::CeilIntegerTranslation(p) => &mut p.integer_proof,
                _ => panic!(),
            };
            let child = super::atomic_proof_mut(child);
            if mutation == "carrier" {
                let AtomicFact::InFact(f) = &mut child.fact else {
                    panic!();
                };
                f.set = Obj::StandardSet(StandardSet::R);
            } else {
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                    &mut child.searched_proof
                else {
                    panic!("original integer citation");
                };
                cite.cite_fact_id = future;
            }
            compiler
                .compile_run(&run, mutation)
                .expect_err("original integer requirement cannot be weakened or cite a later fact");
        }
    }
}

#[test]
fn scalar_zero_reflection_keeps_original_real_domain_and_stored_equality_path() {
    for index in [8, 9] {
        for mutation in ["carrier", "missing", "future", "endpoint"] {
            let (mut run, compiler) = super::execute(CASES[index].0);
            let p = target(&mut run);
            let future = p.fact.fact_id;
            let (real, premise) = match selected(p) {
                Rule::SignZeroReflection(p) => (&mut p.real_proof, p.premise_proof.as_mut()),
                Rule::AbsZeroArgument(p) => (&mut p.real_proof, p.premise_proof.as_mut()),
                _ => panic!(),
            };
            if mutation == "carrier" {
                let AtomicFact::InFact(f) = &mut super::atomic_proof_mut(real).fact else {
                    panic!();
                };
                f.set = Obj::StandardSet(StandardSet::C);
            } else {
                let EqualFactSearchedProof::ByEquivalenceClass(
                    EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
                ) = premise
                else {
                    panic!("original stored property path");
                };
                assert!(!path.path.is_empty());
                match mutation {
                    "missing" => path.path.clear(),
                    "future" => path.path[0].2 = future,
                    _ => path.path[0].0 = Obj::Literal(Literal::Number(Number::new("1".into()))),
                }
            }
            compiler.compile_run(&run, mutation).expect_err("the original real requirement and exact visible property equality must be replayed");
        }
    }
}
