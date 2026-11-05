use super::member_witness_tests::witness;
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::{
    ExistShapedFactSearchProofByBuiltinRule as Rule, ExistShapedFactSearchedProof,
};
use crate::prelude::*;

const POS: &str = r#"thm checked_rational_positive_ratio:
    ? forall q Q:
        exist a,b Z st {b>0,q=a/b}
    exist a,b Z st {b>0,q=a/b}
"#;
const RATIO: &str = r#"thm checked_rational_integer_ratio:
    ? forall q Q:
        exist a Z,b Z* st {q=a/b}
    exist a Z,b Z* st {q=a/b}
"#;
const MULTIPLE: &str = r#"thm checked_integer_multiple_witness:
    ? forall a Z,b Z*:
        a%b=0
        =>:
            exist k Z st {a=b*k}
    exist k Z st {a=b*k}
"#;

fn rule(run: &mut RunLitexCodeResult) -> &mut Rule {
    let ExistShapedFactSearchedProof::ByBuiltinRule(p) = &mut witness(run).searched_proof else {
        panic!("actual selected existential builtin")
    };
    p
}

#[test]
fn rational_and_multiple_witnesses_replay_all_three_original_rules() {
    for (source, law) in [
        (POS, "rationalPositiveRatioWitness"),
        (RATIO, "rationalIntegerRatioWitness"),
        (MULTIPLE, "integerMultipleFromZeroRemainder"),
    ] {
        let (mut run, compiler) = super::execute(source);
        assert!(matches!(
            rule(&mut run),
            Rule::RationalPositiveDenominator(_)
                | Rule::RationalIntegerRatio(_)
                | Rule::IntegerMultipleFromZeroRemainder(_)
        ));
        let output = compiler
            .compile_run(&run, "ratio_multiple")
            .unwrap_or_else(|e| panic!("{e}"));
        assert!(output.contains(&format!("Litex.{law}")));
        assert_eq!(
            output,
            compiler.compile_run(&run, "ratio_multiple").unwrap()
        );
    }
    for source in [
        POS.replace("b>0", "0<b"),
        POS.replace("q=a/b", "a/b=q"),
        RATIO.replace("q=a/b", "a/b=q"),
        MULTIPLE.replace("a=b*k", "a=k*b"),
        MULTIPLE.replace("a=b*k", "b*k=a"),
        MULTIPLE.replace("a=b*k", "k*b=a"),
    ] {
        let (run, compiler) = super::execute(&source);
        compiler
            .compile_run(&run, "orientation")
            .unwrap_or_else(|e| panic!("{e}"));
    }
}

#[test]
fn ratio_witnesses_require_original_rational_membership_and_formation() {
    for source in [POS, RATIO] {
        for mutation in ["member", "future", "formation", "binder"] {
            let (mut run, compiler) = super::execute(source);
            let p = witness(&mut run);
            let goal_id = p.fact.plain().fact_id;
            if mutation == "formation" {
                p.well_defined_proof
                    .as_detailed_mut()
                    .unwrap()
                    .assumed_body_facts
                    .clear();
            } else if mutation == "binder" {
                let ExistShapedFact::Exist(fact) = &mut p.fact else {
                    panic!()
                };
                fact.typed_parameters.groups[0].params[0].id = IdentifierId::new(u64::MAX);
            } else {
                let membership = match &mut p.searched_proof {
                    ExistShapedFactSearchedProof::ByBuiltinRule(
                        Rule::RationalPositiveDenominator(p),
                    ) => &mut p.rational_membership_proof,
                    ExistShapedFactSearchedProof::ByBuiltinRule(Rule::RationalIntegerRatio(p)) => {
                        &mut p.rational_membership_proof
                    }
                    _ => panic!(),
                };
                let atomic = super::atomic_proof_mut(membership);
                if mutation == "member" {
                    let AtomicFact::InFact(f) = &mut atomic.fact else {
                        panic!()
                    };
                    f.set = Obj::StandardSet(StandardSet::R);
                } else {
                    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                        &mut atomic.searched_proof
                    else {
                        panic!()
                    };
                    cite.cite_fact_id = goal_id;
                }
            }
            compiler
                .compile_run(&run, mutation)
                .expect_err("retain original rational member, binder identity and body WD");
        }
    }
}

#[test]
fn integer_multiple_requires_four_original_ordered_premises() {
    for mutation in ["missing", "reorder", "nonzero", "remainder", "future"] {
        let (mut run, compiler) = super::execute(MULTIPLE);
        let id = witness(&mut run).fact.plain().fact_id;
        let Rule::IntegerMultipleFromZeroRemainder(p) = rule(&mut run) else {
            panic!()
        };
        match mutation {
            "missing" => {
                p.proof_of_requirement_facts.pop();
            }
            "reorder" => p.proof_of_requirement_facts.swap(0, 1),
            "nonzero" => {
                let Fact::AtomicFact(AtomicFact::NotEqualFact(f)) = &mut p.requirement_facts[2]
                else {
                    panic!()
                };
                f.right = Obj::Literal(Literal::Number(Number::new("1".into())));
            }
            "remainder" => {
                let Fact::AtomicFact(AtomicFact::EqualFact(f)) = &mut p.requirement_facts[3] else {
                    panic!()
                };
                f.right = Obj::Literal(Literal::Number(Number::new("1".into())));
            }
            "future" => {
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                    &mut super::atomic_proof_mut(&mut p.proof_of_requirement_facts[0])
                        .searched_proof
                else {
                    panic!()
                };
                cite.cite_fact_id = id;
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, mutation)
            .expect_err("exact original integer/nonzero/zero-remainder premises");
    }
}
