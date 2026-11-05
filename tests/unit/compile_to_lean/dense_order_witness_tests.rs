use super::member_witness_tests::witness;
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::{
    ExistShapedFactSearchProofByBuiltinRule, ExistShapedFactSearchedProof,
};
use crate::prelude::*;

const RECIPROCAL: &str = r#"thm checked_reciprocal_witness:
    ? forall epsilon R+:
        exist n N+ st {1/n<epsilon}
    exist n N+ st {1/n<epsilon}
"#;
const MIDPOINT: &str = r#"thm checked_real_density_witness:
    ? forall a,b R:
        a<b
        =>:
            exist x R st {a<x<b}
    exist x R st {a<x<b}
"#;

#[test]
fn dense_order_witnesses_replay_original_selected_exist_rules() {
    for (source, law) in [
        (RECIPROCAL, "reciprocalNaturalWitness"),
        (MIDPOINT, "realMidpointWitness"),
    ] {
        let (mut run, compiler) = super::execute(source);
        assert!(matches!(
            witness(&mut run).searched_proof,
            ExistShapedFactSearchedProof::ByBuiltinRule(
                ExistShapedFactSearchProofByBuiltinRule::ArchimedeanReciprocal(_)
                    | ExistShapedFactSearchProofByBuiltinRule::RealDensityMidpoint(_)
            )
        ));
        let output = compiler
            .compile_run(&run, "dense_order_witness")
            .unwrap_or_else(|e| panic!("{e}"));
        assert!(output.contains(&format!("Litex.{law}")));
        assert_eq!(
            output,
            compiler.compile_run(&run, "dense_order_witness").unwrap()
        );
    }
}

#[test]
fn reciprocal_witness_requires_the_original_positive_bound_proof() {
    for change in ["subject", "future"] {
        let (mut run, compiler) = super::execute(RECIPROCAL);
        let p = witness(&mut run);
        let goal_id = p.fact.plain().fact_id;
        let ExistShapedFactSearchedProof::ByBuiltinRule(
            ExistShapedFactSearchProofByBuiltinRule::ArchimedeanReciprocal(p),
        ) = &mut p.searched_proof
        else {
            panic!()
        };
        let atomic = super::atomic_proof_mut(&mut p.positive_bound_proof);
        if change == "subject" {
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
        compiler
            .compile_run(&run, change)
            .expect_err("original preceding positive membership");
    }
}

#[test]
fn midpoint_witness_requires_original_ordered_real_and_strict_children() {
    for change in ["missing", "reorder", "subject", "future", "requirement"] {
        let (mut run, compiler) = super::execute(MIDPOINT);
        let p = witness(&mut run);
        let goal_id = p.fact.plain().fact_id;
        let ExistShapedFactSearchedProof::ByBuiltinRule(
            ExistShapedFactSearchProofByBuiltinRule::RealDensityMidpoint(p),
        ) = &mut p.searched_proof
        else {
            panic!()
        };
        match change {
            "missing" => {
                p.proof_of_requirement_facts.pop();
            }
            "reorder" => p.proof_of_requirement_facts.swap(0, 1),
            "subject" => {
                let atomic = super::atomic_proof_mut(&mut p.proof_of_requirement_facts[0]);
                let AtomicFact::InFact(f) = &mut atomic.fact else {
                    panic!()
                };
                f.set = Obj::StandardSet(StandardSet::C);
            }
            "future" => {
                let atomic = super::atomic_proof_mut(&mut p.proof_of_requirement_facts[0]);
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                    &mut atomic.searched_proof
                else {
                    panic!()
                };
                cite.cite_fact_id = goal_id;
            }
            "requirement" => {
                p.requirement_facts.pop();
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, change)
            .expect_err("retain the three original checked requirements");
    }
}

#[test]
fn dense_order_witnesses_reject_changed_carrier_body_and_endpoints() {
    for source in [RECIPROCAL, MIDPOINT] {
        for change in ["carrier", "binder", "body", "endpoint"] {
            let (mut run, compiler) = super::execute(source);
            let ExistShapedFact::Exist(fact) = &mut witness(&mut run).fact else {
                panic!()
            };
            match change {
                "carrier" => {
                    fact.typed_parameters.groups[0].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::C))
                }
                "binder" => {
                    fact.typed_parameters.groups[0].params[0].id = IdentifierId::new(u64::MAX)
                }
                "body" => fact.facts.clear(),
                "endpoint" => match &mut fact.facts[0] {
                    QuantifierFreeFact::ChainFact(p) => p.objs.swap(0, 2),
                    QuantifierFreeFact::AtomicFact(AtomicFact::LessFact(p)) => {
                        std::mem::swap(&mut p.left, &mut p.right)
                    }
                    _ => panic!(),
                },
                _ => unreachable!(),
            }
            compiler
                .compile_run(&run, change)
                .expect_err("retain exact existential WD and schema");
        }
    }
}
