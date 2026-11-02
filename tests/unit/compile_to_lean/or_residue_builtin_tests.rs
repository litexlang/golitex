use super::or_order_builtin_tests::target;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    IntegerOperatorObjWellDefinedProofByDef, ModObjWellDefinedProof,
};
use crate::prelude::*;
const TWO: &str = include_str!("../../../lean/examples/complete_residues_two/statement.lit");
const THREE: &str = include_str!("../../../lean/examples/complete_residues_three/statement.lit");
fn remainder_wd(run: &mut RunLitexCodeResult) -> &mut ModObjWellDefinedProof {
    let FactWellDefinedProof::Equality(wd) = &mut target(run)
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .branches[0]
    else {
        panic!()
    };
    let wd = &mut wd.as_detailed_mut().unwrap().left;
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::IntegerOperator(IntegerOperatorObjWellDefinedProofByDef::Mod(wd)),
        ..
    } = wd.as_detailed_mut().unwrap()
    else {
        panic!("original remainder constructor")
    };
    wd
}
#[test]
fn complete_residues_replays_original_modulus_shuffled_positions_and_equalities() {
    for source in [TWO, THREE] {
        let (mut run, compiler) = super::execute(source);
        assert!(matches!(
            &target(&mut run).searched_proof,
            OrFactSearchedProof::ByBuiltinRule(OrFactSearchProofByBuiltinRule::CompleteResidues(_))
        ));
        let output = compiler.compile_run(&run, "residues").unwrap();
        assert!(output.contains("Litex.remainderResidueWitness"));
        assert_eq!(output, compiler.compile_run(&run, "residues").unwrap());
    }
}
#[test]
fn complete_residues_rejects_changed_subject_modulus_or_incomplete_coverage() {
    for source in [TWO, THREE] {
        for mutation in ["subject", "modulus", "duplicate", "missing"] {
            let (mut run, compiler) = super::execute(source);
            let p = target(&mut run);
            match mutation {
                "duplicate" => p.fact.facts[1] = p.fact.facts[0].clone(),
                "missing" => {
                    p.fact.facts.pop();
                }
                _ => {
                    let OrFactSearchedProof::ByBuiltinRule(
                        OrFactSearchProofByBuiltinRule::CompleteResidues(p),
                    ) = &mut p.searched_proof
                    else {
                        panic!()
                    };
                    if mutation == "subject" {
                        p.subject = Obj::Literal(Literal::Number(Number::new("0".into())));
                    } else {
                        p.modulus = Obj::Literal(Literal::Number(Number::new("4".into())));
                    }
                }
            }
            compiler
                .compile_run(&run, mutation)
                .expect_err("retain original subject, modulus and exactly one of each residue");
        }
    }
}
#[test]
fn complete_residues_retains_original_branch_formation_and_remainder_wd_stages() {
    for mutation in ["branches", "guard", "child", "swapped"] {
        let (mut run, compiler) = super::execute(TWO);
        if mutation == "branches" {
            target(&mut run)
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .branches
                .clear();
        } else {
            let wd = remainder_wd(&mut run);
            match mutation {
                "guard" => {
                    wd.requirement_fact_verified.pop();
                }
                "child" => {
                    wd.child_obj_well_defined.pop();
                }
                _ => wd.child_obj_well_defined.swap(0, 1),
            }
        }
        compiler
            .compile_run(&run, mutation)
            .expect_err("selected residue cover cannot replace original Mod constructor WD");
    }
}
#[test]
fn complete_residues_cannot_cite_the_future_or_in_its_integer_domain_proof() {
    let (mut run, compiler) = super::execute(TWO);
    let future = target(&mut run).fact.fact_id;
    let p = super::atomic_proof_mut(&mut remainder_wd(&mut run).requirement_fact_verified[0]);
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) = &mut p.searched_proof
    else {
        panic!("original integer member citation")
    };
    cite.cite_fact_id = future;
    compiler
        .compile_run(&run, "future")
        .expect_err("original constructor member must already be visible");
}
