const RECIPROCAL: &str =
    include_str!("../../../lean/examples/guarded_reciprocal_preimages/statement.lit");

#[test]
fn guarded_preimages_compile_membership_projection_and_containment() {
    let (run, compiler) = super::execute(RECIPROCAL);
    let first = compiler.compile_run(&run, "PreimageTest").unwrap();
    assert!(first.contains("Litex.preimage "));
    assert!(first.contains("Litex.preimageSet "));
    assert!(first.contains("Litex.preimageMembers"));
    assert!(first.contains("Litex.preimageSetMembers"));
    assert_eq!(first, compiler.compile_run(&run, "PreimageTest").unwrap());
}

use crate::execute::execute_fact_stmt::function_preimage::FunctionPreimageConstructionProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef;
use crate::prelude::*;

fn member_mut(
    run: &mut RunLitexCodeResult,
    index: usize,
) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    super::atomic_proof_mut(
        &mut super::fact_statement_mut(&mut run.statement_results[index]).verify_result,
    )
}

#[test]
fn preimage_wd_rejects_missing_or_reordered_operands_and_missing_sethood() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(RECIPROCAL);
        let index = if mutation == 2 { 3 } else { 2 };
        let p = member_mut(&mut run, index);
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FunctionSpace(p),
            ..
        } = (&mut p
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .well_defined_of_each_parameter[1])
            .as_detailed_mut()
            .unwrap()
        else {
            panic!()
        };
        match (mutation, p) {
            (0, FunctionSpaceObjWellDefinedProofByDef::Preimage(p)) => {
                p.child_obj_well_defined.pop();
            }
            (1, FunctionSpaceObjWellDefinedProofByDef::Preimage(p)) => {
                p.child_obj_well_defined.swap(0, 1)
            }
            (2, FunctionSpaceObjWellDefinedProofByDef::PreimageSet(p)) => {
                p.requirement_fact_verified.clear()
            }
            _ => panic!(),
        }
        assert!(compiler.compile_run(&run, "bad_preimage_wd").is_err());
    }
}

fn construction_mut(run: &mut RunLitexCodeResult) -> &mut FunctionPreimageConstructionProof {
    let p = member_mut(run, 2);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PreimageMembership(p),
    ) = &mut p.searched_proof
    else {
        panic!()
    };
    &mut p.construction
}

#[test]
fn preimage_construction_rejects_changed_bound_guard_output_or_source() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(RECIPROCAL);
        let p = construction_mut(&mut run);
        match mutation {
            0 => p.builder.param_set = Box::new(super::number_object("17")),
            1 => {
                p.builder.facts.remove(0);
            }
            2 => {
                let QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(p)) =
                    p.builder.facts.last_mut().unwrap()
                else {
                    panic!()
                };
                p.right = super::number_object("17");
            }
            3 => p.source.signature.dom_facts.clear(),
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "bad_preimage_builder").is_err());
    }
}

#[test]
fn preimage_membership_rejects_missing_or_reordered_children_and_mismatched_requirements() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(RECIPROCAL);
        let p = member_mut(&mut run, 2);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PreimageMembership(p),
        ) = &mut p.searched_proof
        else {
            panic!()
        };
        match mutation {
            0 => {
                p.proof_of_requirement_facts.pop();
            }
            1 => p.proof_of_requirement_facts.swap(0, 1),
            2 => p.requirement_facts.swap(0, 1),
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "bad_preimage_member").is_err());
    }
}

#[test]
fn abstract_binary_and_positive_preimages_replay() {
    for source in [
        include_str!("../../../lean/examples/abstract_function_preimages/statement.lit"),
        include_str!("../../../lean/examples/binary_quotient_preimages/statement.lit"),
        include_str!("../../../lean/examples/positive_domain_preimages/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "preimage_variants").unwrap();
        assert!(lean.contains("Litex.preimageMembers"));
        assert_eq!(
            lean,
            compiler.compile_run(&run, "preimage_variants").unwrap()
        );
    }
}

#[test]
fn preimage_inference_rejects_wrong_seed_reordered_stores_and_reused_ids() {
    use crate::store_fact_and_infer::{InferAtomicFactResult, InferInFactResult, InferResult};
    use std::rc::Rc;
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(RECIPROCAL);
        let p = super::forall_proof_mut(&mut run.statement_results[4]);
        let store = Rc::get_mut(&mut p.introduced_params.defined_params.store_and_infer_results[0])
            .unwrap();
        let Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))) = &mut store.infer
        else {
            panic!()
        };
        let p = rules
            .iter_mut()
            .find_map(|r| match r {
                InferInFactResult::Preimage(p) => Some(p),
                _ => None,
            })
            .unwrap();
        assert!(p.derived.len() >= 3);
        match mutation {
            0 => p.source_fact_id = p.derived[0].primary_fact_id(),
            1 => p.derived.swap(0, 1),
            2 => {
                let reused = p.derived[0].primary_fact_id();
                let StoreFactResult::AtomicFact(stored) = &mut p.derived[1].store else {
                    panic!()
                };
                stored.fact_id = reused;
            }
            3 => p.construction.source.signature.dom_facts.clear(),
            _ => unreachable!(),
        }
        assert!(compiler
            .compile_run(&run, "bad_preimage_inference")
            .is_err());
    }
}

#[test]
fn preimage_membership_rejects_changed_tuple_and_invalid_input_equality() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_strategy::result::FunctionPreimageInputView;
    let source = include_str!("../../../lean/examples/binary_quotient_preimages/statement.lit");
    for mutation in 0..2 {
        let (mut run, compiler) = super::execute(source);
        let p = member_mut(&mut run, 2);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PreimageMembership(p),
        ) = &mut p.searched_proof
        else {
            panic!()
        };
        let FunctionPreimageInputView::LiteralTuple { tuple, input_equal } = &mut p.input_view
        else {
            panic!()
        };
        if mutation == 0 {
            tuple.args.swap(0, 1);
        } else {
            input_equal.path.push((
                super::number_object("6"),
                super::number_object("2"),
                p.requirement_facts[0].fact_id(),
            ));
        }
        assert!(compiler.compile_run(&run, "bad_preimage_input").is_err());
    }
}
