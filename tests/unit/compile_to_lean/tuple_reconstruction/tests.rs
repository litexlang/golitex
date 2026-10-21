use crate::execute::execute_fact_stmt::known_tuple::KnownTupleShapeProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::search_equal_fact_proof_by_known_special_property::{EqualFactSearchProofByKnownSpecialProperty, TupleReconstructionKnownProof};
use crate::prelude::*;

const SOURCE: &str = "forall p cart(R, R):\n    p = (p(1), p(2))\n";

fn selected(result: &mut RunLitexCodeResult) -> &mut TupleReconstructionKnownProof {
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let equality = super::equality_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByKnownSpecialProperty(
        EqualFactSearchProofByKnownSpecialProperty::TupleReconstruction(rule),
    ) = &mut equality.searched_proof
    else {
        panic!("actual selected reconstruction")
    };
    rule
}

#[test]
fn tuple_reconstruction_replays_complete_coordinates_and_orientation() {
    for source in [
        SOURCE,
        "forall p cart(R, R):\n    (p(1), p(2)) = p\n",
        "forall p cart(R, R, R):\n    p = (p(1), p(2), p(3))\n",
    ] {
        let (mut result, compiler) = super::execute(source);
        selected(&mut result);
        let output = compiler
            .compile_run(&result, "reconstruct_coordinates")
            .unwrap();
        assert!(output.contains("Litex.FiniteFunction.reconstruct"));
    }
}

#[test]
fn tuple_reconstruction_rejects_missing_receiver_and_wrong_orientation() {
    for orientation in [false, true] {
        let (mut result, compiler) = super::execute(SOURCE);
        let rule = selected(&mut result);
        if orientation {
            rule.reversed = !rule.reversed;
        } else {
            rule.subjects.pop();
        }
        let error = compiler
            .compile_run(&result, "incomplete_reconstruction")
            .unwrap_err();
        assert_eq!(
            error.route,
            if orientation {
                "TupleReconstruction/Target"
            } else {
                "TupleReconstruction/Arity"
            }
        );
    }
}

#[test]
fn tuple_reconstruction_rejects_wrong_membership_and_dimension() {
    for dimension in [false, true] {
        let (mut result, compiler) = super::execute(SOURCE);
        let KnownTupleShapeProof::CartesianMembership(shape) = &mut selected(&mut result).shape
        else {
            panic!("Cartesian source")
        };
        if dimension {
            shape.cart.args.pop();
        } else {
            shape.membership.fact_id = FactId::new(u64::MAX);
        }
        assert!(compiler
            .compile_run(&result, "wrong_reconstruction_shape")
            .is_err());
    }
}

#[test]
fn tuple_reconstruction_preserves_each_receivers_recorded_equality() {
    let source = "forall p, q cart(R, R):\n    p = q\n    =>:\n        p = (p(1), q(2))\n";
    let (mut result, compiler) = super::execute(source);
    selected(&mut result);
    assert!(compiler
        .compile_run(&result, "transported_reconstruction")
        .is_ok());
    selected(&mut result).subjects.swap(0, 1);
    assert!(compiler
        .compile_run(&result, "swapped_reconstruction_receivers")
        .is_err());
}
