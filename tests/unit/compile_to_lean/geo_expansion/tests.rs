use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::{EqualitySearchProofByObjectDefinition, by_fn_application::EqualitySearchProofByFnApplicationObjectDefinition};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::normalize_function_body::{FunctionBodyExpansionProof, FiniteCoordinateBodyExpansionProof};

fn coordinate_step(result: &mut RunLitexCodeResult) -> &mut FiniteCoordinateBodyExpansionProof {
    let theorem = super::named_theorem_mut(&mut result.statement_results[4]);
    let ExecDefThmBodyProof::Forall(body) = &mut theorem.body else {
        panic!("forall body")
    };
    let eq = super::equality_proof_mut(
        &mut super::fact_statement_mut(&mut body.proof_steps[2]).verify_result,
    );
    let EqualFactSearchedProof::ByObjectDefinition(
        EqualitySearchProofByObjectDefinition::ByFnApplication(
            EqualitySearchProofByFnApplicationObjectDefinition::HaveFnEqual(proof),
        ),
    ) = &mut eq.searched_proof
    else {
        panic!("original midpoint definition expansion")
    };
    proof
        .normalization
        .expansions
        .iter_mut()
        .find_map(|s| match s {
            FunctionBodyExpansionProof::FiniteCoordinate(p) => Some(p),
            _ => None,
        })
        .expect("recorded coordinate beta step")
}

#[test]
fn geometry_midpoint_replays_finite_coordinate_expansions() {
    let (mut result, compiler) = super::execute(include_str!("midpoint.lit"));
    assert!(coordinate_step(&mut result).index > 0);
    assert!(compiler
        .compile_run(&result, "midpoint")
        .unwrap()
        .contains("have _coordinate"));
}

#[test]
fn geometry_finite_expansion_rejects_changed_coordinate_and_body() {
    for change in ["index", "body", "continued"] {
        let (mut result, compiler) = super::execute(include_str!("midpoint.lit"));
        let step = coordinate_step(&mut result);
        match change {
            "index" => step.index = 0,
            "body" => step.expanded_body = super::number_object("7"),
            "continued" => step.continued_body = super::number_object("7"),
            _ => unreachable!(),
        }
        assert_eq!(
            compiler
                .compile_run(&result, "bad_coordinate")
                .unwrap_err()
                .route,
            "FiniteExpansion/Coordinate"
        );
    }
}

const TUPLE: &str = "forall a, b, c R:\n    (c-a,a-c)=(b-a+c-b,a-b+b-c)\n";

#[test]
fn geometry_tuple_strategy_rejects_a_changed_component_requirement() {
    let (mut result, compiler) = super::execute(TUPLE);
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let eq = super::equality_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByBuiltinStrategy(
        EqualitySearchProofByBuiltinStrategy::TupleComponentEquality(p),
    ) = &mut eq.searched_proof
    else {
        panic!("original tuple strategy")
    };
    p.proof_of_requirement_facts.pop();
    assert!(compiler
        .compile_run(&result, "bad_tuple")
        .unwrap_err()
        .route
        .starts_with("Tuple"));
}
