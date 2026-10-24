#[test]
fn cart_release_replays_complete_definition_and_its_citation() {
    let (run, compiler) = super::execute(include_str!(
        "../../../lean/examples/released_cartesian_definition/statement.lit"
    ));
    compiler
        .compile_run(&run, "released_cartesian_definition")
        .unwrap();
}

#[test]
fn cart_release_replays_boundary_lengths_generic_carriers_and_local_theorems() {
    for source in [
        include_str!("../../../lean/examples/empty_and_single_cartesian_products/statement.lit"),
        include_str!("../../../lean/examples/generic_cartesian_definitions/statement.lit"),
        include_str!("../../../lean/examples/local_cartesian_definition/statement.lit"),
        "release cart def cart(R,Z)\nrelease cart def cart(R,Z)\n",
    ] {
        let (run, compiler) = super::execute(source);
        let first = compiler.compile_run(&run, "cartesian_definitions").unwrap();
        assert_eq!(
            first,
            compiler.compile_run(&run, "cartesian_definitions").unwrap()
        );
    }
}

use crate::execute::execute_release_cart_def_stmt::{
    ExecReleaseCartDefStmtResult, ExecReleaseCartDefStmtSuccess,
};
use crate::prelude::*;

fn release(result: &mut ExecStmtResult) -> &mut ExecReleaseCartDefStmtSuccess {
    let ExecStmtResult::ReleaseAndExpand(crate::execute::ExecReleaseAndExpandStmtResult::CartDef(
        ExecReleaseCartDefStmtResult::Success(p),
    )) = result
    else {
        panic!("cart release")
    };
    p
}

fn builder(object: &mut Obj) -> &mut SetBuilder {
    let Obj::SetFormer(SetFormer::SetBuilder(set)) = object else {
        panic!("builder")
    };
    set
}

#[test]
fn cart_release_rejects_incomplete_or_changed_captured_definitions() {
    for mutation in 0..10 {
        let (mut run, compiler) = super::execute("release cart def cart(R,Z)\n");
        let p = release(&mut run.statement_results[0]);
        let EqualFactSearchedProof::ByObjectDefinition(
            crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::EqualitySearchProofByObjectDefinition::CartesianDefinition(definition)
        ) = &mut p.verification.searched_proof else { panic!("selected definition") };
        match mutation {
            0 => p.statement.cart.args.swap(0, 1),
            1 => builder(&mut p.verification.fact.right).facts.clear(),
            2 => builder(&mut definition.expanded_definition)
                .facts
                .swap(0, 1),
            3 => {
                builder(&mut definition.expanded_definition).facts.pop();
            }
            4 => {
                builder(&mut definition.expanded_definition).param_set =
                    Box::new(Obj::StandardSet(StandardSet::R))
            }
            5 | 6 => {
                let Obj::SetFormer(SetFormer::FiniteSeqSet(sequence)) =
                    builder(&mut definition.expanded_definition)
                        .param_set
                        .as_mut()
                else {
                    panic!("finite seq")
                };
                if mutation == 5 {
                    sequence.n = Box::new(Obj::Literal(Literal::Number(Number {
                        normalized_value: "3".into(),
                    })));
                } else {
                    sequence.set = Box::new(Obj::StandardSet(StandardSet::R));
                }
            }
            7 => definition.expanded_definition = Obj::StandardSet(StandardSet::R),
            8 => p.verification.fact.left = Obj::StandardSet(StandardSet::R),
            9 => {
                definition.definition_match = TheyAreTheSameProof::SameIr(
                    crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::SameIrProof::new(),
                );
            }
            _ => unreachable!(),
        }
        assert!(
            compiler
                .compile_run(&run, "corrupt_cart_definition")
                .is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn cart_release_publication_follows_verification_and_stays_in_scope() {
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    let (mut run, compiler) = super::execute("release cart def cart(R,Z)\n");
    let id = release(&mut run.statement_results[0])
        .store_and_infer
        .primary_fact_id();
    let prefix = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    for before in 0..=4 {
        let position = SourcePosition::new(
            Some(&prefix),
            SourceOwner::Statement(&run.statement_results[0]),
            before,
        );
        assert_eq!(
            compiler.cited_fact_reference(id, &position).is_ok(),
            before == 4
        );
    }
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/local_cartesian_definition/statement.lit"
    ));
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(thm),
    )) = &mut run.statement_results[0]
    else {
        panic!("theorem")
    };
    let ExecDefThmBodyProof::Forall(body) = &mut thm.body else {
        panic!("forall")
    };
    let id = release(&mut body.proof_steps[0])
        .store_and_infer
        .primary_fact_id();
    let outside = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    assert!(compiler.cited_fact_reference(id, &outside).is_err());
}

#[test]
fn cart_release_set_parameter_calls_reject_changed_evidence() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/local_cartesian_definition/statement.lit"
        ));
        let ExecStmtResult::By(crate::execute::execute_by_stmt::ExecByStmtResult::Thm(
            crate::execute::execute_by_stmt::ExecByThmStmtResult::Success(call),
        )) = &mut run.statement_results[1]
        else {
            panic!("theorem call")
        };
        match mutation {
            0 => call.type_proofs.swap(0, 1),
            1 => call.type_stores.clear(),
            2 => call.type_stores.swap(0, 1),
            _ => unreachable!(),
        }
        assert!(compiler
            .compile_run(&run, "corrupt_set_parameter_call")
            .is_err());
    }
}
