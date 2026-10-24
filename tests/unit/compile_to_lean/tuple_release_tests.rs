#[test]
fn tuple_release_replays_membership_and_coordinate_publications() {
    let (run, compiler) = super::execute(include_str!(
        "../../../lean/examples/released_tuple_coordinates/statement.lit"
    ));
    compiler
        .compile_run(&run, "released_tuple_coordinates")
        .unwrap();
}

#[test]
fn tuple_release_replays_empty_singleton_mixed_and_cartesian_members() {
    for source in [
        include_str!("../../../lean/examples/released_finite_tuples/statement.lit"),
        include_str!("../../../lean/examples/released_cartesian_coordinates/statement.lit"),
        include_str!("../../../lean/examples/released_local_tuple/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        compiler
            .compile_run(&run, "released_finite_shapes")
            .unwrap();
    }
}
use crate::execute::execute_release_tuple_def_stmt::{
    ExecReleaseTupleDefStmtResult, ExecReleaseTupleDefStmtSuccess,
};
use crate::prelude::*;

fn release(statement: &mut ExecStmtResult) -> &mut ExecReleaseTupleDefStmtSuccess {
    let ExecStmtResult::ReleaseAndExpand(crate::execute::ExecReleaseAndExpandStmtResult::TupleDef(
        ExecReleaseTupleDefStmtResult::Success(p),
    )) = statement
    else {
        panic!("tuple release")
    };
    p
}

#[test]
fn tuple_release_rejects_corrupted_shapes_stages_rules_and_publications() {
    for mutation in 0..9 {
        let (mut run, compiler) = super::execute("let t = (1,2)\nrelease tuple def t\n");
        let p = release(&mut run.statement_results[1]);
        match mutation {
            0 => p.return_proofs.clear(),
            1 => p.return_proofs.swap(0, 1),
            2 => p.coordinate_proofs.clear(),
            3 => p.coordinate_proofs.swap(0, 1),
            4 => p.stored.swap(0, 1),
            5 => {
                p.stored.pop();
            }
            6 => p.shape.signature.ret_set = Box::new(Obj::StandardSet(StandardSet::R)),
            7 => {
                p.membership_rule.theorem =
                    crate::builtin_theorem::BuiltinTheoremId::CartesianMemberFromCoordinates
            }
            8 => p.statement.obj = Obj::StandardSet(StandardSet::R),
            _ => unreachable!(),
        }
        assert!(
            compiler.compile_run(&run, "corrupt_tuple_release").is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn tuple_release_stores_are_visible_only_after_all_checks_and_in_order() {
    use crate::compile_to_lean::compile_release_tuple_def_result::tuple_release_publication_start;
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    let (mut run, compiler) = super::execute("let t = (1,2)\nrelease tuple def t\n");
    let p = release(&mut run.statement_results[1]);
    let ids: Vec<_> = p.stored.iter().map(|s| s.primary_fact_id()).collect();
    let head = tuple_release_publication_start(p);
    let prefix = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    let scope = SourcePosition::new(
        Some(&prefix),
        SourceOwner::Statement(&run.statement_results[1]),
        0,
    );
    for stage in 0..=head + ids.len() {
        let position = SourcePosition {
            before: stage,
            ..scope
        };
        assert_eq!(position.is_local(), stage < head);
        for (index, id) in ids.iter().enumerate() {
            assert_eq!(
                compiler.cited_fact_reference(*id, &position).is_ok(),
                stage > head + index,
                "stage {stage}, store {index}"
            );
        }
    }
}

#[test]
fn tuple_release_rejects_corrupt_union_strategy_premises() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute("let t = (1,2)\nrelease tuple def t\n");
        let p = release(&mut run.statement_results[1]);
        let atomic = super::atomic_proof_mut(&mut p.return_proofs[0]);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionMembershipFromLeft(proof),
        ) = &mut atomic.searched_proof
        else {
            panic!("selected left-union strategy")
        };
        match mutation {
            0 => proof.requirement_facts.clear(),
            1 => proof.proof_of_requirement_facts.clear(),
            2 => {
                let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut proof.requirement_facts[0]
                else {
                    panic!("member")
                };
                f.set = Obj::StandardSet(StandardSet::R);
            }
            _ => unreachable!(),
        }
        assert!(compiler
            .compile_run(&run, "corrupt_union_strategy")
            .is_err());
    }
}

#[test]
fn tuple_release_rejects_corrupt_variable_coordinate_certificates() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute("have p cart(R,Z)\nrelease tuple def p\n");
        let p = release(&mut run.statement_results[1]);
        let VerifyFactResult::ForallFact(checked) = &mut p.return_proofs[0] else {
            panic!("return forall")
        };
        let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(checked)) =
            checked.as_mut()
        else {
            panic!("local introduction")
        };
        let atomic = super::atomic_proof_mut(&mut checked.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteFunctionApplicationMembership(proof)) = &mut atomic.searched_proof else { panic!("finite-return strategy") };
        match mutation {
            0 => proof.index = Some(1),
            1 => proof.proof_of_requirement_facts.clear(),
            2 => proof.requirement_facts.swap(0, 1),
            3 => proof.source.signature.ret_set = Box::new(Obj::StandardSet(StandardSet::R)),
            _ => unreachable!(),
        }
        assert!(compiler
            .compile_run(&run, "corrupt_finite_returns")
            .is_err());
    }
}

#[test]
fn tuple_release_local_facts_do_not_escape_theorem_scope() {
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/released_local_tuple/statement.lit"
    ));
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(theorem),
    )) = &mut run.statement_results[0]
    else {
        panic!("theorem")
    };
    let ExecDefThmBodyProof::Forall(body) = &mut theorem.body else {
        panic!("forall theorem")
    };
    let ids: Vec<_> = release(&mut body.proof_steps[1])
        .stored
        .iter()
        .map(|s| s.primary_fact_id())
        .collect();
    let outside = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    for id in ids {
        assert!(compiler.cited_fact_reference(id, &outside).is_err());
    }
    compiler.compile_run(&run, "local_tuple_release").unwrap();
}

#[test]
fn tuple_release_historical_coordinate_retains_only_its_original_context() {
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    let (mut run, compiler) =
        super::execute("have p cart(R,Z)\nhave later R\nrelease tuple def p\n");
    let p = release(&mut run.statement_results[2]);
    let fact = crate::compile_to_lean::helper::source_subject(&p.coordinate_proofs[0]).unwrap();
    let Fact::AtomicFact(AtomicFact::InFact(member)) = fact else {
        panic!("coordinate")
    };
    let scope = SourcePosition::new(None, SourceOwner::Run(&run), 2);
    let count = scope
        .with_visible_inferred_subject_filter(&member.element, &mut |store, producer| {
            compiler
                .compile_cart_inferred_subject(&member.element, store, producer)
                .map(|term| term.map(|_| producer.context_parameters().len()))
        })
        .unwrap();
    assert_eq!(scope.context_parameters().len(), 2);
    assert_eq!(count, Some(1));
    compiler.compile_run(&run, "historical_coordinate").unwrap();
}
