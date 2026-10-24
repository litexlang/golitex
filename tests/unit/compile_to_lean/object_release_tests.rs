use crate::execute::execute_release_obj_def_stmt::{
    ExecReleaseObjDefStmtResult, ExecReleaseObjDefStmtSuccess, ReleaseObjDefByKind,
};
use crate::prelude::*;

fn released(statement: &mut ExecStmtResult) -> &mut ExecReleaseObjDefStmtSuccess {
    let ExecStmtResult::ReleaseAndExpand(crate::execute::ExecReleaseAndExpandStmtResult::ObjDef(
        ExecReleaseObjDefStmtResult::Success(p),
    )) = statement
    else {
        panic!("object release");
    };
    p
}

#[test]
fn object_release_examples_replay_original_definitions() {
    for source in [
        include_str!("../../../lean/examples/released_value_definitions/statement.lit"),
        include_str!("../../../lean/examples/released_reciprocal_definition/statement.lit"),
        include_str!("../../../lean/examples/released_witness_definition/statement.lit"),
        include_str!("../../../lean/examples/released_local_definitions/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "released_definition").unwrap();
        assert_eq!(
            output,
            compiler.compile_run(&run, "released_definition").unwrap()
        );
    }
}

#[test]
fn object_release_emits_direct_original_fact_references() {
    let (mut run, compiler) = super::execute("have a R = 2\nrelease obj def a\n");
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(p)),
    )) = &run.statement_results[0]
    else {
        panic!("have equal");
    };
    let original: Vec<_> = p
        .store_and_infer_result
        .store_and_infer_results
        .iter()
        .map(|store| store.primary_fact_id())
        .collect();
    let released_ids: Vec<_> = released(&mut run.statement_results[1])
        .store_and_infer
        .iter()
        .map(|store| store.primary_fact_id())
        .collect();
    let output = compiler.compile_run(&run, "released_definition").unwrap();
    for (new, old) in released_ids.iter().zip(original) {
        let declaration = output
            .split(&format!("theorem h_{}", new.value()))
            .nth(1)
            .unwrap()
            .split("\n\n")
            .next()
            .unwrap();
        assert!(
            declaration.contains(&format!("h_{}", old.value())),
            "{declaration}"
        );
    }
}

#[test]
fn object_release_respects_parameter_offsets_and_repetition() {
    for source in [
        "have a, b R = 2, 3\nrelease obj def b\nrelease obj def a\nrelease obj def b\nb + 1 = 4\n",
        "have a, b R\nrelease obj def b\nrelease obj def a\na $in C\nb $in C\n",
        "have A, B set\nrelease obj def B\nrelease obj def A\n$is_set(B)\n",
    ] {
        let (run, compiler) = super::execute(source);
        compiler.compile_run(&run, "release_parameters").unwrap();
    }
}

#[test]
fn object_release_rejects_changed_lookup_identity_and_fact_subject() {
    for corruption in 0..4 {
        let (mut run, compiler) = super::execute("have a R = 2\nrelease obj def a\n");
        let p = released(&mut run.statement_results[1]);
        match corruption {
            0 => {
                let IdentifierObj::Plain { name, .. } = &mut p.statement.name else {
                    unreachable!()
                };
                *name = "other".into();
            }
            1 => {
                let ReleaseObjDefByKind::HaveObjEqual {
                    type_fact: Fact::AtomicFact(AtomicFact::InFact(f)),
                    ..
                } = &mut p.released
                else {
                    unreachable!()
                };
                f.set = Obj::StandardSet(StandardSet::Z);
            }
            2 => p.store_and_infer.swap(0, 1),
            3 => {
                p.store_and_infer.pop();
            }
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "corrupted_release").is_err());
    }
}

#[test]
fn object_release_rejects_a_future_definition() {
    let (mut run, compiler) = super::execute("have a R = 2\nrelease obj def a\n");
    run.statement_results.swap(0, 1);
    let error = compiler.compile_run(&run, "future_definition").unwrap_err();
    assert!(error.to_string().contains("ReleaseObj/DefinitionProducer"));
}

#[test]
fn object_release_citations_follow_ordered_publication() {
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    let (mut run, compiler) = super::execute("have a R = 2\nrelease obj def a\na $in R\n");
    let ids: Vec<_> = released(&mut run.statement_results[1])
        .store_and_infer
        .iter()
        .map(|store| store.primary_fact_id())
        .collect();
    {
        let prefix = SourcePosition::new(None, SourceOwner::Run(&run), 1);
        let release = SourcePosition::new(
            Some(&prefix),
            SourceOwner::Statement(&run.statement_results[1]),
            0,
        );
        for id in &ids {
            assert!(compiler.cited_fact_reference(*id, &release).is_err());
        }
        let first = SourcePosition {
            before: 1,
            ..release
        };
        assert!(compiler.cited_fact_reference(ids[0], &first).is_ok());
        assert!(compiler.cited_fact_reference(ids[1], &first).is_err());
        let complete = SourcePosition {
            before: 2,
            ..release
        };
        for id in &ids {
            assert!(compiler.cited_fact_reference(*id, &complete).is_ok());
        }
    }
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut run.statement_results[2] else {
        panic!("membership");
    };
    let proof = super::atomic_proof_mut(&mut p.verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) = &mut proof.searched_proof
    else {
        panic!("citation");
    };
    cite.cite_fact_id = ids[0];
    compiler.compile_run(&run, "published_citation").unwrap();
}

#[test]
fn object_release_keeps_local_definitions_and_facts_in_their_proof() {
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    let (run, compiler) =
        super::execute("thm local:\n    ? 1 = 1\n    have a R = 2\n    release obj def a\n1 = 1\n");
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &run.statement_results[0]
    else {
        panic!("theorem");
    };
    let ExecDefThmBodyProof::NonForall(body) = &p.body else {
        panic!("body");
    };
    let ExecStmtResult::ReleaseAndExpand(crate::execute::ExecReleaseAndExpandStmtResult::ObjDef(
        ExecReleaseObjDefStmtResult::Success(release),
    )) = &body.proof_steps[1]
    else {
        panic!("release");
    };
    let outside = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    for store in &release.store_and_infer {
        assert!(compiler
            .cited_fact_reference(store.primary_fact_id(), &outside)
            .is_err());
    }
    assert!(outside
        .visible_object_definition(|d| matches!(d, ExecDefinitionStmtResult::DefineObj(_)))
        .is_err());
    compiler.compile_run(&run, "local_release").unwrap();
}
