use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_by_stmt::{ExecReleaseThmStmtSuccess, ExecReleaseThmStmtResult};
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
use crate::prelude::*;

const LITERAL: &str = include_str!("../../../lean/examples/struct_member_literal/statement.lit");
const GENERIC: &str = include_str!("../../../lean/examples/struct_member_cartesian/statement.lit");

fn invocation(run: &mut RunLitexCodeResult) -> &mut ExecReleaseThmStmtSuccess {
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(p),
    )) = &mut run.statement_results[1]
    else {
        panic!("original structure release")
    };
    p
}

#[test]
fn struct_member_replays_literal_generic_and_selected_contracts() {
    let selected = LITERAL.replace(
        "release thm struct_member((1, 2), &PlanarCoordinate)",
        "by thm struct_member((1, 2), &PlanarCoordinate) => (1, 2) $in &PlanarCoordinate",
    );
    for source in [LITERAL, GENERIC, &selected] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "struct_member").unwrap();
        assert_eq!(output, compiler.compile_run(&run, "struct_member").unwrap());
        assert!(!output.contains("sorry") && !output.contains("axiom "));
    }
}

#[test]
fn struct_member_requires_original_arguments_premise_store_and_conclusion_wd() {
    for change in ["args", "proof", "store", "wd", "subject", "type_stage"] {
        let (mut run, compiler) = super::execute(LITERAL);
        let p = invocation(&mut run);
        match change {
            "args" => p.builtin.as_mut().unwrap().arguments.swap(0, 1),
            "proof" => p.dom_proofs.clear(),
            "store" => p.dom_stores.clear(),
            "wd" => p.conclusions_wd.clear(),
            "type_stage" => std::mem::swap(&mut p.type_proofs, &mut p.dom_proofs),
            _ => {
                let Fact::AtomicFact(AtomicFact::InFact(f)) =
                    &mut p.builtin.as_mut().unwrap().requirements[0]
                else {
                    panic!()
                };
                f.set = Obj::StandardSet(StandardSet::R);
            }
        }
        compiler
            .compile_run(&run, change)
            .expect_err("retain the checked structural membership stages");
    }
}

#[test]
fn struct_member_cannot_discard_original_coordinate_or_constructor_evidence() {
    for change in ["coordinate", "order", "formation"] {
        let (mut run, compiler) = super::execute(LITERAL);
        let p = super::atomic_proof_mut(&mut invocation(&mut run).dom_proofs[0]);
        if change == "formation" {
            p.well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .well_defined_of_each_parameter
                .clear();
        } else {
            let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                    InFactSearchProofByBuiltinRule::StructObjMembership(p),
                ),
            ) = &mut p.searched_proof
            else {
                panic!("original coordinate membership proof")
            };
            if change == "coordinate" {
                p.carrier_obligations.pop();
            } else {
                p.carrier_obligations.swap(0, 1);
            }
        }
        compiler
            .compile_run(&run, change)
            .expect_err("identity release cannot replace original checked fields");
    }
}

#[test]
fn struct_member_same_id_is_visible_only_after_its_original_membership_proof() {
    let (mut run, compiler) = super::execute(LITERAL);
    let p = invocation(&mut run);
    let id = p.dom_stores[0].primary_fact_id();
    assert_eq!(id, p.stored[0].primary_fact_id());
    let root = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    let stmt = SourcePosition::new(
        Some(&root),
        SourceOwner::Statement(&run.statement_results[1]),
        0,
    );
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(p),
    )) = &run.statement_results[1]
    else {
        panic!()
    };
    let before = SourcePosition::new(Some(&stmt), SourceOwner::ThmRelease(p), 0);
    assert!(before.visible_fact(id, &compiler.runtime).is_err());
    let after = SourcePosition {
        before: 1,
        ..before
    };
    assert_eq!(
        after.visible_fact(id, &compiler.runtime).unwrap().1,
        format!("h_{}", id.value())
    );
}

#[test]
fn struct_member_cannot_prove_its_original_premise_by_citing_the_future_release() {
    let (mut run, compiler) = super::execute(LITERAL);
    let p = invocation(&mut run);
    let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
    super::atomic_proof_mut(&mut p.dom_proofs[0]).searched_proof =
        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(
            AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
                cite_fact_id: future,
                why_parameters_of_known_fact_are_equal_to_givens: Vec::new(),
            },
        );
    compiler
        .compile_run(&run, "future")
        .expect_err("same-ID contract must not authorize circular membership");
}
