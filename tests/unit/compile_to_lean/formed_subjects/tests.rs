use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::prelude::*;

const SOURCE: &str = "have a R\n$is_set(a + 1)\n$is_set(a + 1)\n";

fn fact(statement: &ExecStmtResult) -> &ExecFactStmtSuccessResult {
    match statement {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) => proof,
        _ => panic!("fact statement"),
    }
}

fn fact_mut(statement: &mut ExecStmtResult) -> &mut ExecFactStmtSuccessResult {
    match statement {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) => proof,
        _ => panic!("fact statement"),
    }
}

#[test]
fn formed_subjects_capture_registration_once_and_reuse_its_id() {
    let (result, compiler) = super::execute(SOURCE);
    let first = fact(&result.statement_results[1]);
    let second = fact(&result.statement_results[2]);
    assert_eq!(first.store_and_infer_result.formed_subjects.len(), 1);
    assert!(second.store_and_infer_result.formed_subjects.is_empty());
    let registration = &first.store_and_infer_result.formed_subjects[0];
    assert_eq!(registration.argument_index, 0);
    let VerifyFactResult::AtomicExceptEquality(atomic) = &second.verify_result else {
        panic!("atomic result")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(atomic) = atomic.as_ref() else {
        panic!("successful atomic")
    };
    let ObjWellDefinedProof::ByKnown { wd_id, .. } =
        &atomic.well_defined_proof.well_defined_of_each_parameter[0]
    else {
        panic!("original cached reference")
    };
    assert_eq!(*wd_id, registration.wd_id);
    let output = compiler.compile_run(&result, "formed_subjects").unwrap();
    let name = format!("_object_w{}", wd_id.value());
    assert_eq!(
        output.matches(&format!("noncomputable def {name}")).count(),
        1
    );
    let last = output.rsplit_once("\ntheorem ").unwrap().1;
    assert!(last.contains(&name));
    assert!(
        !last.contains("Litex.add "),
        "subsequent use must not reconstruct addition"
    );
    assert!(last.lines().count() <= 20);
}

#[test]
fn formed_subjects_references_respect_original_prefix() {
    let (result, _) = super::execute(SOURCE);
    let first = fact(&result.statement_results[1]);
    let registration = &first.store_and_infer_result.formed_subjects[0];
    let object =
        super::super::compile_fact_stmt_result::compile_formed_subjects::formed_subject_proof(
            &first.verify_result,
            registration.argument_index,
        )
        .unwrap()
        .unwrap()
        .obj();
    let before = SourcePosition::new(None, SourceOwner::Run(&result), 1);
    assert!(before
        .registered_wd_reference(object, Some(registration.wd_id))
        .unwrap()
        .is_none());
    let after = SourcePosition::new(None, SourceOwner::Run(&result), 2);
    assert!(after
        .registered_wd_reference(object, Some(registration.wd_id))
        .unwrap()
        .is_some());
    assert!(after
        .registered_wd_reference(object, Some(WellDefinednessId::new(u64::MAX)))
        .unwrap()
        .is_none());
}

#[test]
fn formed_subjects_project_certified_children_without_inventing_wd_ids() {
    let (result, _) = super::execute("have a R\n$is_set((a + 1) * (a + 2))\n$is_set(a + 3)\n");
    let first = fact(&result.statement_results[1]);
    let registration = &first.store_and_infer_result.formed_subjects[0];
    let root =
        super::super::compile_fact_stmt_result::compile_formed_subjects::formed_subject_proof(
            &first.verify_result,
            registration.argument_index,
        )
        .unwrap()
        .unwrap();
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = root.obj() else {
        panic!("original product");
    };
    let before = SourcePosition::new(None, SourceOwner::Run(&result), 1);
    let after = SourcePosition::new(None, SourceOwner::Run(&result), 2);
    assert!(before
        .registered_wd_reference(&product.left, None)
        .unwrap()
        .is_none());
    let left = after
        .registered_wd_reference(&product.left, None)
        .unwrap()
        .unwrap();
    let right = after
        .registered_wd_reference(&product.right, None)
        .unwrap()
        .unwrap();
    assert!(left.ends_with(".val.left"));
    assert!(right.ends_with(".val.right"));
    assert!(left.contains(&format!("_object_w{}", registration.wd_id.value())));
    // A child's projection is not a registration under its parent's WD id.
    assert!(after
        .registered_wd_reference(&product.left, Some(registration.wd_id))
        .unwrap()
        .is_none());
    let later = fact(&result.statement_results[2]);
    let other =
        super::super::compile_fact_stmt_result::compile_formed_subjects::formed_subject_proof(
            &later.verify_result,
            0,
        )
        .unwrap()
        .unwrap();
    assert!(after
        .registered_wd_reference(other.obj(), None)
        .unwrap()
        .is_none());
}

#[test]
fn formed_subjects_reject_invalid_original_argument_index() {
    let (mut result, compiler) = super::execute(SOURCE);
    fact_mut(&mut result.statement_results[1])
        .store_and_infer_result
        .formed_subjects[0]
        .argument_index = 10;
    assert_eq!(
        compiler
            .compile_run(&result, "bad_registration")
            .unwrap_err()
            .route,
        "WD/Registration"
    );
}

#[test]
fn formed_subjects_reject_missing_registered_id() {
    let (mut result, compiler) = super::execute(SOURCE);
    fact_mut(&mut result.statement_results[1])
        .store_and_infer_result
        .formed_subjects[0]
        .wd_id = WellDefinednessId::new(u64::MAX);
    assert_eq!(
        compiler
            .compile_run(&result, "missing_registration")
            .unwrap_err()
            .route,
        "WdId/Resolution"
    );
}

#[test]
fn formed_subjects_skip_identifiers_and_duplicate_atomic_arguments() {
    let (result, _) = super::execute("have a R\na = a\na + 1 = a + 1\n");
    assert!(fact(&result.statement_results[1])
        .store_and_infer_result
        .formed_subjects
        .is_empty());
    let registrations = &fact(&result.statement_results[2])
        .store_and_infer_result
        .formed_subjects;
    assert_eq!(registrations.len(), 1);
    assert_eq!(registrations[0].argument_index, 0);
}

#[test]
fn formed_subjects_keep_local_constructors_inside_their_proof() {
    let source =
        "claim:\n    ? 1 = 1\n    $is_set(1 + 1)\n    $is_set(1 + 1)\n    1 = 1\n$is_set(1 + 1)\n";
    let (result, compiler) = super::execute(source);
    let output = compiler
        .compile_run(&result, "closed_construction")
        .unwrap();
    let local = output
        .lines()
        .find_map(|line| line.trim().strip_prefix("let _object_w"))
        .unwrap()
        .split_whitespace()
        .next()
        .unwrap();
    let local = format!("_object_w{local}");
    let outer = output.rsplit_once("\ntheorem ").unwrap().1;
    assert!(!outer
        .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
        .any(|name| name == local));
    assert!(
        output.contains("noncomputable def _object_w"),
        "the outer construction has its own producer"
    );
}

#[test]
fn formed_subjects_reuse_a_preceding_forall_conclusion() {
    let (result, compiler) =
        super::execute("forall a R:\n    $is_set(a + 1)\n    $is_set(a + 1)\n");
    let output = compiler
        .compile_run(&result, "forall_construction")
        .unwrap();
    assert!(output.contains("let _object_w"));
    assert!(output.contains("Litex.IsSet _atomic_wd"));
    assert!(output.contains(" := _object_w"));
}
