use crate::prelude::*;

const SOURCE: &str = "prop shifted_interval(x R):\n    x + 1 >= 0\n    x + 1 <= 2\n";

fn predicate(result: &mut RunLitexCodeResult) -> &mut crate::execute::ExecDefPropStmtSuccessResult {
    match &mut result.statement_results[0] {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
            crate::execute::ExecDefPropStmtResult::Success(proof),
        )) => proof,
        _ => panic!("expected predicate"),
    }
}

#[test]
fn predicate_reuses_recorded_object_once() {
    let (mut result, compiler) = super::execute(SOURCE);
    let proof = predicate(&mut result);
    let id = proof.assumed_iff_facts[0].store_and_infer.formed_subjects[0].wd_id;
    assert!(proof.assumed_iff_facts[1]
        .store_and_infer
        .formed_subjects
        .iter()
        .all(|s| s.wd_id != id));
    let lean = compiler.compile_run(&result, "sharing").unwrap();
    assert_eq!(
        lean.matches(&format!("let _object_w{} :=", id.value()))
            .count(),
        1
    );
    assert_eq!(lean.matches("Litex.add ").count(), 1, "{lean}");
    assert!(lean.lines().count() <= 25, "{} lines", lean.lines().count());
}

#[test]
fn predicate_rejects_wrong_registration_subject_and_index() {
    for corrupt_index in [false, true] {
        let (mut result, compiler) = super::execute(SOURCE);
        let proof = predicate(&mut result);
        let registration = &mut proof.assumed_iff_facts[0].store_and_infer.formed_subjects[0];
        if corrupt_index {
            registration.argument_index = 20;
        } else {
            registration.wd_id = WellDefinednessId::new(u64::MAX);
        }
        assert!(compiler.compile_run(&result, "bad_registration").is_err());
    }
}

#[test]
fn predicate_does_not_publish_objects_outside_its_body() {
    let source =
        format!("{SOURCE}\n{SOURCE}").replacen("prop shifted_interval", "prop first_interval", 1);
    let (result, compiler) = super::execute(&source);
    let lean = compiler.compile_run(&result, "scopes").unwrap();
    assert_eq!(lean.matches("Litex.add ").count(), 2);
    assert_eq!(lean.matches("let _object_w").count(), 2);
}

#[test]
fn predicate_rejects_reordered_registrations() {
    let (mut result, compiler) = super::execute("prop matching(x, y R):\n    x + 1 = y + 1\n");
    let registrations = &mut predicate(&mut result).assumed_iff_facts[0]
        .store_and_infer
        .formed_subjects;
    assert_eq!(registrations.len(), 2);
    registrations.swap(0, 1);
    assert!(compiler.compile_run(&result, "reordered").is_err());
}

#[test]
fn predicate_reuses_guarded_function_and_its_output_certificate() {
    let source = "have fn inverse(x R: x != 0) R = 1 / x\n\
        prop bounded_inverse(x R):\n    x != 0\n    inverse(x) >= 0\n    inverse(x) <= 2\n";
    let (result, compiler) = super::execute(source);
    let lean = compiler.compile_run(&result, "guarded_sharing").unwrap();
    let body = lean.split("def prop_2 ").nth(1).unwrap();
    assert_eq!(body.matches("Litex.call ").count(), 1, "{body}");
    assert!(body.contains("let _object_w"));
}
