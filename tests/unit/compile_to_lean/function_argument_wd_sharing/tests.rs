use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjObjWellDefinedProof;
use crate::execute::ExecHaveFnEqualStmtResult;
use crate::prelude::*;

const SOURCE: &str = include_str!("../../../../examples/wd/repeated_function_argument.lit");

fn call(result: &mut RunLitexCodeResult) -> &mut FnObjObjWellDefinedProof {
    let forall = super::forall_proof_mut(&mut result.statement_results[2]);
    let equality = super::equality_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(call),
        ..
    } = (&mut equality.well_defined_proof.as_detailed_mut().unwrap().left)
        .as_detailed_mut()
        .unwrap()
    else {
        panic!("original dot WD")
    };
    call
}

#[test]
fn function_argument_wd_sharing_records_one_producer_and_three_references() {
    let (mut result, compiler) = super::execute(SOURCE);
    let call = call(&mut result);
    let scope = call.argument_scope.as_ref().expect("candidate owner");
    assert_eq!(scope.formed_children.len(), 1);
    let formed = &scope.formed_children[0];
    assert_eq!(formed.child_index, 0);
    let first = &call.child_obj_well_defined[0];
    assert!(matches!(
        (first.as_ref()).as_detailed().unwrap(),
        DetailedObjWellDefinedProof::ByDef { .. }
    ));
    assert!(
        scope
            .local_env
            .well_defined_objects
            .wd_id_to_object
            .get(&formed.wd_id)
            == Some(first.obj())
    );
    assert!(
        matches!((call.child_obj_well_defined[1].as_ref()).as_detailed().unwrap(), DetailedObjWellDefinedProof::ByKnown { wd_id, .. } if *wd_id == formed.wd_id)
    );
    for requirement in &call.requirement_fact_verified {
        let VerifyFactResult::AtomicExceptEquality(r) = requirement else {
            panic!("membership")
        };
        let VerifyAtomicExceptEqualityFactResult::Success(r) = r.as_ref() else {
            panic!("checked membership")
        };
        assert!(
            matches!((&r.well_defined_proof.detailed_ref().well_defined_of_each_parameter[0]).as_detailed().unwrap(), DetailedObjWellDefinedProof::ByKnown { wd_id, .. } if *wd_id == formed.wd_id)
        );
    }
    assert!(compiler
        .runtime
        .well_defined_visible_in_stack(first.obj())
        .is_none());
    let output = compiler
        .compile_run(&result, "shared_function_argument")
        .expect("replay scoped IDs");
    assert!(output.contains("let _object_w"));
}

#[test]
fn function_argument_wd_sharing_rejects_missing_scope() {
    let (mut result, compiler) = super::execute(SOURCE);
    call(&mut result).argument_scope = None;
    let error = compiler
        .compile_run(&result, "missing_argument_owner")
        .unwrap_err();
    assert_eq!(error.route, "WdId/Resolution");
}

#[test]
fn function_argument_wd_sharing_rejects_forward_reference() {
    let (mut result, compiler) = super::execute(SOURCE);
    let call = call(&mut result);
    let wd_id = call.argument_scope.as_ref().unwrap().formed_children[0].wd_id;
    let obj = call.child_obj_well_defined[0].obj().clone();
    call.child_obj_well_defined[0] = Box::new(
        crate::execute::execute_fact_stmt::ObjWellDefinedProof::Detailed(Box::new(
            DetailedObjWellDefinedProof::ByKnown { obj, wd_id },
        )),
    );
    let error = compiler
        .compile_run(&result, "forward_argument_reference")
        .unwrap_err();
    assert_eq!(error.route, "WD/FnObj/ForwardReference");
}

#[test]
fn function_argument_wd_sharing_rejects_missing_registration() {
    let (mut result, compiler) = super::execute(SOURCE);
    call(&mut result)
        .argument_scope
        .as_mut()
        .unwrap()
        .formed_children
        .clear();
    let error = compiler
        .compile_run(&result, "missing_argument_producer")
        .unwrap_err();
    assert_eq!(error.route, "WD/FnObj/Registration");
}

#[test]
fn function_argument_wd_sharing_rejects_mismatched_id_subject() {
    let (mut result, compiler) = super::execute(SOURCE);
    let scope = call(&mut result).argument_scope.as_mut().unwrap();
    let id = scope.formed_children[0].wd_id;
    scope
        .local_env
        .well_defined_objects
        .wd_id_to_object
        .insert(id, Obj::StandardSet(StandardSet::R));
    let error = compiler
        .compile_run(&result, "wrong_argument_subject")
        .unwrap_err();
    assert_eq!(error.route, "WD/ByKnown");
}

#[test]
fn function_argument_wd_sharing_keeps_failed_candidates_isolated_and_guards_checked() {
    let source = "have fn step(x R) R = x + 1\nhave fn add(x, y R) R = x + y\nhave fn guarded(x, y R: y != 0) R = x / y\nadd(step(-1), step(-1)) = 0\n";
    let (result, compiler) = super::execute(source);
    let signature = |index: usize| {
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
            ExecHaveFnEqualStmtResult::Success(definition),
        )) = &result.statement_results[index]
        else {
            panic!("function definition")
        };
        definition.statement.equal_to_anonymous_fn.body.clone()
    };
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(fact)) = &result.statement_results[3]
    else {
        panic!("checked application")
    };
    let VerifyFactResult::Equality(equality) = &fact.verify_result else {
        panic!("equality")
    };
    let VerifyEqualityResult::Success(equality) = equality.as_ref() else {
        panic!("proved")
    };
    let Obj::FnObj(application) = equality.well_defined_proof.detailed_ref().left.obj() else {
        panic!("call")
    };
    let argument = application.body[0][0].as_ref();
    let mut runtime = compiler.runtime;
    assert!(runtime.well_defined_visible_in_stack(argument).is_none());

    let rejected = runtime
        .try_verify_fn_obj_against_fn_set(application, &signature(2), VerifyState::top_level())
        .expect("candidate check")
        .err()
        .expect("zero denominator must fail");
    let old_id = rejected.scope.formed_children[0].wd_id;
    assert!(rejected
        .stages
        .detailed_stages()
        .unwrap()
        .requirement_fact_verified
        .last()
        .unwrap()
        .is_failed());
    assert!(
        rejected
            .scope
            .local_env
            .well_defined_objects
            .wd_id_to_object
            .get(&old_id)
            == Some(argument)
    );
    assert!(runtime.well_defined_visible_in_stack(argument).is_none());

    let accepted = runtime
        .try_verify_fn_obj_against_fn_set(application, &signature(1), VerifyState::top_level())
        .expect("next candidate check")
        .ok()
        .expect("addition accepts zero");
    let new_id = accepted.scope.formed_children[0].wd_id;
    assert_ne!(old_id, new_id);
    assert!(matches!(
        (&accepted
            .stages
            .detailed_stages()
            .unwrap()
            .child_obj_well_defined[0])
            .as_detailed_success()
            .unwrap(),
        Some(DetailedObjWellDefinedProof::ByDef { .. })
    ));
    assert!(
        matches!((&accepted.stages.detailed_stages().unwrap().child_obj_well_defined[1]).as_detailed_success().unwrap(), Some(DetailedObjWellDefinedProof::ByKnown { wd_id, .. }) if *wd_id == new_id)
    );
    assert!(runtime.well_defined_visible_in_stack(argument).is_none());

    let failed_run = runtime
        .run_litex_code("guarded(step(-1), step(-1)) = 0\n")
        .unwrap();
    assert!(!failed_run.success && failed_run.session_error.is_none());
    let json = crate::json_output::project_run_detailed(&failed_run, &runtime, "file", None)
        .stringify_pretty();
    assert!(json.contains("\"argument_scope\""));
    assert!(json.contains("\"formed_children\""));
    assert!(runtime.well_defined_visible_in_stack(argument).is_none());
}
