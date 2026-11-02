use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    AnonymousFnBodyInReturnSetProof, AnonymousFnObjWellDefinedProof,
    FnObjDomainFnSetEvidence, FunctionSpaceObjWellDefinedProofByDef,
    StructishObjWellDefinedProofByDef,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::{
    AtomicExceptEqualityFactSearchProofByKnownSpecialProperty as Known,
    InFactSearchProofByKnownSpecialProperty as InKnown,
};
use crate::execute::ExecHaveFnEqualStmtResult;
use crate::prelude::*;

const SOURCES: &[&str] = &[
    include_str!("../../../lean/examples/record_function_formula/statement.lit"),
    include_str!("../../../lean/examples/nested_record_function_formula/statement.lit"),
    include_str!("../../../lean/examples/guarded_record_function_formula/statement.lit"),
    include_str!("../../../lean/examples/record_function_complex_result/statement.lit"),
];

fn formula(run: &mut RunLitexCodeResult, index: usize) -> &mut AnonymousFnObjWellDefinedProof {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
        ExecHaveFnEqualStmtResult::Success(function),
    )) = &mut run.statement_results[index]
    else {
        panic!("formula declaration")
    };
    let Some(DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(
                proof,
            )),
        ..
    }) = function
        .anonymous_fn_well_defined
        .as_detailed_success_mut()
        .unwrap()
    else {
        panic!("formula WD")
    };
    proof
}

#[test]
fn record_projection_replays_nested_fields_guards_and_formula_substitution() {
    for source in SOURCES {
        let (run, compiler) = super::execute(source);
        let lean = compiler
            .compile_run(&run, "record_projections")
            .expect(source);
        assert_eq!(
            lean,
            compiler.compile_run(&run, "record_projections").unwrap()
        );
    }
}

#[test]
fn record_projection_retains_and_validates_each_original_path_step() {
    for mutation in 0..8 {
        let (mut run, compiler) = super::execute(SOURCES[1]);
        let body = formula(&mut run, 3);
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(call),
            ..
        } = body.body_well_defined.as_detailed_mut().unwrap()
        else {
            panic!("field call")
        };
        if mutation == 7 {
            let Some(FnObjDomainFnSetEvidence::AnonymousLiteral { fn_set }) =
                &mut call.domain_fn_set
            else {
                panic!("field signature")
            };
            fn_set.ret_set = Box::new(Obj::StandardSet(StandardSet::C));
        } else {
            let DetailedObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::Structish(StructishObjWellDefinedProofByDef::FieldAccess(
                        field,
                    )),
                ..
            } = call.child_obj_well_defined[0].as_detailed_mut().unwrap()
            else {
                panic!("projection WD")
            };
            assert_eq!(field.projection_steps.len(), 2);
            assert_eq!(
                field
                    .projection_steps
                    .iter()
                    .map(|s| s.field_index)
                    .collect::<Vec<_>>(),
                vec![0, 0]
            );
            assert_ne!(
                field.projection_steps[0].carrier,
                field.projection_steps[1].carrier
            );
            match mutation {
                0 => field.projection_steps.clear(),
                1 => {
                    field.projection_steps.pop();
                }
                2 => field.projection_steps.swap(0, 1),
                3 => field.projection_steps[0].field_index = usize::MAX,
                4 => field.projection_steps[0].carrier = field.projection_steps[1].carrier.clone(),
                5 => field.projection_steps[1].field_index = 1,
                6 => field.child_obj_well_defined.clear(),
                _ => unreachable!(),
            }
        }
        compiler
            .compile_run(&run, "bad_record_projection")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn record_projection_requires_field_domain_and_declared_return_evidence() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(SOURCES[2]);
        let body = formula(&mut run, 1);
        if mutation == 0 {
            body.assumed_dom_facts.clear();
        } else if mutation == 1 {
            let DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::FnObj(call),
                ..
            } = body.body_well_defined.as_detailed_mut().unwrap()
            else {
                panic!("guarded field call")
            };
            call.requirement_fact_verified.pop();
        } else {
            let AnonymousFnBodyInReturnSetProof::CheckedMembership(member) =
                &mut body.body_in_ret_set
            else {
                panic!("return member")
            };
            let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(Known::InFact(
                InKnown::FieldApplicationInDeclaredCodomain(proof),
            )) = &mut super::atomic_proof_mut(member).searched_proof
            else {
                panic!("declared field return")
            };
            match mutation {
                2 => proof.declared_signature.dom_facts.clear(),
                3 => proof.applied_return_set = Obj::StandardSet(StandardSet::C),
                _ => proof.declared_signature.ret_set = Box::new(Obj::StandardSet(StandardSet::C)),
            }
        }
        compiler
            .compile_run(&run, "bad_field_return")
            .expect_err(&format!("mutation {mutation}"));
    }
}

const GENERIC_SOURCES: &[&str] = &[
    include_str!("../../../lean/examples/generic_nested_binary_operation/statement.lit"),
    include_str!("../../../lean/examples/generic_nested_operation_tower/statement.lit"),
    include_str!("../../../lean/examples/generic_selected_operation/statement.lit"),
    include_str!("../../../lean/examples/generic_pointed_operation/statement.lit"),
    include_str!("../../../examples/wd/struct_field_instantiation.lit"),
];

#[test]
fn record_projection_instantiates_original_generic_field_constructors() {
    for source in GENERIC_SOURCES {
        let (run, compiler) = super::execute(source);
        let lean = compiler
            .compile_run(&run, "generic_record_projections")
            .expect(source);
        assert_eq!(
            lean,
            compiler
                .compile_run(&run, "generic_record_projections")
                .unwrap()
        );
        assert!(!lean.contains("axiom ") && !lean.contains("sorry"));
    }
}

#[test]
fn record_projection_rejects_changed_intermediate_header_and_declaration_wd() {
    for mutation in 0..6 {
        let (mut run, compiler) = super::execute(GENERIC_SOURCES[0]);
        if mutation < 3 {
            let forall = super::forall_proof_mut(&mut run.statement_results[2]);
            let atomic = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
            let wd = &mut atomic
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .well_defined_of_each_parameter[0];
            let DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::FnObj(call),
                ..
            } = wd.as_detailed_mut().unwrap()
            else {
                panic!("field call")
            };
            let DetailedObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::Structish(StructishObjWellDefinedProofByDef::FieldAccess(
                        field,
                    )),
                ..
            } = call.child_obj_well_defined[0].as_detailed_mut().unwrap()
            else {
                panic!("field projection")
            };
            match mutation {
                0 => field.projection_steps[1].carrier.params.clear(),
                1 => field.projection_steps[1].carrier.params[0] = Obj::StandardSet(StandardSet::R),
                _ => field.projection_steps[1].field_index = 0,
            }
        } else {
            let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStruct(
                crate::execute::ExecDefStructStmtResult::Success(declaration),
            )) = &mut run.statement_results[1]
            else {
                panic!("outer declaration")
            };
            let DetailedObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::Structish(StructishObjWellDefinedProofByDef::StructObj(
                        wd,
                    )),
                ..
            } = declaration.field_scope.fields[0]
                .well_defined
                .as_detailed_mut()
                .unwrap()
            else {
                panic!("original field constructor")
            };
            match mutation {
                3 => wd.requirement_fact_verified.clear(),
                4 => wd.child_obj_well_defined.clear(),
                _ => super::replace_wd_subject(
                    &mut wd.child_obj_well_defined[0],
                    Obj::StandardSet(StandardSet::R),
                ),
            }
        }
        compiler
            .compile_run(&run, "bad_generic_field")
            .expect_err(&format!("mutation {mutation}"));
    }
}
