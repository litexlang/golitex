use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::fn_sets_alpha_equal;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::*;
use crate::execute::{
    ExecDefTemplateStmtResult, ExecHaveFnByForallExistUniqueStmtResult, ExecHaveFnEqualStmtResult,
};
use crate::prelude::*;

const SOURCES: &[&str] = &[
    include_str!("../../../lean/examples/selected_template_real_composition/statement.lit"),
    include_str!("../../../lean/examples/selected_template_complex_composition/statement.lit"),
    include_str!("../../../lean/examples/selected_template_field_composition/statement.lit"),
    include_str!("../../../lean/examples/selected_template_binary_composition/statement.lit"),
];

fn formula(run: &mut RunLitexCodeResult) -> &mut AnonymousFnObjWellDefinedProof {
    let p = run
        .statement_results
        .iter_mut()
        .find_map(|s| match s {
            ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
                ExecHaveFnEqualStmtResult::Success(p),
            )) => Some(p),
            _ => None,
        })
        .unwrap();
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(
                p,
            )),
        ..
    } = p
        .anonymous_fn_well_defined
        .as_detailed_success_mut()
        .unwrap()
        .unwrap()
    else {
        panic!()
    };
    p
}

fn template(run: &mut RunLitexCodeResult) -> &mut crate::execute::ExecDefTemplateStmtSuccessResult {
    run.statement_results
        .iter_mut()
        .find_map(|s| match s {
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
                ExecDefTemplateStmtResult::Success(p),
            )) => Some(p),
            _ => None,
        })
        .unwrap()
}

#[test]
fn selected_template_compositions_replay_real_complex_record_and_binary_bodies() {
    for source in SOURCES {
        let (run, compiler) = super::execute(source);
        let output = compiler
            .compile_run(&run, "selected_compositions")
            .expect(source);
        assert_eq!(
            output,
            compiler.compile_run(&run, "selected_compositions").unwrap()
        );
    }
}

#[test]
fn template_guard_fact_identity_does_not_change_its_function_signature() {
    let (mut run, compiler) = super::execute(SOURCES[0]);
    compiler.compile_run(&run, "before").unwrap();
    let p = formula(&mut run);
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(call),
        ..
    } = p.body_well_defined.as_detailed_mut().unwrap()
    else {
        panic!()
    };
    let Some(FnObjDomainFnSetEvidence::TemplateDefinition { fn_set, .. }) = &mut call.domain_fn_set
    else {
        panic!()
    };
    let original = fn_set.clone();
    let QuantifierFreeFact::AtomicFact(AtomicFact::NotEqualFact(guard)) = &mut fn_set.dom_facts[0]
    else {
        panic!()
    };
    guard.fact_id = FactId::new(u64::MAX);
    assert_ne!(*fn_set, original);
    assert!(fn_sets_alpha_equal(fn_set, &original));
    compiler.compile_run(&run, "after").unwrap();
}

#[test]
fn selected_template_composition_requires_exact_call_wd_and_guard_evidence() {
    for mutation in 0..7 {
        let (mut run, compiler) = super::execute(SOURCES[0]);
        compiler.compile_run(&run, "baseline").unwrap();
        let p = formula(&mut run);
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(call),
            ..
        } = p.body_well_defined.as_detailed_mut().unwrap()
        else {
            panic!()
        };
        let Some(FnObjDomainFnSetEvidence::TemplateDefinition { fn_set, .. }) =
            &mut call.domain_fn_set
        else {
            panic!()
        };
        match mutation {
            0 => fn_set.dom_facts.clear(),
            1 => fn_set.ret_set = Box::new(Obj::StandardSet(StandardSet::N)),
            2 => {
                fn_set.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::N))
            }
            3 => {
                call.requirement_fact_verified.pop();
            }
            4 => call.requirement_fact_verified.swap(0, 1),
            5 => {
                let DetailedObjWellDefinedProof::ByDef {
                    proof: ObjWellDefinedProofByDef::InstantiatedTemplateObj(instance),
                    ..
                } = call.child_obj_well_defined[0].as_detailed_mut().unwrap()
                else {
                    panic!()
                };
                instance.requirement_fact_verified.pop();
            }
            6 => call.child_obj_well_defined.swap(0, 1),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_call")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn selected_template_callee_requires_original_property_formation_and_publication() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(SOURCES[3]);
        compiler.compile_run(&run, "baseline").unwrap();
        let p = template(&mut run);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByForallExistUnique(
            ExecHaveFnByForallExistUniqueStmtResult::Success(body),
        )) = p.body.as_mut()
        else {
            panic!()
        };
        let FactWellDefinedProof::ForallFact(wd) = &mut body.property_well_defined else {
            panic!()
        };
        match mutation {
            0 => wd.as_detailed_mut().unwrap().then.clear(),
            1 => wd
                .as_detailed_mut()
                .unwrap()
                .introduced_params
                .defined_params
                .store_and_infer_results
                .clear(),
            2 => p.definition_facts[1].source_fact_id = p.definition_facts[0].source_fact_id,
            3 => {
                let StoreFactResult::ForallFact(stored) =
                    &mut p.definition_facts[1].store_and_infer.store
                else {
                    panic!()
                };
                stored.fact.typed_parameters.groups.swap(0, 1);
            }
            4 => p
                .introduced_params
                .defined_params
                .store_and_infer_results
                .clear(),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_publication")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn template_constructor_publication_is_visible_only_after_its_declaration() {
    let (run, compiler) = super::execute(SOURCES[3]);
    compiler.compile_run(&run, "baseline").unwrap();
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
        ExecDefTemplateStmtResult::Success(p),
    )) = &run.statement_results[1]
    else {
        panic!()
    };
    let id = p.definition_facts[1].store_and_infer.primary_fact_id();
    let before = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    let after = SourcePosition {
        before: 2,
        ..before
    };
    assert!(before.visible_template_publication(id).is_none());
    assert!(after.visible_template_publication(id).is_some());
}
