use crate::execute::{ExecDefTemplateStmtResult, ExecDefTemplateStmtSuccessResult, ExecObtainObjFromAtomicFactStmtResult};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::{
    EqualitySearchProofByObjectDefinition,
    by_template::result::EqualitySearchProofByTemplateObjectDefinition,
};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
use crate::prelude::*;

const SOURCES: &[&str] = &[
    include_str!("../../../lean/examples/template_piecewise_declared_type/statement.lit"),
    include_str!("../../../lean/examples/template_piecewise_guarded/statement.lit"),
    include_str!("../../../lean/examples/template_obtained_function/statement.lit"),
    include_str!("../../../lean/examples/template_obtained_value/statement.lit"),
];

fn template(run: &mut RunLitexCodeResult) -> &mut ExecDefTemplateStmtSuccessResult {
    run.statement_results
        .iter_mut()
        .find_map(|statement| match statement {
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
                ExecDefTemplateStmtResult::Success(p),
            )) => Some(p),
            _ => None,
        })
        .unwrap()
}

#[test]
fn template_definition_bodies_replay_cases_witnesses_and_original_guards() {
    for source in SOURCES {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "template_bodies").expect(source);
        assert_eq!(lean, compiler.compile_run(&run, "template_bodies").unwrap());
        assert!(!lean.contains("sorry") && !lean.contains("axiom "));
    }
}

#[test]
fn template_case_publications_preserve_both_quantified_headers() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(SOURCES[1]);
        let declaration = template(&mut run);
        let StoreFactResult::ForallFact(published) =
            &mut declaration.definition_facts[1].store_and_infer.store
        else {
            panic!("published case")
        };
        match mutation {
            0 => {
                published.fact.typed_parameters.groups.pop();
            }
            1 => published.fact.dom_facts.clear(),
            2 => {
                published.fact.dom_facts.pop();
            }
            3 => {
                published
                    .fact
                    .typed_parameters
                    .groups
                    .last_mut()
                    .unwrap()
                    .param_type = ParamType::Obj(Obj::StandardSet(StandardSet::C))
            }
            4 => {
                let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(equal)) =
                    &mut published.fact.then_facts[0]
                else {
                    panic!("case equality")
                };
                equal.right = super::number_object("99");
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_case_publication")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn template_case_unfold_requires_selected_branch_and_residual_endpoints() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(SOURCES[1]);
        let fact = super::fact_statement_mut(run.statement_results.last_mut().unwrap());
        let equal = super::equality_proof_mut(&mut fact.verify_result);
        let EqualFactSearchedProof::ByObjectDefinition(
            EqualitySearchProofByObjectDefinition::ByTemplate(
                EqualitySearchProofByTemplateObjectDefinition::HaveFnEqualCaseByCaseApplication(
                    proof,
                ),
            ),
        ) = &mut equal.searched_proof
        else {
            panic!("template case unfold")
        };
        match mutation {
            0 => proof.matched_case_index = usize::MAX,
            1 => proof.matched_case_index = 0,
            2 => proof.expanded_body = super::number_object("99"),
            3 => {
                super::equality_proof_mut(&mut proof.residual_equal)
                    .fact
                    .right = super::number_object("99")
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_case_unfold")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn template_case_calls_require_instance_and_application_evidence() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(SOURCES[1]);
        let fact = super::fact_statement_mut(run.statement_results.last_mut().unwrap());
        let equal = super::equality_proof_mut(&mut fact.verify_result);
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(call),
            ..
        } = equal
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .left
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("call WD")
        };
        match mutation {
            0 => {
                call.child_obj_well_defined.pop();
            }
            1 => call.child_obj_well_defined.swap(0, 1),
            2 => {
                let Some(FnObjDomainFnSetEvidence::TemplateDefinition { fn_set, .. }) =
                    &mut call.domain_fn_set
                else {
                    panic!("template signature")
                };
                fn_set.ret_set = Box::new(Obj::StandardSet(StandardSet::N));
            }
            3 => {
                let DetailedObjWellDefinedProof::ByDef {
                    proof: ObjWellDefinedProofByDef::InstantiatedTemplateObj(instance),
                    ..
                } = call.child_obj_well_defined[0].as_detailed_mut().unwrap()
                else {
                    panic!("instance WD")
                };
                instance.requirement_fact_verified.pop();
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_case_call")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn template_obtain_requires_original_witness_stores_and_publication() {
    for mutation in 0..2 {
        let (mut run, compiler) = super::execute(SOURCES[2]);
        let declaration = template(&mut run);
        if mutation == 0 {
            declaration.definition_facts[0].source_fact_id = FactId::new(u64::MAX);
        } else {
            let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::ObtainObjFromAtomicFact(
                    ExecObtainObjFromAtomicFactStmtResult::Success(body),
                ),
            )) = declaration.body.as_mut()
            else {
                panic!("obtain body")
            };
            body.store_and_infer_result.store_and_infer_results.pop();
        }
        compiler
            .compile_run(&run, "bad_template_witness")
            .expect_err(&format!("mutation {mutation}"));
    }
}
