use crate::execute::{ExecDefTemplateStmtResult, ExecHaveFnEqualStmtResult};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::{
    EqualitySearchProofByObjectDefinition,
    by_template::result::EqualitySearchProofByTemplateObjectDefinition,
    by_fn_application::normalize_function_body::{FunctionBodyExpansionProof, FunctionBodySourceProof},
};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::SameIrProof;
use crate::prelude::*;

const SOURCES: &[&str] = &[
    include_str!("../../../lean/examples/template_real_translation/statement.lit"),
    include_str!("../../../lean/examples/template_guarded_scaling/statement.lit"),
    include_str!("../../../lean/examples/template_constant_function/statement.lit"),
    include_str!("../../../lean/examples/template_returned_function/statement.lit"),
    include_str!("../../../lean/examples/record_function_evaluation/statement.lit"),
    include_str!("../../../lean/examples/template_formula_composition/statement.lit"),
    include_str!("../../../lean/examples/template_real_to_complex/statement.lit"),
];

fn number() -> Obj {
    Obj::Literal(Literal::Number(Number::new("99".into())))
}

#[test]
fn template_return_replay_requires_declared_codomain_peers_and_matches() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::{
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty as Known,
        InFactSearchProofByKnownSpecialProperty as InKnown,
    };
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
        AnonymousFnBodyInReturnSetProof, FunctionSpaceObjWellDefinedProofByDef,
    };
    for mutation in 0..8 {
        let (mut run, compiler) = super::execute(SOURCES[5]);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
            ExecHaveFnEqualStmtResult::Success(function),
        )) = &mut run.statement_results[1]
        else {
            panic!("formula declaration")
        };
        let Some(DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(
                    FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(function),
                ),
            ..
        }) = function
            .anonymous_fn_well_defined
            .as_detailed_success_mut()
            .unwrap()
        else {
            panic!("formula WD")
        };
        let AnonymousFnBodyInReturnSetProof::CheckedMembership(member) =
            &mut function.body_in_ret_set
        else {
            panic!("return membership")
        };
        let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(Known::InFact(
            InKnown::TemplateApplicationInDeclaredCodomain(proof),
        )) = &mut super::atomic_proof_mut(member).searched_proof
        else {
            panic!("template declared return")
        };
        match mutation {
            0 => proof.declared_signature.ret_set = Box::new(Obj::StandardSet(StandardSet::Z)),
            1 => proof.applied_return_set = Obj::StandardSet(StandardSet::Z),
            2 => proof.instance.args[0] = number(),
            3 => proof.alternative_template_signature_matches.clear(),
            4 => proof.alternative_template_signature_matches[0].instance.args[0] = number(),
            5 => proof.function_equal.path.push((number(), number(), FactId::new(u64::MAX))),
            6 => proof.alternative_template_signature_matches[0].function_equal.path.push((number(), number(), FactId::new(u64::MAX))),
            _ => proof.alternative_signature_matches.push(
                crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::SignatureReturnMatchProof {
                    cite_signature_fact_id: FactId::new(u64::MAX),
                    return_set_match: EqualFactSearchedProof::ByTheyAreTheSame(TheyAreTheSameProof::SameIr(SameIrProof {})),
                }),
        }
        compiler
            .compile_run(&run, "bad_template_return")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn template_return_replay_requires_standard_superset_and_selected_signature() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::{
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty as Known,
        InFactSearchProofByKnownSpecialProperty as InKnown,
    };
    for mutation in 0..6 {
        let (mut run, compiler) = super::execute(SOURCES[6]);
        let atomic = super::atomic_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[1]).verify_result,
        );
        let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(Known::InFact(
            InKnown::TemplateApplicationInStandardSuperset(proof),
        )) = &mut atomic.searched_proof
        else {
            panic!("template standard return")
        };
        match mutation {
            0 => proof.target_set = StandardSet::R,
            1 => proof.declared_returns.clear(),
            2 => proof.declared_returns[0].source_set = StandardSet::Z,
            3 => {
                proof.declared_returns[0].declared_signature.ret_set =
                    Box::new(Obj::StandardSet(StandardSet::Z))
            }
            4 => proof.declared_returns[0].function = number(),
            _ => proof.declared_returns[0].function_equal.path.push((
                number(),
                number(),
                FactId::new(u64::MAX),
            )),
        }
        compiler
            .compile_run(&run, "bad_template_standard_return")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn template_function_replay_preserves_captures_guards_sets_and_returned_calls() {
    for source in SOURCES {
        let (run, compiler) = super::execute(source);
        let generated = compiler.compile_run(&run, "function_heads").expect(source);
        assert_eq!(
            generated,
            compiler.compile_run(&run, "function_heads").unwrap()
        );
    }
}

#[test]
fn template_function_replay_requires_the_original_declaration_and_publications() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(SOURCES[1]);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
            ExecDefTemplateStmtResult::Success(p),
        )) = &mut run.statement_results[0]
        else {
            panic!("template declaration")
        };
        match mutation {
            0 => {
                p.assumed_dom_facts.clear();
            }
            1 => {
                p.definition_facts.pop();
            }
            2 => {
                p.definition_facts[0].source_fact_id = FactId::new(u64::MAX);
            }
            3 => {
                p.definition_facts.swap(0, 1);
            }
            _ => {
                let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
                    ExecHaveFnEqualStmtResult::Success(body),
                )) = p.body.as_mut()
                else {
                    panic!("function body")
                };
                body.statement.equal_to_anonymous_fn.equal_to = Box::new(number());
            }
        }
        compiler
            .compile_run(&run, "bad_template_declaration")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn template_function_replay_requires_original_call_wd_and_template_guards() {
    for source in &SOURCES[..3] {
        for mutation in 0..6 {
            let (mut run, compiler) = super::execute(source);
            let p = super::equality_proof_mut(
                &mut super::fact_statement_mut(&mut run.statement_results[1]).verify_result,
            );
            let wd = &mut p.well_defined_proof.as_detailed_mut().unwrap().left;
            let DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::FnObj(call),
                ..
            } = wd.as_detailed_mut().unwrap()
            else {
                panic!("call WD")
            };
            match mutation {
                0 => {
                    call.child_obj_well_defined.pop();
                }
                1 => {
                    call.requirement_fact_verified.pop();
                }
                2 => {
                    call.child_obj_well_defined.swap(0, 1);
                }
                3 => {
                    let Some(FnObjDomainFnSetEvidence::TemplateDefinition { fn_set, .. }) =
                        &mut call.domain_fn_set
                    else {
                        panic!("template signature")
                    };
                    fn_set.ret_set = Box::new(Obj::StandardSet(StandardSet::Z));
                }
                4 => {
                    call.domain_fn_set = None;
                }
                _ => {
                    let DetailedObjWellDefinedProof::ByDef {
                        proof: ObjWellDefinedProofByDef::InstantiatedTemplateObj(instance),
                        ..
                    } = call.child_obj_well_defined[0].as_detailed_mut().unwrap()
                    else {
                        panic!("template instance WD")
                    };
                    instance.requirement_fact_verified.pop();
                }
            }
            compiler
                .compile_run(&run, "bad_template_call")
                .expect_err(&format!("mutation {mutation}"));
        }
    }
}

#[test]
fn template_function_replay_requires_each_recorded_normalization_step() {
    for source in &SOURCES[..3] {
        for mutation in 0..6 {
            let (mut run, compiler) = super::execute(source);
            let p = super::equality_proof_mut(
                &mut super::fact_statement_mut(&mut run.statement_results[1]).verify_result,
            );
            let EqualFactSearchedProof::ByObjectDefinition(
                EqualitySearchProofByObjectDefinition::ByTemplate(
                    EqualitySearchProofByTemplateObjectDefinition::HaveFnEqualApplication(proof),
                ),
            ) = &mut p.searched_proof
            else {
                panic!("selected template normalization")
            };
            if mutation == 0 {
                proof.normalization.expansions.clear();
            } else if mutation == 1 {
                proof.normalization.expanded_body = number();
            } else {
                let FunctionBodyExpansionProof::Anonymous(step) =
                    &mut proof.normalization.expansions[0]
                else {
                    panic!("anonymous beta")
                };
                match mutation {
                    2 => step.continued_body = number(),
                    3 => step.application = number(),
                    _ => {
                        let FunctionBodySourceProof::Template {
                            instance,
                            instantiated_function,
                            ..
                        } = &mut step.function_body
                        else {
                            panic!("template body source")
                        };
                        if mutation == 4 {
                            *instance = number();
                        } else {
                            instantiated_function.equal_to = Box::new(number());
                        }
                    }
                }
            }
            compiler
                .compile_run(&run, "bad_template_normalization")
                .expect_err(&format!("mutation {mutation}"));
        }
    }
}

#[test]
fn record_function_replay_requires_field_identity_tuple_path_and_substituted_wd() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::{
        EqualitySearchProofByFnApplicationObjectDefinition,
        by_parent_checked_beta::{ByParentCheckedBetaObjectDefinitionProof, ParentCheckedBetaFunctionBody},
        struct_field_value::StructTupleValueSource,
    };
    for mutation in 0..6 {
        let (mut run, compiler) = super::execute(SOURCES[4]);
        let p = super::equality_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[4]).verify_result,
        );
        let EqualFactSearchedProof::ByObjectDefinition(
            EqualitySearchProofByObjectDefinition::ByFnApplication(
                EqualitySearchProofByFnApplicationObjectDefinition::ParentCheckedBeta(
                    ByParentCheckedBetaObjectDefinitionProof::OneSide(beta),
                ),
            ),
        ) = &mut p.searched_proof
        else {
            panic!("recorded field beta")
        };
        if mutation == 5 {
            let EqualFactSearchedProof::ByClosedCalculation(calculation) =
                beta.residual_proof.as_mut()
            else {
                panic!("closed residual calculation")
            };
            calculation.values = ClosedValuePair::Rational {
                left: EvalRational::new(99, 1).unwrap(),
                right: EvalRational::new(99, 1).unwrap(),
            };
            compiler
                .compile_run(&run, "bad_field_calculation")
                .expect_err("changed closed certificate");
            continue;
        }
        let ParentCheckedBetaFunctionBody::ReturnedKnownFunctionApplication {
            receiver_function_body,
            application_well_defined,
            ..
        } = &mut beta.function_body
        else {
            panic!("returned field function")
        };
        let ParentCheckedBetaFunctionBody::StructField(field) = receiver_function_body.as_mut()
        else {
            panic!("field projection")
        };
        match mutation {
            0 => field.index = 0,
            1 => field.index = 2,
            2 => {
                let StructTupleValueSource::Known(tuple) = &mut field.source else {
                    panic!("stored tuple")
                };
                tuple.tuple_equal.path.clear();
            }
            3 => {
                let StructTupleValueSource::Known(tuple) = &mut field.source else {
                    panic!("stored tuple")
                };
                tuple.value.args.swap(0, 1);
            }
            _ => {
                let DetailedObjWellDefinedProof::ByDef { obj, .. } =
                    application_well_defined.as_detailed_mut().unwrap()
                else {
                    panic!("substituted call WD")
                };
                *obj = number();
            }
        }
        compiler
            .compile_run(&run, "bad_field_function")
            .expect_err(&format!("mutation {mutation}"));
    }
}
