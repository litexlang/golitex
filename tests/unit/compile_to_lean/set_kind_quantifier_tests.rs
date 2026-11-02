use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_by_stmt::{ExecByContraStmtResult, ExecByStmtResult};
use crate::execute::{
    ExecDefTemplateStmtResult, ExecObtainObjFromExistFactStmtResult,
    ExecWitnessExistFactStmtResult, ExecWitnessExistFactStmtSuccessResult, ExecWitnessStmtResult,
    ObtainExistVerifySuccess,
};
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferExistUniqueFactResult, InferNotExistFactResult, InferResult,
};

const SOURCES: &[&str] = &[
    include_str!("../../../lean/examples/unique_empty_finite_set/statement.lit"),
    include_str!("../../../lean/examples/unique_real_nonempty_set/statement.lit"),
    include_str!("../../../lean/examples/unique_finite_point/statement.lit"),
    include_str!("../../../lean/examples/unique_finite_copy/statement.lit"),
    include_str!("../../../lean/examples/incompatible_set_kind_equalities/statement.lit"),
    include_str!("../../../lean/examples/template_unique_finite_copy/statement.lit"),
    include_str!("../../../lean/examples/template_unique_nonempty_copy/statement.lit"),
];

fn witness(run: &mut RunLitexCodeResult) -> &mut ExecWitnessExistFactStmtSuccessResult {
    let ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessExistFact(
        ExecWitnessExistFactStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!("unique witness")
    };
    p
}

#[test]
fn set_kind_quantifiers_replay_unique_witnesses_obtain_theorems_and_templates() {
    for source in SOURCES {
        let (run, compiler) = super::execute(source);
        let lean = compiler
            .compile_run(&run, "set_kind_quantifiers")
            .expect(source);
        assert_eq!(
            lean,
            compiler.compile_run(&run, "set_kind_quantifiers").unwrap()
        );
    }
}

#[test]
fn set_kind_uniqueness_preserves_the_original_candidate_kinds_and_order() {
    for source in &SOURCES[..3] {
        for mutation in 0..5 {
            let (mut run, compiler) = super::execute(source);
            let p = witness(&mut run);
            let Some(VerifyFactResult::ForallFact(verified)) = &mut p.obligations.uniqueness_check
            else {
                panic!()
            };
            let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(
                verified,
            )) = verified.as_mut()
            else {
                panic!()
            };
            match mutation {
                0 => {
                    verified.fact.typed_parameters.groups[0].param_type =
                        ParamType::Set(crate::ast::param::Set {})
                }
                1 => {
                    let replacement = match &verified.fact.typed_parameters.groups[0].param_type {
                        ParamType::FiniteSet(_) => {
                            ParamType::NonemptySet(crate::ast::param::NonemptySet {})
                        }
                        _ => ParamType::FiniteSet(crate::ast::param::FiniteSet {}),
                    };
                    verified.fact.typed_parameters.groups[0].param_type = replacement;
                }
                2 => verified.fact.dom_facts.swap(0, 1),
                3 => {
                    let id = verified.fact.typed_parameters.groups[0].params[0].id;
                    verified
                        .fact
                        .typed_parameters
                        .groups
                        .last_mut()
                        .unwrap()
                        .params[0]
                        .id = id;
                }
                4 => {
                    let Some(InferResult::ExistUniqueFact(
                        InferExistUniqueFactResult::UniquenessForall(infer),
                    )) = &mut p.store_and_infer_result.infer
                    else {
                        panic!()
                    };
                    let StoreFactResult::ForallFact(stored) = &mut infer.derived.store else {
                        panic!()
                    };
                    stored.fact.typed_parameters.groups[0].param_type =
                        ParamType::Set(crate::ast::param::Set {});
                }
                _ => unreachable!(),
            }
            compiler
                .compile_run(&run, "bad_unique_kind")
                .expect_err(&format!("mutation {mutation}"));
        }
    }
}

#[test]
fn set_kind_theorem_substitution_checks_exact_quantified_kinds() {
    use crate::compile_to_lean::helper::instantiated_fact_matches;
    let (mut run, _) = super::execute(SOURCES[0]);
    let p = witness(&mut run);
    let source =
        crate::ast::fact::exist_shaped_fact_to_fact(&p.statement.exist_shaped_fact_in_witness);
    let Fact::ExistUniqueFact(mut changed) = source.clone() else {
        panic!()
    };
    let substitution = std::collections::HashMap::new();
    assert!(instantiated_fact_matches(&source, &source, &substitution));
    for kind in [
        ParamType::Set(crate::ast::param::Set {}),
        ParamType::NonemptySet(crate::ast::param::NonemptySet {}),
    ] {
        changed.typed_parameters.groups[0].param_type = kind;
        assert!(!instantiated_fact_matches(
            &source,
            &Fact::ExistUniqueFact(changed.clone()),
            &substitution
        ));
    }
}

#[test]
fn set_kind_negative_inference_rejects_changed_kinds_binders_and_negations() {
    for theorem_index in [0, 3] {
        for mutation in 0..4 {
            let (mut run, compiler) = super::execute(SOURCES[4]);
            let theorem = super::named_theorem_mut(&mut run.statement_results[theorem_index]);
            let ExecDefThmBodyProof::NonForall(body) = &mut theorem.body else {
                panic!()
            };
            let ExecStmtResult::By(ExecByStmtResult::Contra(ExecByContraStmtResult::Success(p))) =
                &mut body.proof_steps[0]
            else {
                panic!()
            };
            let Some(InferResult::NotExistFact(InferNotExistFactResult::DemorganForall(infer))) =
                &mut p.stored.infer
            else {
                panic!()
            };
            let StoreFactResult::ForallFact(stored) = &mut infer.derived.store else {
                panic!()
            };
            match mutation {
                0 => {
                    stored.fact.typed_parameters.groups[0].param_type =
                        ParamType::Set(crate::ast::param::Set {})
                }
                1 => stored.fact.typed_parameters.groups[0].params.swap(0, 1),
                2 => stored.fact.then_facts.clear(),
                3 => {
                    let id = stored.fact.typed_parameters.groups[0].params[0].id;
                    stored.fact.typed_parameters.groups[0].params[1].id = id;
                }
                _ => unreachable!(),
            }
            compiler
                .compile_run(&run, "bad_negative_kind")
                .expect_err(&format!("mutation {mutation}"));
        }
    }
}

#[test]
fn obtained_set_kind_parameters_and_facts_become_visible_after_their_producer() {
    for (source, index) in [(SOURCES[0], 2), (SOURCES[1], 1)] {
        let (run, compiler) = super::execute(source);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::ObtainObjFromExistFact(
                ExecObtainObjFromExistFactStmtResult::Success(p),
            ),
        )) = &run.statement_results[index]
        else {
            panic!()
        };
        let id = p.statement.equal_tos[0].id;
        let fact_id = p.store_and_infer_result.store_and_infer_results[0].primary_fact_id();
        let before = SourcePosition::new(None, SourceOwner::Run(&run), index);
        let after = SourcePosition {
            before: index + 1,
            ..before
        };
        assert!(before.visible_parameter(id, &compiler.runtime).is_err());
        assert!(after.visible_parameter(id, &compiler.runtime).is_ok());
        assert!(before.visible_fact(fact_id, &compiler.runtime).is_err());
        assert!(after.visible_fact(fact_id, &compiler.runtime).is_ok());
    }
}

#[test]
fn set_kind_quantifiers_do_not_accept_wrong_witnesses_or_false_exclusions() {
    for source in [
        "witness exist! x nonempty_set st {x = {}} from {}",
        "witness exist! x finite_set st {x = {1}} from {}",
        "not exist x finite_set st {x = {}}",
        "not exist x nonempty_set st {x = R}",
    ] {
        let mut runtime = Runtime::new_with_result_detail(
            LaunchCommand::Eval {
                code: String::new(),
                session: false,
                strict: true,
                language: OutputLanguage::English,
            },
            crate::result_detail::OutputDetail::Detailed,
        );
        assert!(!runtime.run_litex_code(source).unwrap().success, "{source}");
    }
}

#[test]
fn unique_set_template_requires_formation_stores_and_scoped_publication() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(SOURCES[5]);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
            ExecDefTemplateStmtResult::Success(template),
        )) = &mut run.statement_results[1]
        else {
            panic!()
        };
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::ObtainObjFromExistFact(
                ExecObtainObjFromExistFactStmtResult::Success(p),
            ),
        )) = template.body.as_mut()
        else {
            panic!()
        };
        let ObtainExistVerifySuccess::ExistUnique(verified) = &mut p.verify_exist else {
            panic!()
        };
        match mutation {
            0 => {
                verified
                    .well_defined_proof
                    .as_detailed_mut()
                    .unwrap()
                    .introduced_params
                    .param_type_well_defined[0] = ParamTypeWellDefinedProof::Set
            }
            1 => p.store_and_infer_result.store_and_infer_results.swap(0, 1),
            2 => {
                template.definition_facts[1].source_fact_id =
                    template.definition_facts[0].source_fact_id
            }
            3 => p.statement.equal_tos[0].id = IdentifierId::new(u64::MAX),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_unique_template")
            .expect_err(&format!("mutation {mutation}"));
    }
    let (run, compiler) = super::execute(SOURCES[5]);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
        ExecDefTemplateStmtResult::Success(template),
    )) = &run.statement_results[1]
    else {
        panic!()
    };
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::ObtainObjFromExistFact(
            ExecObtainObjFromExistFactStmtResult::Success(p),
        ),
    )) = template.body.as_ref()
    else {
        panic!()
    };
    let outside = SourcePosition::new(None, SourceOwner::Run(&run), 2);
    assert!(outside
        .visible_parameter(p.statement.equal_tos[0].id, &compiler.runtime)
        .is_err());
    assert!(outside
        .visible_fact(
            p.store_and_infer_result.store_and_infer_results[0].primary_fact_id(),
            &compiler.runtime
        )
        .is_err());
}
