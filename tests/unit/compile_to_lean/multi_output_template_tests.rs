use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::{ExecDefTemplateStmtResult, ExecDefTemplateStmtSuccessResult};
use crate::prelude::*;

const SOURCES: &[&str] = &[
    include_str!("../../../lean/examples/multi_output_adjacent_pair/statement.lit"),
    include_str!("../../../lean/examples/dependent_template_point/statement.lit"),
    include_str!("../../../lean/examples/paired_template_aliases/statement.lit"),
    include_str!("../../../lean/examples/paired_template_function/statement.lit"),
    include_str!("../../../lean/examples/correlated_template_witnesses/statement.lit"),
    include_str!("../../../lean/examples/guarded_template_alias_pair/statement.lit"),
    include_str!("../../../lean/examples/atomic_template_function_pair/statement.lit"),
];

fn template(run: &mut RunLitexCodeResult) -> &mut ExecDefTemplateStmtSuccessResult {
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
fn multi_output_template_pairs_replay_one_body_and_all_publications() {
    for source in SOURCES {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "multi_output").expect(source);
        assert_eq!(lean, compiler.compile_run(&run, "multi_output").unwrap());
        for statement in &run.statement_results {
            if let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
                ExecDefTemplateStmtResult::Success(p),
            )) = statement
            {
                for binding in p.statement.template_def_stmt.defined_bindings() {
                    assert!(lean.contains(&format!("def _template_i{}", binding.id.value())));
                }
                for published in &p.definition_facts {
                    assert!(lean.contains(&format!(
                        "theorem h_{}",
                        published.store_and_infer.primary_fact_id().value()
                    )));
                }
            }
        }
    }
}

#[test]
fn secondary_template_publications_cannot_be_replaced_by_primary_outputs() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(SOURCES[0]);
        let p = template(&mut run);
        match mutation {
            0 => p.definition_facts[1].source_fact_id = p.definition_facts[0].source_fact_id,
            1 => {
                p.definition_facts.remove(1);
            }
            2 => {
                let StoreFactResult::ForallFact(first) =
                    &p.definition_facts[0].store_and_infer.store
                else {
                    panic!()
                };
                let conclusion = first.fact.then_facts[0].clone();
                let StoreFactResult::ForallFact(second) =
                    &mut p.definition_facts[1].store_and_infer.store
                else {
                    panic!()
                };
                second.fact.then_facts[0] = conclusion;
            }
            3 => p.definition_facts.swap(0, 1),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_multi_output")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn every_template_output_has_the_same_original_visibility_boundary() {
    let (run, compiler) = super::execute(SOURCES[0]);
    let index = run
        .statement_results
        .iter()
        .position(|s| {
            matches!(
                s,
                ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(_))
            )
        })
        .unwrap();
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
        ExecDefTemplateStmtResult::Success(p),
    )) = &run.statement_results[index]
    else {
        panic!()
    };
    let before = SourcePosition::new(None, SourceOwner::Run(&run), index);
    let after = SourcePosition {
        before: index + 1,
        ..before
    };
    for binding in p.statement.template_def_stmt.defined_bindings() {
        let name = AtomicName::Plain {
            name: binding.name.clone(),
        };
        assert!(before.visible_template(&name).is_err());
        assert!(std::ptr::eq(after.visible_template(&name).unwrap().0, p));
        // Body-local identifiers and their source facts do not become globals.
        assert!(after
            .visible_parameter(binding.id, &compiler.runtime)
            .is_err());
    }
    for publication in &p.definition_facts {
        assert!(before
            .visible_fact(
                publication.store_and_infer.primary_fact_id(),
                &compiler.runtime
            )
            .is_err());
        assert!(after
            .visible_fact(
                publication.store_and_infer.primary_fact_id(),
                &compiler.runtime
            )
            .is_ok());
        assert!(after
            .visible_fact(publication.source_fact_id, &compiler.runtime)
            .is_err());
    }
}
