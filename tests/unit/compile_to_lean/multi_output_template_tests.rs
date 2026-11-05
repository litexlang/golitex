use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::{ExecDefTemplateStmtResult, ExecDefTemplateStmtSuccessResult};
use crate::prelude::*;

const SOURCES: &[&str] = &[
    r#"# Choose two adjacent real numbers together and use both named template outputs.
thm adjacent_pair:
    ? forall t R:
        exist! x, y R st {x = t, y = t + 1}
    witness exist! x, y R st {x = t, y = t + 1} from t, t + 1

template<t R>:
    obtain first_copy, second_copy from exist! x, y R st {x = t, y = t + 1}

\first_copy<2> = 2

\second_copy<2> = 3

\second_copy<2> = \first_copy<2> + 1

have fn paired_successor(t R) R = \second_copy<t>

paired_successor(2) = \second_copy<2> = 3
"#,
    r#"# Choose a finite singleton and a member from the same existential witness.
thm singleton_point:
    ? forall t R:
        exist A finite_set, x A st {A = {t}, x = t}
    witness exist A finite_set, x A st {A = {t}, x = t} from {t}, t

template<t R>:
    obtain point_set, point_member from exist A finite_set, x A st {A = {t}, x = t}

\point_member<4> $in \point_set<4>
"#,
    r#"# Give two real expressions separate template names in one declaration.
template<t R>:
    have alias_left, alias_right R = t, t + 1

\alias_right<4> = 5
"#,
    r#"# Select a real label and a function together, then call the second output.
thm function_pair:
    ? forall t R, f fn(a R) R:
        exist x R, g fn(a R) R st {x = t, g = f}
    witness exist x R, g fn(a R) R st {x = t, g = f} from t, f

template<t R, f fn(a R) R>:
    obtain function_label, copied_function from exist x R, g fn(a R) R st {x = t, g = f}

have fn identity_for_pair(a R) R = a

\copied_function<2, identity_for_pair> = identity_for_pair

\copied_function<2, identity_for_pair>(3) = identity_for_pair(3) = 3
"#,
    r#"# Choose adjacent numbers without uniqueness and retain their joint relation.
witness exist x, y R st {y = x + 1} from 0, 1

template<t R>:
    obtain related_left, related_right from exist x, y R st {y = x + 1}

\related_left<2> $in R

\related_right<2> = \related_left<2> + 1
"#,
    r#"# Select a divisor and its reciprocal under their shared nonzero condition.
template<t R: t != 0,>:
    have divisor_copy, reciprocal_copy R = t, 1 / t

\reciprocal_copy<2> = 1 / 2
"#,
    r#"# Obtain a label and callable companion from one predicate witness.
have fn identity_for_pair(a R) R = a

prop pair_of_function(t R, f fn(a R) R):
    exist x R, g fn(a R) R st {x = t, g = f}

thm atomic_function_pair:
    ? forall t R, f fn(a R) R:
        $pair_of_function(t, f)
    witness $pair_of_function(t, f) from t, f

template<t R, f fn(a R) R>:
    obtain atomic_label, atomic_function from $pair_of_function(t, f)

\atomic_function<2, identity_for_pair> = identity_for_pair

\atomic_function<2, identity_for_pair>(3) = identity_for_pair(3) = 3
"#,
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
        assert!(before.visible_template(&name, &compiler.runtime).is_err());
        assert!(std::ptr::eq(
            after.visible_template(&name, &compiler.runtime).unwrap().0,
            p
        ));
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
