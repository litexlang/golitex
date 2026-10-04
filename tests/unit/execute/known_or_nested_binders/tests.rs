use crate::ast::fact::{Fact, OrFact};
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::verify_or_fact::OrFactSearchedProof;
use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime(strict: bool) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict,
        language: OutputLanguage::English,
    })
}
fn or_fact(rt: &mut Runtime, code: &str) -> OrFact {
    let tokens = Tokenizer::new()
        .tokenize(code, rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(Fact::OrFact(fact)) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("or fact")
    };
    fact
}
fn sizes(rt: &Runtime) -> Vec<(usize, usize)> {
    rt.execution_environments_stack
        .iter()
        .map(|e| {
            (
                e.facts.facts_by_id.len(),
                e.well_defined_objects.object_to_wd_id.len(),
            )
        })
        .collect()
}

#[test]
fn inferred_union_disjunction_reuses_nested_binders_without_trust() {
    let run = runtime(true)
        .run_litex_code(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/or/by_known_or_fact/set_builder_union_membership.lit"
        )))
        .unwrap();
    assert!(run.success && run.session_error.is_none());
}

#[test]
fn known_or_citation_preserves_free_owners_carriers_and_conditions() {
    let mut rt = runtime(false);
    // A unit assumption, not a new textbook/builtin trusted result.
    assert!(
        rt.run_litex_code(
            "have y, first, second R\ntrust y $in {x R: x < first} or y $in {x R: x > first}\n"
        )
        .unwrap()
        .success
    );
    let before = sizes(&rt);
    let goal = or_fact(&mut rt, "y $in {u R: u < first} or y $in {v R: v > first}");
    for level in [
        VerifyStateLevel::Direct,
        VerifyStateLevel::KnownSpecialProperty,
        VerifyStateLevel::DefinitionAndForall,
    ] {
        let Some(OrFactSearchedProof::ByKnownOrFact(proof)) = rt
            .search_or_fact_proof_by_known_or_fact(&goal, VerifyState::new(level))
            .unwrap()
        else {
            panic!("stored Or citation")
        };
        assert!(matches!(
            rt.fact_by_id_in_stack(proof.cite_fact_id),
            Some(Fact::OrFact(_))
        ));
        assert_eq!(before, sizes(&rt));
    }
    for goal in [
        "y $in {u Z: u < first} or y $in {v R: v > first}",
        "y $in {u R: u <= first} or y $in {v R: v > first}",
        "y $in {u R: u < second} or y $in {v R: v > first}",
        "not y $in {u R: u < first} or y $in {v R: v > first}",
        "first $in {u R: u < first} or first $in {v R: v > first}",
    ] {
        let goal_fact = or_fact(&mut rt, goal);
        assert!(
            rt.search_or_fact_proof_by_known_or_fact(&goal_fact, VerifyState::top_level())
                .unwrap()
                .is_none(),
            "{goal}"
        );
        assert_eq!(before, sizes(&rt));
    }
}
