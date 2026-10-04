use crate::ast::fact::Fact;
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}
fn fact(rt: &mut Runtime, code: &str) -> Fact {
    let tokens = Tokenizer::new()
        .tokenize(code, rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(fact) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("fact")
    };
    fact
}

#[test]
fn maintained_standard_superset_tracer_passes() {
    let code = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/examples/proof_nodes/atomic/by_known_special_property/standard_numeric_superset.lit"
    ));
    let run = runtime().run_litex_code(code).unwrap();
    assert!(run.success && run.session_error.is_none());
}

#[test]
fn stored_inclusion_has_the_right_direction_and_sign_boundary() {
    for (source, target, expected) in [
        ("Z", "R", true),
        ("N", "Q", true),
        ("N+", "R+", true),
        ("Q*", "C*", true),
        ("R-", "R*", true),
        ("R", "Q", false),
        ("C", "R", false),
        ("N", "N+", false),
        ("Q*", "Z*", false),
        ("R*", "R+", false),
        ("C", "C*", false),
    ] {
        let mut rt = runtime();
        assert!(
            rt.run_litex_code(&format!("have v {source}"))
                .unwrap()
                .success
        );
        let goal = fact(&mut rt, &format!("v $in {target}"));
        let before: Vec<_> = rt
            .execution_environments_stack
            .iter()
            .map(|e| {
                (
                    e.facts.facts_by_id.len(),
                    e.well_defined_objects.object_to_wd_id.len(),
                )
            })
            .collect();
        let proof = rt
            .verify_fact(
                &goal,
                VerifyState::new(VerifyStateLevel::KnownSpecialProperty),
            )
            .unwrap();
        assert_eq!(!proof.is_failed(), expected, "{source} -> {target}");
        let after: Vec<_> = rt
            .execution_environments_stack
            .iter()
            .map(|e| {
                (
                    e.facts.facts_by_id.len(),
                    e.well_defined_objects.object_to_wd_id.len(),
                )
            })
            .collect();
        assert_eq!(before, after, "search must not store facts or WD");
    }
}

#[test]
fn carrier_lookup_and_direct_structure_do_not_reopen_general_search() {
    for (level, expected) in [
        (VerifyStateLevel::Direct, true),
        (VerifyStateLevel::KnownSpecialProperty, true),
    ] {
        let mut rt = runtime();
        assert!(rt.run_litex_code("have v Z").unwrap().success);
        let goal = fact(&mut rt, "v $in R");
        assert_eq!(
            !rt.verify_fact(&goal, VerifyState::new(level))
                .unwrap()
                .is_failed(),
            expected
        );
    }
    let mut rt = runtime();
    assert!(rt.run_litex_code("have v Z").unwrap().success);
    let goal = fact(&mut rt, "v+1 $in R");
    assert!(!rt
        .verify_fact(
            &goal,
            VerifyState::new(VerifyStateLevel::KnownSpecialProperty)
        )
        .unwrap()
        .is_failed());
}

#[test]
fn detailed_superset_proof_cites_the_stored_membership() {
    let mut rt = runtime();
    let run = rt.run_litex_code("have v Z\nv $in R").unwrap();
    assert!(run.success);
    let json =
        crate::json_output::project_stmt_detailed(&run.statement_results[1], &rt).stringify();
    for needle in [
        "by_structural_membership",
        "standard_superset",
        "v $in Z",
        "cite_fact_id",
        "\"set\":\"Z\"",
        "\"set\":\"R\"",
    ] {
        assert!(json.contains(needle), "{json}");
    }
}

#[test]
fn stored_superset_leaf_remains_a_read_only_citation_without_constructor_search() {
    use super::{AtomicExceptEqualityFactSearchProofByKnownSpecialProperty, InFactSearchProofByKnownSpecialProperty};
    let mut rt = runtime();
    assert!(rt.run_litex_code("have v Z").unwrap().success);
    let Fact::AtomicFact(goal) = fact(&mut rt, "v $in R") else { panic!("atomic") };
    let proof = rt.search_atomic_except_equality_fact_proof_by_known_special_property(&goal).unwrap();
    let AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(
        InFactSearchProofByKnownSpecialProperty::StandardNumericSuperset(proof)
    ) = proof else { panic!("stored superset") };
    assert_eq!(proof.source_set, crate::ast::obj::StandardSet::Z);
    assert_eq!(proof.target_set, crate::ast::obj::StandardSet::R);
    assert!(proof.source_membership_proof.cite_fact_id().is_some());
    let Fact::AtomicFact(composite) = fact(&mut rt, "v+1 $in R") else { panic!("atomic") };
    assert!(rt.search_atomic_except_equality_fact_proof_by_known_special_property(&composite).is_none());
}
