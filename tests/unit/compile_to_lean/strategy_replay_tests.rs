use crate::execute::{ExecDefStrategyStmtResult, ExecDefStrategyStmtSuccess};
use crate::prelude::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::{SearchProofByKnownStrategy, DetailedSearchProofByKnownStrategy};

const APPLICATION: &str =
    include_str!("../../../lean/examples/strategy_known_application/statement.lit");
const MULTIPLE: &str =
    include_str!("../../../lean/examples/strategy_multiple_conclusions/statement.lit");
const DEPENDENT: &str =
    include_str!("../../../lean/examples/strategy_dependent_arguments/statement.lit");
const LOCAL: &str = include_str!("../../../lean/examples/strategy_local_declaration/statement.lit");
const NESTED: &str = include_str!("../../../lean/examples/strategy_nested_proof/statement.lit");
const GUARDED: &str =
    include_str!("../../../lean/examples/strategy_guarded_transport/statement.lit");

fn selected(statement: &mut ExecStmtResult) -> &mut DetailedSearchProofByKnownStrategy {
    let atomic = super::atomic_proof_mut(&mut super::fact_statement_mut(statement).verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByKnownStrategy(
        SearchProofByKnownStrategy::Detailed(p),
    ) = &mut atomic.searched_proof
    else {
        panic!("actual selected KnownStrategy")
    };
    p
}

const DECLARATION: &str = "prop replay_zero(x R):\n    x = 0\nstrategy replay_use_zero:\n    ? forall x R:\n        x = 0\n        =>:\n            $replay_zero(x)\n    by def $replay_zero(x)\n";

fn declaration(statement: &mut ExecStmtResult) -> &mut ExecDefStrategyStmtSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStrategy(
        ExecDefStrategyStmtResult::Success(proof),
    )) = statement
    else {
        panic!("actual strategy declaration")
    };
    proof
}

#[test]
fn strategy_declaration_replays_distinct_original_goal_and_body_headers() {
    let (mut run, compiler) = super::execute(DECLARATION);
    let p = declaration(&mut run.statement_results[1]);
    let VerifyFactWellDefinedResult::Success(FactWellDefinedProof::ForallFact(goal)) = &p.goal_wd
    else {
        panic!("original goal formation")
    };
    assert_ne!(
        goal.detailed_ref()
            .introduced_params
            .defined_params
            .store_and_infer_results[0]
            .primary_fact_id(),
        p.body
            .introduced_params
            .defined_params
            .store_and_infer_results[0]
            .primary_fact_id()
    );
    super::compile_run(&run, &compiler, "strategy_declaration").unwrap();
}

#[test]
fn strategy_declaration_rejects_missing_original_body_header_and_conclusions() {
    for change in ["parameters", "domain", "steps", "conclusions"] {
        let (mut run, compiler) = super::execute(DECLARATION);
        let p = declaration(&mut run.statement_results[1]);
        match change {
            "parameters" => p
                .body
                .introduced_params
                .defined_params
                .store_and_infer_results
                .clear(),
            "domain" => p.body.assumed_dom_facts.clear(),
            "steps" => p.body.proof_steps.clear(),
            "conclusions" => p.body.conclusion_proofs.clear(),
            _ => unreachable!(),
        }
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}

#[test]
fn known_strategy_replays_original_clause_and_dependent_instantiation() {
    for (source, index, clause) in [
        (APPLICATION, 2, 0),
        (MULTIPLE, 3, 0),
        (MULTIPLE, 4, 1),
        (DEPENDENT, 2, 0),
    ] {
        let (mut run, compiler) = super::execute(source);
        assert_eq!(
            selected(&mut run.statement_results[index]).then_index,
            clause
        );
        super::compile_run(&run, &compiler, "known_strategy").unwrap();
    }
}

#[test]
fn known_strategy_rejects_changed_name_clause_arguments_and_requirements() {
    for change in [
        "name",
        "clause",
        "matches",
        "arguments",
        "requirements",
        "domain",
    ] {
        let (mut run, compiler) = super::execute(APPLICATION);
        let p = selected(&mut run.statement_results[2]);
        match change {
            "name" => p.strategy_name = "missing_strategy".into(),
            "clause" => p.then_index = 10,
            "matches" => p.arg_match_proofs.clear(),
            "arguments" => p.forall_parameters_match_what_args.clear(),
            "requirements" => p
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .param_type_requirements
                .clear(),
            "domain" => p
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .proof_of_dom_facts
                .clear(),
            _ => unreachable!(),
        }
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}

#[test]
fn known_strategy_cannot_resolve_a_future_declaration_from_final_runtime() {
    let (mut run, compiler) = super::execute(APPLICATION);
    selected(&mut run.statement_results[2]);
    run.statement_results.swap(1, 2);
    let error = super::compile_run(&run, &compiler, "future_strategy").unwrap_err();
    assert_eq!(error.route, "Strategy/DeclarationProducer");
}

#[test]
fn local_strategy_replays_without_publishing_its_name_outside_the_claim() {
    let (run, compiler) = super::execute(LOCAL);
    super::compile_run(&run, &compiler, "local_strategy").unwrap();
    let root = SourcePosition::new(None, SourceOwner::Run(&run), run.statement_results.len());
    assert!(root.visible_strategy("replay_local_rule").is_err());
}

#[test]
fn strategy_nested_proof_replays_claim_witness_obtain_and_original_conclusion() {
    let (mut run, compiler) = super::execute(NESTED);
    assert_eq!(
        declaration(&mut run.statement_results[1])
            .body
            .proof_steps
            .len(),
        5
    );
    selected(&mut run.statement_results[2]);
    super::compile_run(&run, &compiler, "strategy_nested_body").unwrap();
}

#[test]
fn known_strategy_replays_guard_citation_and_rejects_missing_or_future_guard() {
    for future in [false, true] {
        let (mut run, compiler) = super::execute(GUARDED);
        selected(&mut run.statement_results[3]);
        super::compile_run(&run, &compiler, "original_strategy_guard").unwrap();
        let unavailable = if future {
            super::equality_proof_mut(
                &mut super::fact_statement_mut(&mut run.statement_results[4]).verify_result,
            )
            .fact
            .fact_id
        } else {
            FactId::new(u64::MAX)
        };
        let p = selected(&mut run.statement_results[3]);
        let requirements = p.instantiation_requirements.as_detailed_mut().unwrap();
        let path = super::equality_path_mut(&mut requirements.proof_of_dom_facts[0]);
        assert_eq!(path.path.len(), 1);
        path.path[0].2 = unavailable;
        let error = super::compile_run(&run, &compiler, "unavailable_strategy_guard").unwrap_err();
        assert_eq!(
            error.route,
            if future {
                "FactId/Producer"
            } else {
                "FactId/Resolution"
            }
        );
    }
}
