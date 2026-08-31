//! Contracts for statement-local proof reuse and recursion guards.

use super::{StatementProofScopeState, StatementProofStateStack};
use crate::error::RuntimeError;
use crate::fact::{AtomicFact, EqualFact, Fact};
use crate::output::render_statement_result_json;
use crate::parsing::Tokenizer;
use crate::result::{StmtResult, SuccessFactProofResult, SuccessVerifyFactResult};
use crate::runtime::Runtime;
use crate::statement::Stmt;
use crate::syntax::name_types::FactString;
use crate::verification::VerifyState;
use std::rc::Rc;

impl StatementProofStateStack {
    fn current_atomic_fact_proof_count(&self) -> usize {
        self.current_scope()
            .map(|scope| scope.atomic_fact_proofs.len())
            .unwrap_or(0)
    }

    fn current_scope(&self) -> Option<&StatementProofScopeState> {
        self.scopes.last()
    }
}

impl Runtime {
    fn statement_atomic_fact_proof_is_cached(&self, key: &FactString) -> bool {
        self.statement_proof_state
            .scopes_from_inner()
            .any(|scope| scope.atomic_fact_proofs.contains_key(key))
    }

    fn current_statement_atomic_fact_proof_count(&self) -> usize {
        self.statement_proof_state.current_atomic_fact_proof_count()
    }
}

#[test]
fn successful_atomic_fact_is_shared_until_statement_proof_cache_is_cleared() {
    let mut runtime = new_test_runtime();
    let fact = parse_atomic_fact(&mut runtime, "1 < 2");

    let first = runtime
        .verify_atomic_fact(&fact, &VerifyState::initial())
        .expect("first verification should run");
    let first_source = direct_verification(&first);
    assert!(!matches!(
        first_source.proof(),
        SuccessFactProofResult::Reuse(_)
    ));
    assert!(runtime.statement_atomic_fact_proof_is_cached(&fact.to_string()));
    assert!(runtime
        .verification_result_from_known_fact_cache(&fact.clone().into())
        .is_none());

    let second = runtime
        .verify_atomic_fact(&fact, &VerifyState::initial())
        .expect("second verification should hit the statement proof cache");
    let second_source = reused_verification(&second);
    assert!(Rc::ptr_eq(&first_source, second_source));
    assert!(second.infer_result().is_empty());
    let output = render_statement_result_json(&second);
    assert!(output.contains("number comparison"), "{output}");
    assert!(!output.contains("statement proof cache"), "{output}");

    runtime.clear_statement_proof_state();
    assert_eq!(runtime.current_statement_atomic_fact_proof_count(), 0);
}

#[test]
fn unknown_atomic_fact_is_not_cached() {
    let mut runtime = new_test_runtime();
    let fact = parse_atomic_fact(&mut runtime, "1 = 2");

    let result = runtime
        .verify_atomic_fact(&fact, &VerifyState::initial())
        .expect("unknown verification should not error");
    assert!(result.is_unknown());
    assert!(!runtime.statement_atomic_fact_proof_is_cached(&fact.to_string()));

    runtime.clear_statement_proof_state();
    let stmt = parse_stmt(&mut runtime, "1 = 2");
    assert!(runtime.execute_statement(&stmt).is_err());
    assert_eq!(runtime.current_statement_atomic_fact_proof_count(), 0);
}

#[test]
fn local_environment_proof_cache_is_visible_inward_and_discarded_outward() {
    let mut runtime = new_test_runtime();
    let parent_fact = parse_atomic_fact(&mut runtime, "1 < 2");
    let child_fact = parse_atomic_fact(&mut runtime, "2 < 3");
    runtime
        .verify_atomic_fact(&parent_fact, &VerifyState::initial())
        .expect("parent fact should verify");

    runtime
        .run_in_local_env(|runtime| {
            assert!(runtime
                .verification_result_from_statement_proof_cache(&parent_fact)
                .is_some());
            runtime.verify_atomic_fact(&child_fact, &VerifyState::initial())?;
            assert!(runtime.statement_atomic_fact_proof_is_cached(&child_fact.to_string()));
            Ok::<(), RuntimeError>(())
        })
        .expect("local verification should succeed");

    assert!(runtime
        .verification_result_from_statement_proof_cache(&parent_fact)
        .is_some());
    assert!(runtime
        .verification_result_from_statement_proof_cache(&child_fact)
        .is_none());
}

#[test]
fn known_only_entry_points_reuse_statement_proofs() {
    let mut runtime = new_test_runtime();
    let set_fact = parse_atomic_fact(&mut runtime, "$is_set(R)");
    let first_set_result = runtime
        .verify_atomic_fact(&set_fact, &VerifyState::initial())
        .expect("builtin set fact should verify");
    let set_source = direct_verification(&first_set_result);
    let known_set_result = runtime
        .verify_non_equational_atomic_fact_with_known_atomic_facts(&set_fact)
        .expect("known-only non-equality entry should consult the statement proof cache");
    assert!(Rc::ptr_eq(
        &set_source,
        reused_verification(&known_set_result)
    ));

    let equality = parse_atomic_fact(&mut runtime, "1 = 1");
    let first_equality_result = runtime
        .verify_atomic_fact(&equality, &VerifyState::initial())
        .expect("reflexive equality should verify");
    let equality_source = direct_verification(&first_equality_result);
    let AtomicFact::EqualFact(equality_fact) = equality else {
        unreachable!()
    };
    let known_equality_result =
        runtime.verify_equal_fact_by_known_equality(&EqualFact::new_from_refs(
            &equality_fact.left,
            &equality_fact.right,
            equality_fact.line_file,
        ));
    assert!(Rc::ptr_eq(
        &equality_source,
        reused_verification(&known_equality_result)
    ));
}

#[test]
fn next_statement_does_not_inherit_the_previous_proof_cache_source() {
    let mut runtime = new_test_runtime();
    let fact = parse_atomic_fact(&mut runtime, "1 < 2");
    let first = runtime
        .verify_atomic_fact(&fact, &VerifyState::initial())
        .expect("temporary proof should verify");
    let first_source = direct_verification(&first);

    let stmt = parse_stmt(&mut runtime, "1 < 2");
    let second = runtime
        .execute_statement(&stmt)
        .expect("the next statement should verify independently");
    let second_source = direct_verification(&second);
    assert!(!Rc::ptr_eq(&first_source, &second_source));
    assert_eq!(runtime.current_statement_atomic_fact_proof_count(), 0);
}

#[test]
fn exec_stmt_clears_temporary_successes_but_keeps_the_proof_evidence() {
    let mut runtime = new_test_runtime();
    let stmt = parse_stmt(&mut runtime, "1 < 2");
    let Stmt::Fact(Fact::AtomicFact(fact)) = &stmt else {
        unreachable!()
    };
    let result = runtime
        .execute_statement(&stmt)
        .expect("statement should verify");

    assert_eq!(runtime.current_statement_atomic_fact_proof_count(), 0);
    assert!(runtime
        .verification_result_from_known_fact_cache(&fact.clone().into())
        .is_some());
    let output = render_statement_result_json(&result);
    assert!(output.contains("number comparison"), "{output}");
    assert!(!output.contains("statement proof cache"), "{output}");
}

fn new_test_runtime() -> Runtime {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("statement_proof_cache_test.lit");
    runtime
}

fn parse_atomic_fact(runtime: &mut Runtime, source: &str) -> AtomicFact {
    let stmt = parse_stmt(runtime, source);
    let Stmt::Fact(Fact::AtomicFact(fact)) = stmt else {
        panic!("expected an atomic fact: {source}");
    };
    fact
}

fn parse_stmt(runtime: &mut Runtime, source: &str) -> Stmt {
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks(source, Rc::from("statement_proof_cache_test.lit"))
        .expect("test statement should tokenize");
    assert_eq!(blocks.len(), 1);
    runtime
        .parse_statement(&mut blocks[0])
        .expect("test statement should parse")
}

fn direct_verification(result: &StmtResult) -> Rc<SuccessVerifyFactResult> {
    let success = result
        .factual_success()
        .expect("atomic fact should be factual");
    success.verification.clone()
}

fn reused_verification(result: &StmtResult) -> &Rc<SuccessVerifyFactResult> {
    let success = result
        .factual_success()
        .expect("cached atomic fact should be factual");
    let SuccessFactProofResult::Reuse(result) = success.proof() else {
        panic!("atomic success should retain its statement proof-cache source");
    };
    &result.source
}
