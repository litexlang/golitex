use crate::prelude::*;

const REGISTERED: &str =
    include_str!("../../../../examples/proof_nodes/atomic/by_known_rewrite/transitivity.lit");

#[test]
fn one_step_transitivity_tries_the_next_known_left_edge_after_a_failed_residual() {
    let mut rt = runtime();
    let run = rt.run_litex_code("1 <= 9\n1 <= 2\n").unwrap();
    assert!(run.success);
    let second = atomic_subject(&run.statement_results[1]);
    let goal = parse_atomic(&mut rt, "1 <= 4");
    let proof = rt
        .search_transitive_relation(&goal, VerifyState::top_level().without_rewrite())
        .unwrap()
        .expect("the second left edge has a true residual");
    assert_eq!(proof.known_left_fact_id, second.fact_id());
    assert_eq!(proof.residual_fact.readable_string(), "2 <= 4");
    assert!(!proof.proof_of_residual_fact.is_failed());
}

#[test]
fn one_step_transitivity_rejects_other_predicates_left_endpoints_and_false_residuals() {
    let mut rt = runtime();
    let run = rt.run_litex_code("1 < 2\n0 <= 2\n1 <= 9\n").unwrap();
    assert!(run.success);
    let goal = parse_atomic(&mut rt, "1 <= 4");
    assert!(rt
        .search_transitive_relation(&goal, VerifyState::top_level())
        .unwrap()
        .is_none());
}

#[test]
fn one_step_transitivity_reaches_all_four_builtin_order_rewrites() {
    for (premise, goal) in [
        ("x <= 900", "x <= 1070"),
        ("x < 900", "x < 1070"),
        ("x >= 1260", "x >= 1250"),
        ("x > 1260", "x > 1250"),
    ] {
        let mut rt = runtime();
        let source = format!("forall x R:\n    {premise}\n    =>:\n        {goal}\n");
        let result = rt.run_litex_code(&source).unwrap();
        assert!(result.success, "{source}");
        let output = crate::json_output::emit_run_detailed(&result, &rt, "eval", None);
        assert!(
            output.contains("\"rule\": \"OrderTransitivity\""),
            "{output}"
        );
        assert!(output.contains("known_left_fact_id"));
        assert!(output.contains("proof_of_residual_fact"));
    }
}

#[test]
fn one_step_transitivity_requires_an_explicit_positive_complement() {
    let mut rt = runtime();
    let direct = "forall x R:\n    x <= 900\n    =>:\n        not x > 1070\n";
    assert!(!rt.run_litex_code(direct).unwrap().success);
    let explicit = "forall x R:\n    x <= 900\n    =>:\n        x <= 1070\n        not x > 1070\n";
    assert!(rt.run_litex_code(explicit).unwrap().success);
}

#[test]
fn one_step_transitivity_does_not_chain_a_second_rewrite_or_reverse_search() {
    for source in [
        "forall a,b,c,d R:\n    a<=b\n    b<=c\n    c<=d\n    =>:\n        a<=d\n",
        "forall x R:\n    900 <= x\n    =>:\n        800 <= x\n",
        "forall x R:\n    x <= 900\n    =>:\n        x <= 899\n",
        "forall x R:\n    x <= 900\n    =>:\n        x < 1070\n",
    ] {
        let mut rt = runtime();
        let result = rt.run_litex_code(source).unwrap();
        assert!(
            !result.success && result.session_error.is_none(),
            "{source}"
        );
        assert_eq!(rt.execution_environments_stack.len(), 1);
    }
}

#[test]
fn one_step_registered_transitivity_reaches_the_shared_search_and_registered_rewrite() {
    let mut rt = runtime();
    let prefix = REGISTERED.split("# Now:").next().unwrap();
    let source = format!("{prefix}\nhave rel_a R=1\nhave rel_b R=2\nhave rel_c R=3\nby def $below(rel_a,rel_b)\nby def $below(rel_b,rel_c)\n");
    let result = rt.run_litex_code(&source).unwrap();
    assert!(
        result.success,
        "{}",
        crate::json_output::emit_run_normal(&result, &rt, "eval", None)
    );
    let goal = parse_atomic(&mut rt, "$below(rel_a,rel_c)");
    let proof = rt
        .search_atomic_except_equality_fact_proof_by_known_rewrite(&goal, VerifyState::top_level())
        .unwrap()
        .expect("registered rewrite");
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::AtomicExceptEqualityFactSearchProofByKnownRewrite as Rule;
    let Rule::Transitivity(proof) = proof else {
        panic!("registered transitivity")
    };
    assert_eq!(proof.cite_prop, goal.prop_name());
    assert_eq!(
        proof.application.residual_fact.readable_string(),
        "$below(rel_b, rel_c)"
    );
    assert!(!proof.application.proof_of_residual_fact.is_failed());
}

#[test]
fn one_step_registered_transitivity_requires_registration_without_changing_other_proof_routes() {
    let mut rt = runtime();
    let prefix = REGISTERED.split("register transitive:").next().unwrap();
    assert!(rt.run_litex_code(prefix).unwrap().success);
    assert!(rt.run_litex_code("have rel_a R=1\nhave rel_b R=2\nhave rel_c R=3\nby def $below(rel_a,rel_b)\nby def $below(rel_b,rel_c)\n").unwrap().success);
    let goal = parse_atomic(&mut rt, "$below(rel_a,rel_c)");
    assert!(rt
        .search_atomic_except_equality_fact_proof_by_known_rewrite(&goal, VerifyState::top_level())
        .unwrap()
        .is_none());
    let registration = "register transitive:\n    ? forall x,y,z set:\n        $below(x,y)\n        $below(y,z)\n        =>:\n            $below(x,z)\n";
    assert!(rt.run_litex_code(registration).unwrap().success);
    assert!(rt
        .search_atomic_except_equality_fact_proof_by_known_rewrite(&goal, VerifyState::top_level())
        .unwrap()
        .is_some());
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

fn parse_atomic(rt: &mut Runtime, source: &str) -> AtomicFact {
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize(source, rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(Fact::AtomicFact(fact)) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("atomic fact")
    };
    fact
}

fn atomic_subject(statement: &ExecStmtResult) -> AtomicFact {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) = statement else {
        panic!("fact statement")
    };
    let VerifyFactResult::AtomicExceptEquality(result) = &statement.verify_result else {
        panic!("non-equality verification")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_ref() else {
        panic!("successful verification")
    };
    proof.fact.clone()
}

fn runtime() -> Runtime {
    Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    )
}
