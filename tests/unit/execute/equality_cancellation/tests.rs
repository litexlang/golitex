use crate::json_output::{project_stmt_detailed, project_stmt_normal};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferEqualFactResult, InferResult};

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

fn exec(runtime: &mut Runtime, code: &str) -> ExecStmtResult {
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize(code, runtime.current_file.clone())
        .expect("tokenize");
    let stmts = runtime.parse(&tokens).expect("parse");
    assert_eq!(stmts.len(), 1, "one transactional statement per test step");
    runtime.exec_stmt(&stmts[0]).expect("exec_stmt")
}

fn forall(result: &ExecStmtResult) -> &VerifyForallFactSuccess {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(success)) = result else {
        panic!("successful forall")
    };
    let VerifyFactResult::ForallFact(proof) = &success.verify_result else {
        panic!("forall")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(proof)) =
        proof.as_ref()
    else {
        panic!("local forall")
    };
    proof
}

fn equality_rules(store: &StoreFactAndInferResult) -> &[InferEqualFactResult] {
    let Some(InferResult::AtomicFact(InferAtomicFactResult::EqualFact(rules))) = &store.infer
    else {
        panic!("equality inference")
    };
    rules
}

#[test]
fn equality_cancellation_all_positions_and_numeric_carriers() {
    for carrier in ["N", "Z", "Q", "R", "C"] {
        for (operator, guard) in [("+", ""), ("*", "    k != 0\n")] {
            for (left, right) in [
                ("a@k", "b@k"),
                ("k@a", "k@b"),
                ("a@k", "k@b"),
                ("k@a", "b@k"),
            ] {
                let left = left.replace('@', operator);
                let right = right.replace('@', operator);
                let source = format!("forall a, b, k {carrier}:\n{guard}    {left} = {right}\n    =>:\n        a = b\n");
                let mut rt = runtime();
                let result = exec(&mut rt, &source);
                assert!(
                    !result.is_failed(),
                    "{source}\n{}",
                    project_stmt_normal(&result, &rt).stringify_pretty()
                );
                let proof = forall(&result);
                let seed = &proof.assumed_dom_facts.last().unwrap().store_and_infer;
                assert_eq!(equality_rules(seed).len(), 1, "{source}");
                let VerifyFactResult::Equality(equality) =
                    &proof.proved_then_facts[0].verify_result
                else {
                    panic!("equality")
                };
                let VerifyEqualityResult::Success(equality) = equality.as_ref() else {
                    panic!("proved equality")
                };
                assert!(
                    matches!(
                        equality.searched_proof,
                        EqualFactSearchedProof::ByEquivalenceClass(_)
                    ),
                    "consume the inferred equality"
                );
            }
        }
    }
}

#[test]
fn equality_cancellation_keeps_source_and_all_premises() {
    let mut rt = runtime();
    let result = exec(
        &mut rt,
        "forall a, b, k C:\n    k != 0\n    a*k=b*k\n    =>:\n        a=b",
    );
    let proof = forall(&result);
    let seed = &proof.assumed_dom_facts[1].store_and_infer;
    let [InferEqualFactResult::NonzeroFactorCancellation(cancel)] = equality_rules(seed) else {
        panic!("factor certificate")
    };
    assert_eq!(cancel.source_fact_id, seed.primary_fact_id());
    for premise in [
        &cancel.left_in_c_proof,
        &cancel.right_in_c_proof,
        &cancel.common_in_c_proof,
        &cancel.factor_nonzero_proof,
    ] {
        assert!(!premise.is_failed());
    }
    let VerifyFactResult::AtomicExceptEquality(nonzero) = &cancel.factor_nonzero_proof else {
        panic!("nonzero")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(nonzero) = nonzero.as_ref() else {
        panic!("proved nonzero")
    };
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) = &nonzero.searched_proof
    else {
        panic!("stored nonzero cite")
    };
    assert_eq!(
        cite.cite_fact_id,
        proof.assumed_dom_facts[0].store_and_infer.primary_fact_id()
    );
    assert_eq!(
        proof
            .local_env
            .facts
            .facts_by_id
            .get(&cancel.derived.store.primary_fact_id())
            .unwrap()
            .readable_string(),
        "a = b"
    );
    for output in [
        project_stmt_normal(&result, &rt),
        project_stmt_detailed(&result, &rt),
    ] {
        assert!(output.stringify_pretty().contains("a = b"));
    }
    let detailed = project_stmt_detailed(&result, &rt).stringify_pretty();
    for field in [
        "NonzeroFactorCancellation",
        "source",
        "common_operand",
        "left_in_c_proof",
        "right_in_c_proof",
        "common_in_c_proof",
        "factor_nonzero_proof",
        "derived",
    ] {
        assert!(detailed.contains(field), "missing {field}: {detailed}");
    }
}

#[test]
fn equality_cancellation_nested_and_composite_common_operands() {
    for source in [
        "forall a, b, x, y C:\n    (a+x)+y=(b+x)+y\n    =>:\n        a+x=b+x\n        a=b",
        "forall a, b, x, y C:\n    x!=0\n    y!=0\n    (a*x)*y=(b*x)*y\n    =>:\n        a*x=b*x\n        a=b",
        "forall a, b, x, y C:\n    x+y!=0\n    a*(x+y)=b*(x+y)\n    =>:\n        a=b",
        "forall a, b, x, y C:\n    a+(x*y)=b+(x*y)\n    =>:\n        a=b",
        "forall a, b C:\n    a*2=b*2\n    =>:\n        a=b",
    ] {
        let mut rt = runtime();
        let result = exec(&mut rt, source);
        assert!(!result.is_failed(), "{source}");
        let proof = forall(&result);
        let seed = &proof.assumed_dom_facts.last().unwrap().store_and_infer;
        let derived_count = seed.stored_fact_ids().len() - seed.store.stored_fact_ids().len();
        assert_eq!(derived_count, 1, "the seed has only its direct conclusion");
    }
}

#[test]
fn equality_cancellation_missing_zero_and_wrong_shared_factor_reject() {
    for source in [
        "forall a, b, k C:\n    a*k=b*k\n    =>:\n        a=b",
        "forall a, b C:\n    a*0=b*0\n    =>:\n        a=b",
        "forall a, b, k C:\n    k=0\n    a*k=b*k\n    =>:\n        a=b",
        "forall a, b, k, l C:\n    k!=0\n    a*l=b*l\n    =>:\n        a=b",
        "forall a, b, k, l C:\n    a+k=b+l\n    =>:\n        a=b",
        "forall a, b, k C:\n    a+b=k+b\n    =>:\n        a=b",
        "forall a, b, k C:\n    k!=0\n    a*k=b*k\n    =>:\n        a=b+1",
        "forall a, b, k C:\n    a+k=b+k or a*k=b*k\n    =>:\n        a=b",
    ] {
        let mut rt = runtime();
        assert!(
            exec(&mut rt, source).is_failed(),
            "unexpected acceptance: {source}"
        );
        assert_eq!(rt.execution_environments_stack.len(), 1);
    }
}

#[test]
fn equality_cancellation_does_not_expand_reassociate_or_retrigger() {
    for source in [
        "forall a, b, x, y C:\n    (a+x)+y=(b+y)+x\n    =>:\n        a=b",
        "forall a, b, k C:\n    a*k=b*k\n    k!=0\n    =>:\n        a=b",
        "forall a, b, k, l C:\n    k=l\n    k!=0\n    a*k=b*l\n    =>:\n        a=b",
    ] {
        let mut rt = runtime();
        assert!(
            exec(&mut rt, source).is_failed(),
            "unexpected inference expansion: {source}"
        );
    }
}

#[test]
fn equality_cancellation_repeated_seed_uses_later_nonzero_certificate() {
    let mut rt = runtime();
    let result = exec(
        &mut rt,
        "forall a, b, k C:\n    a*k=b*k\n    k!=0\n    a*k=b*k\n    =>:\n        a=b",
    );
    let proof = forall(&result);
    assert!(equality_rules(&proof.assumed_dom_facts[0].store_and_infer).is_empty());
    assert_eq!(
        equality_rules(&proof.assumed_dom_facts[2].store_and_infer).len(),
        1
    );
}

#[test]
fn equality_cancellation_deduplicates_known_and_repeated_results() {
    let mut rt = runtime();
    let result = exec(
        &mut rt,
        "forall a, b, k C:\n    a+k=b+k\n    a+k=b+k\n    b+k=a+k\n    =>:\n        a=b",
    );
    let proof = forall(&result);
    assert_eq!(
        equality_rules(&proof.assumed_dom_facts[0].store_and_infer).len(),
        1
    );
    for seed in &proof.assumed_dom_facts[1..] {
        assert!(equality_rules(&seed.store_and_infer).is_empty());
    }
    let result = exec(
        &mut rt,
        "forall a, b, k C:\n    a=b\n    a+k=b+k\n    a+k=k+a\n    =>:\n        a=b",
    );
    for seed in &forall(&result).assumed_dom_facts[1..] {
        assert!(equality_rules(&seed.store_and_infer).is_empty());
    }
}

#[test]
fn equality_cancellation_scope_and_failed_statement_rollback() {
    let mut rt = runtime();
    assert!(!exec(&mut rt, "have a, b, k C").is_failed());
    assert!(!exec(&mut rt, "forall t C:\n    a+t=b+t\n    =>:\n        a=b").is_failed());
    assert!(exec(&mut rt, "a=b").is_failed());
    let before = rt.top_exec_env().facts.facts_by_id.len();
    let failed = exec(&mut rt, "claim:\n    ? 0=1\n    0*a+k=0*b+k");
    assert!(failed.is_failed());
    assert_eq!(
        rt.top_exec_env().facts.facts_by_id.len(),
        before,
        "the failed statement publishes neither its seed nor its inferred equality"
    );
    assert!(exec(&mut rt, "a=b").is_failed());
    assert_eq!(rt.execution_environments_stack.len(), 1);
    assert!(
        !exec(&mut rt, "1=1").is_failed(),
        "live context after normal failures"
    );
    // Failed claim output retains the failed conclusion, not its prior steps.
    // Prove separately that the very same body step does perform cancellation.
    let mut control = runtime();
    assert!(!exec(&mut control, "have a, b, k C").is_failed());
    let seed = exec(&mut control, "0*a+k=0*b+k");
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(seed)) = &seed else {
        panic!("checked cancellation seed")
    };
    assert!(matches!(
        equality_rules(&seed.store_and_infer_result),
        [InferEqualFactResult::AdditiveCancellation(_)]
    ));
}

#[test]
fn equality_cancellation_chain_and_and_keep_inference_evidence() {
    for seed in ["a+k=b+k and b=b", "a+k=b+k=b+k"] {
        let source = format!("forall a, b, k C:\n    {seed}\n    =>:\n        a=b");
        let mut rt = runtime();
        let result = exec(&mut rt, &source);
        assert!(!result.is_failed(), "{source}");
        let detail = project_stmt_detailed(&result, &rt).stringify();
        assert!(detail.contains("AdditiveCancellation"), "{detail}");
    }
}

#[test]
fn equality_cancellation_no_invalid_seed_or_function_injectivity() {
    for source in [
        "forall a, b set:\n    a+1=b+1\n    =>:\n        a=b",
        "have a C=1\nhave b C=2\na+3=b+3",
        "have fn f(x C) C=0\nforall a, b C:\n    f(a)=f(b)\n    =>:\n        a=b",
    ] {
        let mut rt = runtime();
        let result = rt.run_litex_code(source).expect("run");
        assert!(!result.success, "unexpected acceptance: {source}");
    }
}

#[test]
fn equality_cancellation_premise_ceiling_does_not_search_forall() {
    for expression in ["a*k=b*k", "k/a=k/b"] {
        let source = format!("forall a, b C*, k C:\n    forall t C:\n        t=k\n        =>:\n            t!=0\n    {expression}\n    =>:\n        {expression}");
        let mut rt = runtime();
        let result = exec(&mut rt, &source);
        let seed = &forall(&result).assumed_dom_facts[1].store_and_infer;
        assert!(
            equality_rules(seed).is_empty(),
            "nonzero only available through forall search"
        );
        let explicit = source
            .replace(
                &format!("    {expression}\n    =>:"),
                &format!("    k!=0\n    {expression}\n    =>:"),
            )
            .replace(&format!("        {expression}"), "        a=b");
        assert!(
            !exec(&mut rt, &explicit).is_failed(),
            "explicit nonzero exposes the permitted certificate"
        );
    }
}

#[test]
fn equality_cancellation_lean_citations_replay_the_selected_inference() {
    for (seed, guard) in [
        ("a*k=b*k", "    k!=0\n"),
        ("a-k=b-k", ""),
        ("k-a=k-b", ""),
        ("a/k=b/k", "    k!=0\n"),
        ("k/a=k/b", "    k!=0\n    a!=0\n    b!=0\n"),
    ] {
        let source = format!("forall a, b, k C:\n{guard}    {seed}\n    =>:\n        a=b");
        let mut rt = runtime();
        let run = rt.run_litex_code(&source).expect("source run");
        assert!(run.success);
        let output = crate::compile_to_lean::compile_run(&run, rt, "cancellation_boundary")
            .expect("the selected inferred equality has a checked compiler consumer");
        assert!(!output.contains("sorry") && !output.contains("admit"));
    }
}

#[test]
fn equality_cancellation_subtraction_division_positions_and_carriers() {
    for carrier in ["N", "Z", "Q", "R", "C"] {
        for (seed, guard, label) in [
            ("a-k=b-k", "", "SubtractiveCancellation"),
            ("k-a=k-b", "", "SubtractiveCancellation"),
            ("a/k=b/k", "    k!=0\n", "CommonDenominatorCancellation"),
            (
                "k/a=k/b",
                "    k!=0\n    a!=0\n    b!=0\n",
                "NonzeroNumeratorCancellation",
            ),
        ] {
            let source =
                format!("forall a, b, k {carrier}:\n{guard}    {seed}\n    =>:\n        a=b");
            let mut rt = runtime();
            let result = exec(&mut rt, &source);
            assert!(
                !result.is_failed(),
                "{source}\n{}",
                project_stmt_normal(&result, &rt).stringify_pretty()
            );
            let proof = forall(&result);
            let store = &proof.assumed_dom_facts.last().unwrap().store_and_infer;
            assert_eq!(
                equality_rules(store).len(),
                1,
                "must infer the equality at storage"
            );
            assert!(project_stmt_detailed(&result, &rt)
                .stringify()
                .contains(label));
            let VerifyFactResult::Equality(equal) = &proof.proved_then_facts[0].verify_result
            else {
                panic!("equality")
            };
            let VerifyEqualityResult::Success(equal) = equal.as_ref() else {
                panic!("proved equality")
            };
            assert!(matches!(
                equal.searched_proof,
                EqualFactSearchedProof::ByEquivalenceClass(_)
            ));
        }
    }
}

#[test]
fn equality_cancellation_division_retains_all_nonzero_certificates() {
    let mut rt = runtime();
    let result = exec(
        &mut rt,
        "forall a, b, k C*:\n    k/a=k/b\n    =>:\n        a=b",
    );
    let proof = forall(&result);
    let store = &proof.assumed_dom_facts[0].store_and_infer;
    let [InferEqualFactResult::NonzeroNumeratorCancellation(r)] = equality_rules(store) else {
        panic!("reciprocal certificate")
    };
    assert_eq!(r.source_fact_id, store.primary_fact_id());
    for premise in [
        &r.left_in_c_proof,
        &r.right_in_c_proof,
        &r.common_in_c_proof,
        &r.numerator_nonzero_proof,
        &r.left_denominator_nonzero_proof,
        &r.right_denominator_nonzero_proof,
    ] {
        assert!(!premise.is_failed());
    }
    assert_eq!(
        proof
            .local_env
            .facts
            .facts_by_id
            .get(&r.derived.store.primary_fact_id())
            .unwrap()
            .readable_string(),
        "a = b"
    );
    let detail = project_stmt_detailed(&result, &rt).stringify();
    for field in [
        "numerator_nonzero_proof",
        "left_denominator_nonzero_proof",
        "right_denominator_nonzero_proof",
    ] {
        assert!(detail.contains(field));
    }
    let result = exec(
        &mut rt,
        "forall a, b C, k C*:\n    a/k=b/k\n    =>:\n        a=b",
    );
    let proof = forall(&result);
    let store = &proof.assumed_dom_facts[0].store_and_infer;
    let [InferEqualFactResult::CommonDenominatorCancellation(r)] = equality_rules(store) else {
        panic!("denominator certificate")
    };
    assert_eq!(r.source_fact_id, store.primary_fact_id());
    assert!(!r.denominator_nonzero_proof.is_failed());
    assert!(project_stmt_detailed(&result, &rt)
        .stringify()
        .contains("denominator_nonzero_proof"));
}

#[test]
fn equality_cancellation_division_and_subtraction_do_not_cancel_cross_positions() {
    for source in [
        "forall a, b, k C:\n    a-k=k-b\n    =>:\n        a=b",
        "forall a, b, k C:\n    k-a=b-k\n    =>:\n        a=b",
        "forall a, b, k C*:\n    a/k=k/b\n    =>:\n        a=b",
        "forall a, b, k C*:\n    k/a=b/k\n    =>:\n        a=b",
        "forall a, b C*:\n    0/a=0/b\n    =>:\n        a=b",
        "forall a, b C*, k C:\n    k/a=k/b\n    =>:\n        a=b",
        "forall a, b, k, l C:\n    a-k=b-l\n    =>:\n        a=b",
    ] {
        let mut rt = runtime();
        assert!(
            exec(&mut rt, source).is_failed(),
            "incorrect cancellation: {source}"
        );
    }
}

#[test]
fn equality_cancellation_division_rejects_missing_or_zero_denominator_wd() {
    for source in [
        "forall a, b C:\n    a/0=b/0\n    =>:\n        a=b",
        "forall a, b, k C:\n    a/k=b/k\n    =>:\n        a=b",
        "forall a, b C, k C*:\n    k/a=k/b\n    =>:\n        a=b",
        "forall a C, b C*, k C*:\n    k/a=k/b\n    =>:\n        a=b",
        "forall a C*, b C, k C*:\n    k/a=k/b\n    =>:\n        a=b",
        "forall b C*, k C*:\n    k/0=k/b\n    =>:\n        0=b",
    ] {
        let mut rt = runtime();
        assert!(
            exec(&mut rt, source).is_failed(),
            "undefined quotient accepted: {source}"
        );
        assert_eq!(rt.execution_environments_stack.len(), 1);
    }
}

#[test]
fn equality_cancellation_mixed_nested_operators_and_zero_numerator() {
    for source in [
        "forall a, b, k, t C:\n    (k-a)-t=(k-b)-t\n    =>:\n        k-a=k-b\n        a=b",
        "forall a, b, k, t C:\n    k!=0\n    (a-t)/k=(b-t)/k\n    =>:\n        a-t=b-t\n        a=b",
        "forall a, b, x, y C:\n    x+y!=0\n    a/(x+y)=b/(x+y)\n    =>:\n        a=b",
        "forall a, b, k, t C*:\n    (k/a)/t=(k/b)/t\n    =>:\n        k/a=k/b\n        a=b",
        "forall b C, k C*:\n    0/k=b/k\n    =>:\n        b=0",
    ] {
        let mut rt = runtime();
        assert!(!exec(&mut rt, source).is_failed(), "{source}");
    }
}

#[test]
fn equality_cancellation_subtraction_division_dedup_scope_and_rollback() {
    for (seed, carrier) in [("a-k=b-k", "C"), ("a/k=b/k", "C*"), ("k/a=k/b", "C*")] {
        let mut rt = runtime();
        let source =
            format!("forall a, b, k {carrier}:\n    {seed}\n    {seed}\n    =>:\n        a=b");
        let result = exec(&mut rt, &source);
        let proof = forall(&result);
        assert_eq!(
            equality_rules(&proof.assumed_dom_facts[0].store_and_infer).len(),
            1
        );
        assert!(equality_rules(&proof.assumed_dom_facts[1].store_and_infer).is_empty());
        assert!(!exec(&mut rt, "have a, b, k C*").is_failed());
        let local = format!("forall t C:\n    {seed}\n    =>:\n        a=b");
        assert!(!exec(&mut rt, &local).is_failed());
        assert!(exec(&mut rt, "a=b").is_failed());
        let before = rt.top_exec_env().facts.facts_by_id.len();
        let body = match seed {
            "a-k=b-k" => "0*a-k=0*b-k",
            "a/k=b/k" => "(0*a)/k=(0*b)/k",
            _ => "k/(a-a+1)=k/(b-b+1)",
        };
        assert!(exec(&mut rt, &format!("claim:\n    ? 0=1\n    {body}")).is_failed());
        assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), before);
        assert_eq!(rt.execution_environments_stack.len(), 1);
    }
}
