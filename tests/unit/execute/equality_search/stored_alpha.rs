use super::*;

const TRACER: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/examples/proof_nodes/equal/by_equivalence_class/stored_aggregate_alpha.lit"
));

fn normal_runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: false,
        language: OutputLanguage::English,
    })
}

#[test]
fn stored_aggregate_alpha_cites_original_fact_without_changing_store() {
    let mut rt = normal_runtime();
    exec_ok(&mut rt, "have f, g, h fn(index Z) R");
    exec_ok(&mut rt, "have m, n Z");
    exec_ok(&mut rt, "trust m <= n");
    exec_ok(&mut rt, "trust sum(m, n, fn(source Z) R {f(source)}) = sum(m, n, fn(target Z) R {g(target)})");
    for (code, reversed) in [
        ("sum(m, n, fn(left_index Z) R {f(left_index)}) = sum(m, n, fn(right_index Z) R {g(right_index)})", false),
        ("sum(m, n, fn(left_index Z) R {g(left_index)}) = sum(m, n, fn(right_index Z) R {f(right_index)})", true),
    ] {
        let goal = equal(&mut rt, code);
        assert!(!rt.verify_equal_fact_well_definedness(&goal, VerifyState::top_level()).unwrap().is_failed());
        let before = store_sizes(&rt);
        let proof = rt.search_equal_fact_proof_by_equivalence_class(&goal, VerifyState::top_level()).unwrap().expect("stored alpha equality");
        let EqualFactSearchedProofByEquivalenceClass::AlphaEndpoints(proof) = proof else { panic!("alpha endpoint citation") };
        assert_eq!(proof.reversed, reversed);
        assert!(matches!(rt.fact_by_id_in_stack(proof.cited.fact_id), Some(Fact::AtomicFact(AtomicFact::EqualFact(_)))));
        assert_eq!(store_sizes(&rt), before, "read-only equality replay");
    }
    for code in [
        "sum(m, n, fn(left_index Z) R {f(left_index)}) = sum(m, n, fn(right_index Z) R {h(right_index)})",
        "sum(m, n, fn(left_index Z) R {f(left_index) + 1}) = sum(m, n, fn(right_index Z) R {g(right_index)})",
        "sum(m, n + 1, fn(left_index Z) R {f(left_index)}) = sum(m, n, fn(right_index Z) R {g(right_index)})",
        "sum(m, n, fn(left_index Z) C {f(left_index)}) = sum(m, n, fn(right_index Z) R {g(right_index)})",
    ] {
        let goal = equal(&mut rt, code);
        let before = store_sizes(&rt);
        assert!(rt.search_equal_fact_proof_by_equivalence_class(&goal, VerifyState::top_level()).unwrap().is_none(), "{code}");
        assert_eq!(store_sizes(&rt), before);
    }
}

#[test]
fn same_anonymous_aggregate_trust_can_close_theorem_and_wd_still_rejects() {
    let mut rt = normal_runtime();
    let run = rt.run_litex_code("thm scalar_sum:\n    ? forall a fn(index N+) R, c R, m, n N+:\n        m <= n\n        =>:\n            sum(m, n, fn(source_index N+) R {c * a(source_index)}) = c * sum(m, n, fn(target_index N+) R {a(target_index)})\n    trust sum(m, n, fn(source_index N+) R {c * a(source_index)}) = c * sum(m, n, fn(target_index N+) R {a(target_index)})\n").unwrap();
    assert!(run.success && run.session_error.is_none(), "same checked fact must be reusable: {:?}", run.session_error);
    let rejected = rt.run_litex_code("thm invalid_division:\n    ? 1 / 0 = 1 / 0\n    trust 1 / 0 = 1 / 0\n").unwrap();
    assert!(!rejected.success && rejected.session_error.is_none());
}

#[test]
fn strict_aggregate_alpha_premise_tracer() {
    let run = runtime().run_litex_code(TRACER).unwrap();
    assert!(run.success && run.session_error.is_none());
}
