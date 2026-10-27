use super::*;
use crate::execute::execute_fact_stmt::VerifyStateLevel;
use crate::json_output::project_run_detailed;

const TEMPLATE: &str = "template<S set>:\n    have fn real_identity(x R) R = x";

#[test]
fn template_standard_return_respects_the_known_search_ceiling() {
    for cached in [false, true] {
        for (level, expected) in [
            (VerifyStateLevel::Direct, false),
            (VerifyStateLevel::KnownSpecialProperty, true),
        ] {
            let mut rt = runtime();
            exec_ok(&mut rt, TEMPLATE);
            // Establish the template instance itself at the ordinary ceiling;
            // fresh/cached below refers to this actual application, not a new
            // template-domain proof inside the known-property leaf.
            exec_ok(&mut rt, "\\real_identity<R> $in fn(x R) R");
            exec_ok(&mut rt, "have a R");
            if cached {
                exec_ok(&mut rt, "\\real_identity<R>(a) = \\real_identity<R>(a)");
            }
            let fact = Fact::AtomicFact(atomic(&mut rt, "\\real_identity<R>(a) $in C"));
            let before = memory_sizes(&rt);
            let result = rt.verify_fact(&fact, VerifyState::new(level)).unwrap();
            assert_eq!(
                !result.is_failed(),
                expected,
                "cached={cached}, level={level:?}"
            );
            assert_eq!(memory_sizes(&rt), before);
        }
    }
}

#[test]
fn template_standard_return_captures_declarations_and_aliases() {
    let mut rt = runtime();
    exec_ok(&mut rt, TEMPLATE);
    exec_ok(&mut rt, "have alias fn(x R) R = \\real_identity<R>");
    let run = rt
        .run_litex_code("forall x R:\n    alias(x) $in C")
        .unwrap();
    assert!(run.success);
    let detail = project_run_detailed(&run, &rt, "test", None).stringify();
    assert!(
        detail.contains("TemplateApplicationInStandardSuperset"),
        "{detail}"
    );
    assert!(detail.contains("declared_signature") && detail.contains("function_equal"));
    assert!(
        detail.contains("cite_signature_fact_id"),
        "alias signature retained"
    );
}

#[test]
fn template_standard_return_refuses_invalid_widening_or_arguments() {
    for goal in [
        "forall x R:\n    \\real_identity<R>(x) $in Z",
        "\\real_identity<R>(i) $in C",
        "\\real_identity<R>(1,2) $in C",
    ] {
        let mut rt = runtime();
        exec_ok(&mut rt, TEMPLATE);
        let run = rt.run_litex_code(goal).unwrap();
        assert!(!run.success && run.session_error.is_none(), "{goal}");
        assert!(rt.run_litex_code("1 = 1").unwrap().success);
    }
    let mut rt = runtime();
    exec_ok(
        &mut rt,
        "template<S set>:\n    have fn complex_identity(x C) C = x",
    );
    assert!(
        !rt.run_litex_code("forall x C:\n    \\complex_identity<R>(x) $in R")
            .unwrap()
            .success
    );
}

#[test]
fn template_standard_return_cannot_bypass_a_template_guard() {
    let mut rt = runtime();
    exec_ok(
        &mut rt,
        "template<S set: $is_nonempty_set(S)>:\n    have fn guarded_identity(x R) R = x",
    );
    assert!(
        !rt.run_litex_code("\\guarded_identity<{}>(0) $in C")
            .unwrap()
            .success
    );
    assert!(rt.run_litex_code("1 = 1").unwrap().success);
}

#[test]
fn template_standard_return_checks_every_applicable_alias_signature() {
    let mut rt = runtime();
    exec_ok(
        &mut rt,
        "template<S set>:\n    have fn rational_identity(x Q) Q = x",
    );
    exec_ok(&mut rt, "have wide fn(x Q) C = \\rational_identity<R>");
    exec_ok(&mut rt, "have x Q");
    exec_ok(&mut rt, "wide(x) = wide(x)");
    let AtomicFact::InFact(goal) = atomic(&mut rt, "wide(x) $in R") else {
        panic!("membership")
    };
    let before = memory_sizes(&rt);
    assert!(
        rt.known_template_application_standard_superset(&goal)
            .is_none(),
        "the stored C return must not disappear behind the Q declaration"
    );
    let AtomicFact::InFact(goal) = atomic(&mut rt, "wide(x) $in C") else {
        panic!("membership")
    };
    let proof = rt
        .known_template_application_standard_superset(&goal)
        .expect("Q and C both lie in C");
    assert!(!proof.declared_returns.is_empty() && !proof.signature_returns.is_empty());
    assert_eq!(memory_sizes(&rt), before);
}
