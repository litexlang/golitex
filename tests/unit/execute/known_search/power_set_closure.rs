use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
use crate::json_output::project_run_detailed;
use crate::prelude::*;
use crate::tokenize::Tokenizer;

const CASES: [(&str, &str); 4] = [
    (
        "forall X set, A,B power_set(X):\n    union(A,B) $in power_set(X)",
        "UnionInPowerSet",
    ),
    (
        "forall X set, A power_set(X), B set:\n    intersect(A,B) $in power_set(X)",
        "IntersectInPowerSetFromLeft",
    ),
    (
        "forall X set, A set, B power_set(X):\n    intersect(A,B) $in power_set(X)",
        "IntersectInPowerSetFromRight",
    ),
    (
        "forall X set, A power_set(X), B set:\n    set_minus(A,B) $in power_set(X)",
        "SetMinusInPowerSet",
    ),
];

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

#[test]
fn power_set_closure_quotes_the_actual_membership_evidence() {
    for (source, rule) in CASES {
        let mut rt = runtime();
        let run = rt.run_litex_code(source).unwrap();
        assert!(run.success && run.session_error.is_none(), "{source}");
        let detail = project_run_detailed(&run, &rt, "test", None).stringify();
        assert!(detail.contains(rule), "{detail}");
        assert!(detail.contains("cite_fact_id"), "{detail}");
        assert!(!detail.contains("by_builtin_strategy"), "{detail}");
    }
}

#[test]
fn power_set_closure_respects_the_existing_search_ceiling() {
    for (source, _) in CASES {
        for (level, expected) in [
            (VerifyStateLevel::Direct, false),
            (VerifyStateLevel::KnownSpecialProperty, true),
        ] {
            let mut rt = runtime();
            let blocks = Tokenizer::new().tokenize(source, CodeSource::Eval).unwrap();
            let stmts = rt.parse(&blocks).unwrap();
            let Stmt::Fact(fact) = &stmts[0] else {
                panic!("forall fact");
            };
            let result = rt.verify_fact(fact, VerifyState::new(level)).unwrap();
            assert_eq!(!result.is_failed(), expected, "{source}: {level:?}");
        }
    }
}

#[test]
fn power_set_closure_refuses_missing_or_reversed_carriers() {
    for source in [
        "forall X,Y set, A power_set(X), B power_set(Y):\n    union(A,B) $in power_set(X)",
        "forall X,Y set, A power_set(Y), B power_set(X):\n    set_minus(A,B) $in power_set(X)",
        "forall X,Y set, A,B power_set(X):\n    union(A,B) $in power_set(Y)",
        "forall X set, A,B set:\n    intersect(A,B) $in power_set(X)",
    ] {
        let mut rt = runtime();
        let run = rt.run_litex_code(source).unwrap();
        assert!(!run.success && run.session_error.is_none(), "{source}");
        assert!(rt.run_litex_code("1 = 1").unwrap().success);
    }
}
