use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
use crate::json_output::project_run_detailed;
use crate::prelude::*;
use crate::tokenize::Tokenizer;

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

const CASES: [(&str, &str); 2] = [
    (
        "forall A finite_set, B set:\n    $is_finite_set(intersect(A,B))",
        "IntersectFiniteFromLeft",
    ),
    (
        "forall A set, B finite_set:\n    $is_finite_set(intersect(A,B))",
        "IntersectFiniteFromRight",
    ),
];

#[test]
fn finite_intersection_one_bound_retains_the_actual_single_premise() {
    for (source, rule) in CASES {
        let mut rt = runtime();
        let run = rt.run_litex_code(source).unwrap();
        assert!(run.success && run.session_error.is_none());
        let detail = project_run_detailed(&run, &rt, "test", None).stringify();
        assert!(
            detail.contains(rule) && detail.contains("proof_of_requirement_facts"),
            "{detail}"
        );
    }
}

#[test]
fn finite_intersection_one_bound_does_not_reopen_strategy_permissions() {
    for (source, _) in CASES {
        for (level, expected) in [
            (VerifyStateLevel::BuiltinRule, false),
            (VerifyStateLevel::Strategy, true),
        ] {
            let mut rt = runtime();
            let blocks = Tokenizer::new().tokenize(source, CodeSource::Eval).unwrap();
            let stmts = rt.parse(&blocks).unwrap();
            let Stmt::Fact(fact) = &stmts[0] else {
                panic!("forall")
            };
            let result = rt.verify_fact(fact, VerifyState::new(level)).unwrap();
            assert_eq!(!result.is_failed(), expected, "{source}: {level:?}");
        }
    }
}

#[test]
fn finite_intersection_one_bound_keeps_both_finite_priority_and_cardinality_wd() {
    let mut rt = runtime();
    let run = rt
        .run_litex_code("forall A,B finite_set:\n    $is_finite_set(intersect(A,B))")
        .unwrap();
    assert!(run.success);
    assert!(project_run_detailed(&run, &rt, "test", None)
        .stringify()
        .contains("IntersectFiniteFromBoth"));
    assert!(
        rt.run_litex_code(
            "forall E set, point R:\n    finite_set_size(intersect(E,{point})) $in N"
        )
        .unwrap()
        .success
    );
    assert!(rt.run_litex_code("template<Omega finite_set,point Omega>:\n    have fn dirac_event_probability(E power_set(Omega)) R = finite_set_size(intersect(E,{point}))").unwrap().success);
}

#[test]
fn finite_intersection_one_bound_preserves_nearest_boundaries_and_liveness() {
    for source in [
        "forall A,B set:\n    $is_finite_set(intersect(A,B))",
        "forall A finite_set,B set:\n    $is_finite_set(union(A,B))",
        "forall A set,B finite_set:\n    $is_finite_set(set_minus(A,B))",
        "finite_set_size(intersect({1/0},{})) $in N",
    ] {
        let mut rt = runtime();
        let run = rt.run_litex_code(source).unwrap();
        assert!(!run.success && run.session_error.is_none(), "{source}");
        assert!(rt.run_litex_code("1 = 1").unwrap().success);
    }
    let mut rt = runtime();
    assert!(
        rt.run_litex_code("have E set\n$is_finite_set(intersect(E,{0}))")
            .unwrap()
            .success
    );
    assert!(!rt.run_litex_code("$is_finite_set(E)").unwrap().success);
}
