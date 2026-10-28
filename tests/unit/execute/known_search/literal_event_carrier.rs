use super::*;
use crate::execute::execute_fact_stmt::VerifyStateLevel;
use crate::json_output::project_run_detailed;

const CASES: [&str; 3] = [
    "forall X set,a X:\n    {a} $in power_set(X)",
    "forall X set,a,b X:\n    a != b\n    =>:\n        {a,b} $in power_set(X)",
    "forall X,Y set,a X:\n    X = Y\n    =>:\n        {a} $in power_set(Y)",
];

#[test]
fn literal_event_carrier_reads_each_member_without_reopening_search() {
    for source in CASES {
        for (level, expected) in [
            (VerifyStateLevel::Direct, false),
            (VerifyStateLevel::KnownSpecialProperty, true),
        ] {
            let mut rt = runtime();
            let Stmt::Fact(fact) = parse(&mut rt, source) else {
                panic!("forall")
            };
            let before = memory_sizes(&rt);
            let result = rt.verify_fact(&fact, VerifyState::new(level)).unwrap();
            assert_eq!(!result.is_failed(), expected, "{source}: {level:?}");
            assert_eq!(memory_sizes(&rt), before);
        }
        let mut rt = runtime();
        let run = rt.run_litex_code(source).unwrap();
        assert!(run.success);
        let detail = project_run_detailed(&run, &rt, "test", None).stringify();
        assert!(detail.contains("ListSetInPowerSetFromMembers") && detail.contains("cite_fact_id"));
    }
}

#[test]
fn literal_event_carrier_keeps_missing_member_distinctness_and_inner_wd_boundaries() {
    for source in [
        "forall X,Y set,a X:\n    {a} $in power_set(Y)",
        "forall X set,a,b X:\n    {a,b} $in power_set(X)",
        "{1/0} $in power_set(R)",
    ] {
        let mut rt = runtime();
        let run = rt.run_litex_code(source).unwrap();
        assert!(!run.success && run.session_error.is_none(), "{source}");
        assert!(rt.run_litex_code("1 = 1").unwrap().success);
    }
}

#[test]
fn literal_event_carrier_supports_the_original_finite_expectation_definition() {
    let mut rt = runtime();
    assert!(
        rt.run_litex_code(include_str!("../../../../std/probability/main.lit"))
            .unwrap()
            .success
    );
    // The standard library now owns finite_expectation. Independently check
    // the original formula without redeclaring that public template name.
    let source = "template<Ambient set,space &FiniteProbabilitySpace<Ambient>>:\n    have fn regression_finite_expectation(X fn(outcome space.carrier) R) R = finite_set_sum(space.carrier,fn(outcome space.carrier) R {X(outcome)*space.prob({outcome})})";
    let run = rt.run_litex_code(source).unwrap();
    assert!(
        run.success,
        "{}",
        project_run_detailed(&run, &rt, "test", None).stringify()
    );
}
