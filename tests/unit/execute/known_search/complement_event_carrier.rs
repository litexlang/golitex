use super::*;
use crate::execute::execute_fact_stmt::VerifyStateLevel;
use crate::json_output::project_run_detailed;

const OWN: &str = "forall X set,B set:\n    set_minus(X,B) $in power_set(X)";
const ALIAS: &str =
    "forall X,Y set,B set:\n    X = Y\n    =>:\n        set_minus(X,B) $in power_set(Y)";
const GUARD: &str = "forall X set,p fn(E power_set(X)) R,B set:\n    p(set_minus(X,B)) > 0\n    =>:\n        p(set_minus(X,B)) > 0";

#[test]
fn complement_event_carrier_uses_identity_or_stored_equality_at_the_existing_ceiling() {
    for source in [OWN, ALIAS, GUARD] {
        for (level, expected) in [
            (VerifyStateLevel::Direct, false),
            (VerifyStateLevel::KnownSpecialProperty, true),
        ] {
            let mut rt = runtime();
            let Stmt::Fact(fact) = parse(&mut rt, source) else {
                panic!("forall")
            };
            let before = memory_sizes(&rt);
            let checked = rt.verify_fact(&fact, VerifyState::new(level)).unwrap();
            assert_eq!(!checked.is_failed(), expected, "{source}: {level:?}");
            assert_eq!(memory_sizes(&rt), before);
        }
        let mut rt = runtime();
        let run = rt.run_litex_code(source).unwrap();
        assert!(run.success && run.session_error.is_none());
        let detailed = project_run_detailed(&run, &rt, "test", None).stringify();
        assert!(detailed.contains("SetMinusInPowerSetOfLeft"), "{detailed}");
        assert!(detailed.contains("left_equal_carrier"));
    }
}

#[test]
fn complement_event_carrier_preserves_stored_member_priority_and_cached_call_wd() {
    for cached in [false, true] {
        let mut rt = runtime();
        exec_ok(&mut rt, "have X set");
        exec_ok(&mut rt, "have B set");
        exec_ok(&mut rt, "have fn p(E power_set(X)) R = 0");
        if cached {
            exec_ok(&mut rt, "p(set_minus(X,B)) = p(set_minus(X,B))");
        }
        let fact = Fact::AtomicFact(atomic(&mut rt, "p(set_minus(X,B)) $in R"));
        let before = memory_sizes(&rt);
        assert!(!rt
            .verify_fact(&fact, builtin_disabled())
            .unwrap()
            .is_failed());
        assert_eq!(memory_sizes(&rt), before);
    }
    let mut rt = runtime();
    let run = rt
        .run_litex_code("forall X set,A power_set(X),B set:\n    set_minus(A,B) $in power_set(X)")
        .unwrap();
    let detailed = project_run_detailed(&run, &rt, "test", None).stringify();
    assert!(run.success && detailed.contains("SetMinusInPowerSet\""));
    assert!(!detailed.contains("SetMinusInPowerSetOfLeft"));
}

#[test]
fn complement_event_carrier_refuses_wrong_carriers_and_preserves_other_guards() {
    for source in [
        "forall X,Y set,B set:\n    set_minus(X,B) $in power_set(Y)",
        "forall X,Y set:\n    set_minus(X,Y) $in power_set(Y)",
        "have fn p(E power_set(R): $is_nonempty_set(E)) R = 0\np(set_minus(R,R)) $in R",
        "set_minus({1/0},{}) $in power_set({1/0})",
    ] {
        let mut rt = runtime();
        let run = rt.run_litex_code(source).unwrap();
        assert!(!run.success && run.session_error.is_none(), "{source}");
        assert!(rt.run_litex_code("1 = 1").unwrap().success);
    }
}
