use crate::ast::fact::{AtomicFact, Fact};
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime(strict: bool) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict,
        language: OutputLanguage::English,
    })
}
fn sizes(rt: &Runtime) -> Vec<(usize, usize)> {
    rt.execution_environments_stack
        .iter()
        .map(|env| {
            (
                env.facts.facts_by_id.len(),
                env.well_defined_objects.object_to_wd_id.len(),
            )
        })
        .collect()
}

#[test]
fn stored_self_builder_equality_replays_and_keeps_new_conditions() {
    let mut rt = runtime(true);
    let run = rt
        .run_litex_code(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/infer/atomic/set_builder_projection_replay.lit"
        )))
        .unwrap();
    assert!(run.success && run.session_error.is_none());
    let before = sizes(&rt);
    let tokens = Tokenizer::new()
        .tokenize("s = {fresh s: 0 = 0}", rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(goal))) =
        rt.parse(&tokens).unwrap().remove(0)
    else {
        panic!("equality")
    };
    assert!(!rt
        .verify_equal_fact_well_definedness(&goal, VerifyState::top_level())
        .unwrap()
        .is_failed());
    assert_eq!(
        sizes(&rt),
        before,
        "builder WD must not publish its binder or facts"
    );
    assert!(!rt
        .verify_equal_fact(&goal, VerifyState::top_level())
        .unwrap()
        .is_failed());
    assert_eq!(sizes(&rt), before);
}

#[test]
fn mutual_carriers_and_repeated_body_membership_terminate() {
    let mut rt = runtime(false);
    // Unit assumptions only, to exercise a cyclic checked carrier graph.
    assert!(rt.run_litex_code("have first, second set\ntrust first = {x second: x $in second}\ntrust second = {x first: x $in first}\n").unwrap().success);
    let run=rt.run_litex_code("forall element first:\n    element $in second\nforall element second:\n    element $in first\n").unwrap();
    assert!(run.success && run.session_error.is_none());
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn false_builder_and_undefined_carrier_reject_and_rollback() {
    let mut rt = runtime(true);
    assert!(rt.run_litex_code("have s set\n").unwrap().success);
    let before = sizes(&rt);
    for code in [
        "claim:\n    ? forall object s:\n        object $in {x s: 0 = 1}\n",
        "ghost = {x ghost: 0 = 0}\n",
        "0 = 1\n",
    ] {
        let run = rt.run_litex_code(code).unwrap();
        assert!(!run.success, "{code}");
        assert_eq!(sizes(&rt), before, "{code}");
    }
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn late_carrier_equalities_retain_conditions_without_selecting_or_branches() {
    for (domain, condition) in [
        ("R", "value $in Carrier"),
        ("R", "value $in Carrier and 0 = 0"),
        ("Carrier", "0 = 0 = 0"),
    ] {
        let mut rt = runtime(true);
        // The ordinary Carrier membership predates its defining equality.
        let code = format!("claim:\n    ? forall Carrier set, value R:\n        value $in Carrier\n        Carrier = {{x R: x > 0}}\n        =>:\n            value > 0\n    release thm set_builder_member(value, {{x {domain}: {condition}}})\n    value > 0\n");
        let run = rt.run_litex_code(&code).unwrap();
        assert!(run.success && run.session_error.is_none(), "{code}");
        assert_eq!(rt.execution_environments_stack.len(), 1);
    }
    for code in [
        "claim:\n    ? forall First, Second set, value R:\n        value $in Second\n        First = {x R: x > 0}\n        =>:\n            value > 0\n    release thm set_builder_member(value, {x R: x $in First or x $in Second})\n    value > 0\n",
        "claim:\n    ? forall First, Second set, value R:\n        value $in First\n        Second = {x R: x > 0}\n        =>:\n            value > 0\n    release thm set_builder_member(value, {x First: 0 = 0})\n    value > 0\n",
    ] {
        let mut rt = runtime(true);
        let before = sizes(&rt);
        let run = rt.run_litex_code(code).unwrap();
        assert!(!run.success && run.session_error.is_none(), "{code}");
        assert_eq!(rt.execution_environments_stack.len(), 1);
        assert_eq!(sizes(&rt), before, "{code}");
    }
}
