use crate::prelude::*;
fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}
fn check(rt: &mut Runtime, source: &str, success: bool) {
    let run = rt.run_litex_code(source).unwrap();
    assert_eq!(run.success, success, "{source}");
    assert!(run.session_error.is_none(), "{source}");
}
#[test]
fn pointwise_continuity_direct_arithmetic_and_nested_composition() {
    let mut rt = runtime();
    let source = include_str!(
        "../../../../examples/proof_nodes/atomic/by_builtin_strategy/pointwise_continuity.lit"
    );
    let run = rt.run_litex_code(source).unwrap();
    assert!(run.success && run.session_error.is_none());
    let json = crate::json_output::project_run_detailed(&run, &rt, "test", None).stringify();
    for tag in [
        "PointwiseContinuity",
        "body_equal",
        "body_well_defined",
        "denominator_nonzero",
        "NaturalPower",
        "outer_point",
        "Compose",
    ] {
        assert!(json.contains(tag), "{tag}");
    }
}
#[test]
fn pointwise_continuity_missing_leaves_and_wrong_composite_points_remain_unproved() {
    for source in [
        "claim:\n    ? forall f,g fn(x R) R:\n        $is_continuous_at(f,0)\n        =>:\n            $is_continuous_at(fn(t R) R {f(t)+g(t)},0)\n    $is_continuous_at(fn(t R) R {f(t)+g(t)},0)",
        "claim:\n    ? forall f,g,h fn(x R) R:\n        $is_continuous_at(f,0)\n        $is_continuous_at(g,0)\n        $is_continuous_at(h,0)\n        =>:\n            $is_continuous_at(fn(t R) R {f(g(h(t)))},0)\n    $is_continuous_at(fn(t R) R {f(g(h(t)))},0)",
        "have fn reciprocal(t R*) R=1/t\n$is_continuous_at(reciprocal,0)",
    ] {
        let mut rt=runtime();check(&mut rt,"have anchor R=7",true);
        check(&mut rt,source,false);check(&mut rt,"anchor+1=8",true);
    }
}
#[test]
fn pointwise_continuity_keeps_actual_domain_and_isolated_point_semantics() {
    check(
        &mut runtime(),
        "have fn square(x {0}) R=x*x\n$is_continuous_at(square,0)",
        true,
    );
    check(
        &mut runtime(),
        "have fn guarded(x R:x>0) R=x*x\n$is_continuous_at(guarded,0)",
        false,
    );
    check(
        &mut runtime(),
        "have fn reciprocal(x R*) R=1/x\n$is_continuous_at(reciprocal,2)",
        true,
    );
}
#[test]
fn pointwise_continuity_respects_search_ceiling_and_failed_scope() {
    let mut rt = runtime();
    check(&mut rt, "have fn square(x R) R=x*x", true);
    let blocks = crate::tokenize::Tokenizer::new()
        .tokenize("$is_continuous_at(square,0)", rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(goal) = rt.parse(&blocks).unwrap().remove(0) else {
        panic!("fact")
    };
    assert!(rt
        .verify_fact(&goal, VerifyState::new(VerifyStateLevel::BuiltinRule))
        .unwrap()
        .is_failed());
    check(
        &mut rt,
        "claim:\n    ? 0=1\n    $is_continuous_at(square,0)\n    0=1",
        false,
    );
    assert!(rt
        .verify_fact(&goal, VerifyState::new(VerifyStateLevel::BuiltinRule))
        .unwrap()
        .is_failed());
    check(&mut rt, "$is_continuous_at(square,0)", true);
}
#[test]
fn pointwise_continuity_lean_remains_explicitly_unsupported() {
    let mut rt = runtime();
    let run = rt
        .run_litex_code("have fn square(x R) R=x*x\n$is_continuous_at(square,0)")
        .unwrap();
    assert!(run.success);
    let err = crate::compile_to_lean::LitexToLeanCompiler::new(rt)
        .compile_run(&run, "pointwise")
        .unwrap_err();
    assert!(
        err.message.contains("not supported") || err.message.contains("Unsupported"),
        "{err}"
    );
}
