use crate::prelude::*;
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
fn check(rt: &mut Runtime, source: &str, expected: bool) -> crate::run::RunLitexCodeResult {
    let run = rt.run_litex_code(source).unwrap();
    assert_eq!(run.success, expected, "{source}");
    assert!(run.session_error.is_none(), "{source}");
    run
}
#[test]
fn elementary_pointwise_tests_tracer_domain_and_symbolic_formulas() {
    let mut rt = runtime();
    let source = include_str!(
        "../../../../examples/proof_nodes/atomic/by_builtin_strategy/pointwise_elementary.lit"
    );
    let run = check(&mut rt, source, true);
    let json = crate::json_output::project_run_detailed(&run, &rt, "elementary", None).stringify();
    for key in [
        "ElementaryChainRule",
        "ElementaryContinuity",
        "analytic_domain",
        "sqrt",
        "ln",
        "exp",
        "cos",
        "sin",
    ] {
        assert!(json.contains(key), "{key}");
    }
    // Fresh scope: the fixture above already stored this same derivative.
    // Inspect its constructing certificate rather than a later known-fact citation.
    let mut rt = runtime();
    let run = check(
        &mut rt,
        "$has_derivative_at(fn(x R:x>=0) R {sqrt(x)},4,1/4)",
        true,
    );
    let json = crate::json_output::project_run_detailed(&run, &rt, "elementary", None).stringify();
    assert!(json.contains("strict_margin_for_weak_guard"));
    check(
        &mut rt,
        "$has_derivative_at(fn(x R:x<=0) R {x*x},-2,-4)",
        true,
    );
    check(
        &mut rt,
        "$is_differentiable_at(fn(x R:x<=0) R {x},0)",
        false,
    );
}
#[test]
fn elementary_pointwise_tests_selection_false_neighbors_and_rollback() {
    for source in [
        "have fn wave(x R) R=sin(x*x)+exp(x)\nderivative(wave,0)=1",
        "have fn wave(x R) R=sin(x*x)+exp(x)\n0*derivative(wave,0)=0",
        "$has_derivative_at(fn(x R) R {sin(x)},0,0)",
        "$has_derivative_at(fn(x R) R {exp(x)},0,0)",
        "$has_derivative_at(fn(x R+) R {ln(x)},1,-1)",
        "$has_derivative_at(fn(x R+) R {ln(x)},0,0)",
        "$has_derivative_at(fn(x R+) R {ln(x)},-1,0)",
        "$has_derivative_at(fn(x R:x>=0) R {sqrt(x)},0,0)",
        "$has_derivative_at(fn(x R+) R {sqrt(x)},4,1/2)",
        "$has_derivative_at(fn(x R:x>=0) R {sqrt(x)},-1,0)",
    ] {
        let mut rt = runtime();
        check(&mut rt, "have anchor R=7", true);
        check(&mut rt, source, false);
        check(&mut rt, "anchor+1=8", true);
    }
    let mut rt = runtime();
    check(&mut rt, "have fn wave(x R) R=sin(x*x)+exp(x)", true);
    check(
        &mut rt,
        "claim:\n    ? 0=1\n    $has_derivative_at(wave,0,1)\n    0=1",
        false,
    );
    check(&mut rt, "derivative(wave,0)=1", false);
    check(&mut rt, "$has_derivative_at(wave,0,1)", true);
    check(&mut rt, "derivative(wave,0)=1", true);
}
#[test]
fn elementary_pointwise_tests_restricted_permissions_and_missing_leaf() {
    let mut rt = runtime();
    check(&mut rt, "forall f fn(x R) R+:\n    f(0)!=0", true);
    check(&mut rt, "forall f fn(x R) C*:\n    f(0)!=0", true);
    check(&mut rt, "forall f fn(x R) R:\n    f(0)!=0", false);
    check(&mut rt, "forall f fn(x R:x>0) R+:\n    f(0)!=0", false);
    check(&mut rt, "have fn wave(x R) R=sin(x*x)+exp(x)", true);
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize("$has_derivative_at(wave,0,1)", rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(goal) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("fact")
    };
    assert!(rt
        .verify_fact(&goal, VerifyState::new(VerifyStateLevel::BuiltinRule))
        .unwrap()
        .is_failed());
    check(&mut rt,"claim:\n    ? forall f fn(x R) R:\n        $is_differentiable_at(fn(t R) R {exp(f(t))},0)\n    $is_differentiable_at(fn(t R) R {exp(f(t))},0)",false);
}
#[test]
fn elementary_pointwise_tests_explicit_laws_require_actual_graphs_and_domains() {
    for name in ["exp", "ln", "sin", "cos", "sqrt"] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(format!(
            "examples/stmt_nodes/release_and_expand/builtin_thm/fn_derivative_at_{name}.lit"
        ));
        check(
            &mut runtime(),
            &std::fs::read_to_string(path).unwrap(),
            true,
        );
    }
    for source in [
        "have fn f(x R) R=x\nrelease thm fn_derivative_at_real_interior(0)\nrelease thm fn_derivative_at_exp(f,0)",
        "have fn f(x R:x>=0) R=sqrt(x)\nrelease thm fn_derivative_at_sqrt(f,0)",
        "have fn f(x R+) R=ln(x)\nrelease thm fn_derivative_at_ln(f,-1)",
        "have fn f(x R) R=sin(x)\nrelease thm fn_derivative_at_cos(f,0)"
    ] {check(&mut runtime(),source,false);}
}
#[test]
fn elementary_pointwise_tests_reading_keeps_elementary_and_domain_evidence() {
    let source = "have fn f(x R) R=sin(x*x)+exp(x)\n$has_derivative_at(f,0,1)\nderivative(f,0)=1";
    let result = crate::reading::build_reading(
        &crate::reading::ReadingInput::Source(source.into()),
        true,
        OutputLanguage::English,
    );
    assert!(result.success);
    let json = result.document.stringify();
    for key in [
        "Elementary",
        "ElementaryRealFunction",
        "domain",
        "argument",
        "Sin",
        "Exp",
    ] {
        assert!(json.contains(key), "{key}");
    }
    assert!(!json.contains("\"coverage\":\"missing\""));
}
