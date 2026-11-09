use litex::launch_command::{LaunchCommand, OutputLanguage};
use litex::run::RunLitexCodeResult;
use litex::runtime::Runtime;

fn runtime() -> Runtime {
    Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        litex::result_detail::OutputDetail::Detailed,
    )
}

fn check(rt: &mut Runtime, source: &str, accepted: bool) -> RunLitexCodeResult {
    let run = rt.run_litex_code(source).unwrap();
    assert_eq!(
        run.success,
        accepted,
        "{source}\n{}",
        litex::json_output::emit_run_normal(&run, rt, "continuity", None)
    );
    run
}

#[test]
fn norm_continuity_at_origin_does_not_require_a_derivative() {
    let mut rt = runtime();
    check(
        &mut rt,
        "have fn norm(p finite_seq(R,2)) R = sqrt(p(1)^2+p(2)^2)",
        true,
    );
    let continuity = check(&mut rt, "$is_multi_continuous_at(norm,(0,0),2)", true);
    let json =
        litex::json_output::project_run_detailed(&continuity, &rt, "continuity", None).stringify();
    assert!(json.contains("ContinuousMultivariableExpression"), "{json}");
    assert!(
        !json.contains("derivative_expression"),
        "continuity must not manufacture derivative evidence"
    );
    check(&mut rt, "$has_multi_limit_at(norm,(0,0),2,0)", true);
    check(&mut rt, "$has_multi_limit_at(norm,(0,0),2,1)", false);
    check(&mut rt, "$is_multi_differentiable_at(norm,(0,0),2)", false);
    check(&mut rt, "0 = 0", true);
}

#[test]
fn symbolic_coordinate_is_jointly_continuous_and_differentiable() {
    let mut rt = runtime();
    check(&mut rt, "have k closed_range(1,2)", true);
    check(
        &mut rt,
        "have fn projection(p finite_seq(R,2)) R = p(k)",
        true,
    );
    check(&mut rt, "$is_multi_continuous_at(projection,(0,0),2)", true);
    let differentiable = check(
        &mut rt,
        "$is_multi_differentiable_at(projection,(0,0),2)",
        true,
    );
    let json = litex::json_output::project_run_detailed(&differentiable, &rt, "projection", None)
        .stringify();
    assert!(
        json.contains("CoordinateProjectionDifferentiable"),
        "{json}"
    );
    // The still-symbolic coordinate value is exact. Reducing an arbitrary
    // coordinate of a homogeneous literal tuple is a separate equality route.
    check(
        &mut rt,
        "$has_multi_limit_at(projection,(0,0),2,(0,0)(k))",
        true,
    );
    check(
        &mut rt,
        "$is_multi_continuous_at(projection,(0,0,0),3)",
        false,
    );
}

#[test]
fn continuous_expression_composition_preserves_domain_and_wrong_value_rejection() {
    let mut rt = runtime();
    check(
        &mut rt,
        "have fn continuous(p finite_seq(R,2)) R = exp(sqrt(p(1)^2+p(2)^2)) + sin(p(1))",
        true,
    );
    check(&mut rt, "$is_multi_continuous_at(continuous,(0,0),2)", true);
    check(&mut rt, "$has_multi_limit_at(continuous,(0,0),2,1)", true);
    check(&mut rt, "$has_multi_limit_at(continuous,(0,0),2,0)", false);
}

#[test]
fn scalar_continuity_and_limit_replay_without_derivative_evidence() {
    let mut rt = runtime();
    let run = check(&mut rt, "have fn norm(p finite_seq(R,2)) R = sqrt(p(1)^2+p(2)^2)\n$is_multi_continuous_at(norm,(0,0),2)\n$has_multi_limit_at(norm,(0,0),2,0)", true);
    let output = litex::compile_to_lean::LitexToLeanCompiler::new(rt)
        .compile_run(&run, "norm_continuity")
        .expect("joint continuity evidence must replay");
    assert!(output.contains("semanticEuclideanContinuousSqrt"));
    assert!(output.contains("scalarContinuityToMultivariableLimit"));
}

#[test]
fn symbolic_coordinate_differentiability_has_an_explicit_lean_boundary() {
    let mut rt = runtime();
    let run = check(&mut rt, "forall k closed_range(1,2):\n    $is_multi_differentiable_at(fn(p finite_seq(R,2)) R {p(k)},(0,0),2)", true);
    let error = litex::compile_to_lean::LitexToLeanCompiler::new(rt)
        .compile_run(&run, "projection_differentiable")
        .expect_err("coordinate differentiability needs its own semantic bridge");
    assert_eq!(error.route, "Atomic/BuiltinStrategy", "{error:?}");
    assert!(
        error.message.contains("is_multi_differentiable_at"),
        "{error:?}"
    );
}
