use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::{CodeSource, Runtime};

fn runtime() -> Runtime {
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(), session: false, strict: true, language: OutputLanguage::English,
    });
    // Canonical showcases export main.lit: exercise qualified definition owners.
    rt.set_code_source(CodeSource::RootExport { export_file_id: 0 });
    rt
}

fn check(source: &str, expected: bool) -> String {
    let mut rt = runtime();
    let run = rt.run_litex_code(source).unwrap();
    assert!(run.session_error.is_none(), "{source}\n{:?}", run.session_error);
    assert_eq!(run.success, expected, "{source}");
    assert_eq!(rt.execution_environments_stack.len(), 1);
    let detailed = crate::json_output::project_run_detailed(&run, &rt, "test", None).stringify();
    // Neither positive nor negative checks may export a contradiction.
    assert!(!rt.run_litex_code("0 = 1").unwrap().success);
    detailed
}

const FIELD: &str = include_str!("../../../../examples/wd/field_application_codomain.lit");
const TEMPLATE: &str = include_str!("../../../../examples/wd/template_unique_from_typed_carrier.lit");

#[test]
fn positive_natural_predecessor_keeps_both_cited_premises_and_allows_recursion() {
    let detail = check(include_str!("../../../../examples/wd/positive_natural_predecessor.lit"), true);
    assert!(detail.contains("PredecessorFromPositiveNatural"));
    assert!(detail.contains("in_natural_proof") && detail.contains("positive_proof"));
    check("forall n N:\n    n >= 1\n    =>:\n        n - 1 $in N", true);
    check("forall n N:\n    0 < n\n    =>:\n        n - 1 $in N", true);
    for source in [
        "0 - 1 $in N", "(1 / 2) - 1 $in N",
        "forall n N:\n    n - 1 $in N",
        "forall x R:\n    x > 0\n    =>:\n        x - 1 $in N",
        "forall n Z:\n    n < 0\n    =>:\n        n - 1 $in N",
    ] { check(source, false); }
}

#[test]
fn declared_field_types_close_nested_calls_without_releasing_laws() {
    let detail = check(FIELD, true);
    assert!(detail.contains("FieldApplicationInDeclaredCodomain"));
    assert!(detail.contains("\"kind\":\"FieldAccess\""));
    assert!(detail.contains("declared_signature") && detail.contains("cite_signature_fact_id"));
    for goal in [
        "s.add(s.add(i, 0), 0) $in R",
        "s.add(s.add(0, 0), 0) $in N",
        "s.add(s.add(0, 0), 0) = 1",
    ] {
        check(&format!("{FIELD}\nthm bad:\n    ? forall s &Operation<R>:\n        {goal}"), false);
    }
    check("struct Guarded<A nonempty_set, zero A>:\n    tag N\n    call fn(x A: x != zero) A\nthm bad:\n    ? forall s &Guarded<R, 0>:\n        s.call(s.call(0)) $in R", false);
}

#[test]
fn unique_function_templates_recover_hidden_carriers_and_work_in_nested_wd() {
    let detail = check(TEMPLATE, true);
    assert!(detail.contains("template_definition"));
    assert!(detail.contains("TemplateApplicationInDeclaredCodomain"));
    check(&format!("{TEMPLATE}\nthm bad:\n    ? forall t &Point<N, R>:\n        \\selected_value<Z, R, t>(0) = t.value"), false);
    check(&format!("{TEMPLATE}\nthm bad:\n    ? forall t, u &Point<N, R>:\n        \\selected_value<N, R, t>(0) = u.value"), false);
    // A template guard is checked even when its result is a nested argument.
    let guarded = "template<S set: $is_nonempty_set(S)>:\n    have fn guarded_identity(x R) R = x\nhave fn identity(x R) R = x\n";
    check(&format!("{guarded}\nthm good:\n    ? forall S nonempty_set:\n        identity(\\guarded_identity<S>(0)) $in R"), true);
    check(&format!("{guarded}\nthm bad:\n    ? forall S set:\n        identity(\\guarded_identity<S>(0)) $in R"), false);
}

#[test]
fn set_builder_matching_infers_free_arguments_without_capturing_local_binders() {
    check(include_str!("../../../../examples/wd/forall_set_builder_matching.lit"), true);
    check("forall family power_set(power_set(R)):\n    forall a R:\n        {x R: x = a} $in family\n    =>:\n        {y R: y = y} $in family", false);
    for goal in ["{y R: not y $in U}", "{y N: y $in U}"] {
        check(&format!("forall U power_set(R), family power_set(power_set(R)):\n    forall V power_set(R):\n        {{x R: x $in V}} $in family\n    =>:\n        {goal} $in family"), false);
    }
    check("forall f, g fn(x R) R, U power_set(R), family power_set(power_set(R)):\n    forall V power_set(R):\n        {x R: f(x) $in V} $in family\n    =>:\n        {y R: g(y) $in U} $in family", false);
    check("forall U power_set(R), family power_set(power_set(R)):\n    forall V power_set(R):\n        {x R: x $in V and x > 0} $in family\n    =>:\n        {y R: y $in U or y > 0} $in family", false);
}

#[test]
fn anonymous_range_membership_uses_alpha_equality_and_keeps_bodies_and_guards() {
    let detail = check(include_str!("../../../../examples/wd/anonymous_application_range_alpha.lit"), true);
    assert!(detail.contains("AnonymousFnApplicationInFnRange"));
    assert!(detail.contains("function_equal"));
    check("forall x R:\n    fn(a R) R {0}(x) $in fn_range(fn(b R) R {1})", false);
    check("forall x R:\n    fn(a R: a > 0) R {a}(x) $in fn_range(fn(b R: b > 0) R {b})", false);
}

#[test]
fn original_showcase_sections_use_the_repaired_paths() {
    let linear = include_str!("../../../../showcases/math_concepts_in_litex/5_linear_algebra/main.lit");
    check(linear.split("thm injective_linear_map_has_trivial_kernel:").next().unwrap(), true);
    let group = include_str!("../../../../showcases/math_concepts_in_litex/6_abstract_algebra/main.lit");
    check(group.split("thm ring_homomorphism_kernel_is_ideal:").next().unwrap(), true);
    let topology = include_str!("../../../../showcases/math_concepts_in_litex/9_topology/main.lit");
    check(topology.split("thm continuous_image_of_compact_is_compact:").next().unwrap(), true);
    let newton = include_str!("../../../../showcases/math_concepts_in_litex/13_numerical_analysis_in_nutshell/main.lit");
    check(newton.split("thm newton_sqrt_two_residual_identity:").next().unwrap(), true);
}
