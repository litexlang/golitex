use crate::parse::builtin_aliases::{canonical_builtin_name, BuiltinAliasKind, BUILTIN_ALIASES};
use crate::prelude::*;

#[test]
fn builtin_short_names_parse_to_the_existing_objects() {
    for (short, long) in [
        ("deriv(1,2)", "derivative(1,2)"),
        ("pderiv(1,2,3,4)", "partial_derivative(1,2,3,4)"),
        ("grad_at(1,2,3)", "gradient_at(1,2,3)"),
        (
            "set_sum({1,2},fn(x R)R{x})",
            "finite_set_sum({1,2},fn(x R)R{x})",
        ),
        (
            "set_prod({1,2},fn(x R)R{x})",
            "finite_set_product({1,2},fn(x R)R{x})",
        ),
        ("integ(1,2,3)", "integral(1,2,3)"),
        (
            "deriv(fn(x R)R{integ(fn(t R)R{t},0,x)},2)",
            "derivative(fn(x R)R{integral(fn(t R)R{t},0,x)},2)",
        ),
    ] {
        assert_eq!(
            parsed(&format!("eval {short}")),
            parsed(&format!("eval {long}"))
        );
    }
}

#[test]
fn builtin_short_names_parse_to_the_existing_positive_and_negative_facts() {
    for &(short, long, kind) in BUILTIN_ALIASES {
        if kind != BuiltinAliasKind::Predicate {
            continue;
        }
        let count = crate::parse::real_analysis_fact_arity(long).unwrap();
        let args = vec!["1"; count].join(",");
        for sign in ["", "not "] {
            assert_eq!(
                parsed(&format!("{sign}${short}({args})")),
                parsed(&format!("{sign}${long}({args})")),
                "different facts for {sign}{short}"
            );
        }
    }
}

#[test]
fn builtin_short_names_parse_to_canonical_theorem_calls_and_ids() {
    for &(short, long, kind) in BUILTIN_ALIASES {
        if kind != BuiltinAliasKind::Theorem {
            continue;
        }
        let id = crate::builtin_theorem::BuiltinTheoremId::from_name(long).unwrap();
        assert_eq!(
            crate::builtin_theorem::BuiltinTheoremId::from_name(short),
            Some(id)
        );
        assert_eq!(id.as_str(), long);
        let args = vec!["1"; id.arity()].join(",");
        for command in ["release thm", "by thm"] {
            assert_eq!(
                parsed(&format!("{command} {short}({args})")),
                parsed(&format!("{command} {long}({args})")),
                "different calls for {short}"
            );
        }
        assert_eq!(
            parsed(&format!("by thm {short}({args}) => 1=1")),
            parsed(&format!("by thm {long}({args}) => 1=1"))
        );
    }
}

#[test]
fn builtin_short_names_are_unique_reserved_and_context_specific() {
    for (index, &(short, long, kind)) in BUILTIN_ALIASES.iter().enumerate() {
        assert!(BUILTIN_ALIASES[..index]
            .iter()
            .all(|(name, _, _)| *name != short));
        assert!(crate::builtin_theorem::is_reserved_builtin_name(short));
        assert_eq!(canonical_builtin_name(short, kind), long);
        for other in [
            BuiltinAliasKind::Object,
            BuiltinAliasKind::Predicate,
            BuiltinAliasKind::Theorem,
        ] {
            if other != kind {
                assert_eq!(canonical_builtin_name(short, other), short);
            }
        }
        for code in [
            format!("let {short}=0"),
            format!("forall {short} R:\n    {short}={short}"),
        ] {
            let mut rt = runtime();
            assert!(rt.run_litex_code("have retained R=2").unwrap().success);
            let result = rt.run_litex_code(&code).unwrap();
            assert!(!result.success, "reserved name accepted: {code}");
            let error = format!("{:?}{:?}", result.input_error, result.session_error);
            assert!(error.contains("reserved builtin name"), "{error}");
            assert!(result.session_error.is_none());
            assert!(rt.run_litex_code("retained+1=3").unwrap().success);
        }
    }
}

#[test]
fn builtin_short_names_preserve_namespace_aliases_and_similar_identifiers() {
    let parse = |source: &str| {
        let mut rt = runtime();
        let config = crate::module_manager::parse_litex_config(
            "[import]\nLibrary=\"library\"\n[alias]\nderiv=Library::defs\ndiff_at=Library::defs\ninteg_add=Library::defs\n[export]\nmain=\"main.lit\"\n",
            std::path::Path::new("/builtin-alias-test"),
            std::path::Path::new("/std"),
        ).unwrap();
        rt.global_module_manager.set_root_config(config);
        let library = crate::module_manager::parse_litex_config(
            "[export]\ndefs=\"defs.lit\"\n",
            std::path::Path::new("/builtin-alias-test/library"),
            std::path::Path::new("/std"),
        )
        .unwrap();
        rt.global_module_manager
            .record_import(
                "Library".into(),
                "/builtin-alias-test/library".into(),
                library,
            )
            .unwrap();
        let blocks = crate::tokenize::Tokenizer::new()
            .tokenize(source, rt.current_file.clone())
            .unwrap();
        rt.parse(&blocks).unwrap()
    };
    for (short, full) in [
        ("eval deriv::value", "eval Library::defs::value"),
        ("$diff_at::positive(1)", "$Library::defs::positive(1)"),
        (
            "by thm integ_add::add_zero(1) => 1=1",
            "by thm Library::defs::add_zero(1) => 1=1",
        ),
    ] {
        assert_eq!(parse(short), parse(full));
    }
    let mut rt = runtime();
    assert!(rt.run_litex_code(
        "let deriv_value=2\nlet integrate=3\nlet int=4\nlet sum_set=5\nlet prod_set=6\nderiv_value+integrate+int+sum_set+prod_set=20"
    ).unwrap().success);
}

#[test]
fn builtin_short_names_execute_uniform_continuity_and_multivariable_objects() {
    let uniform = include_str!("../../../examples/real_analysis/lipschitz_uniform_continuous.lit")
        .replace("$is_uniformly_continuous(", "$unif_cont(");
    let multivariable = include_str!("../../../examples/real_analysis/multivariable/main.lit")
        .replace("\npartial_derivative(", "\npderiv(")
        .replace("\ngradient_at(", "\ngrad_at(");
    for (name, source) in [("unif_cont", uniform), ("pderiv/grad_at", multivariable)] {
        let mut rt = runtime();
        let run = rt.run_litex_code(&source).unwrap();
        assert!(
            run.success,
            "{name}: {}",
            crate::json_output::emit_run_normal(&run, &rt, name, None)
        );
    }
}

#[test]
fn builtin_short_names_keep_arity_wd_and_failure_recovery() {
    let mut rt = runtime();
    assert!(
        rt.run_litex_code("have fn square(x R)R=x^2\nhave fn broken(x R)R=x\n")
            .unwrap()
            .success
    );
    for code in [
        "eval deriv(square)",
        "eval integ(square,0)",
        "eval set_sum({1,2})",
        "eval set_prod({1,2},square,0)",
        "eval grad_at(square,3)",
        "eval pderiv(square,3,2)",
        "$diff_at(square)",
        "$has_deriv_at(square,3)",
        "release thm deriv_add(square)",
        "release thm integ_add(square)",
        "deriv(square,3)=6",
        "0*integ(square,0,1)=0",
        "$has_deriv_at(square,3,7)",
        "$diff_at(fn(x R)R{abs(x)},0)",
        "release thm deriv_add(square,square,broken,3,6,6)",
        "eval pderiv(square,3,0,1)",
    ] {
        let rejected = rt.run_litex_code(code).unwrap();
        assert!(!rejected.success, "accepted {code}");
        assert!(
            rejected.session_error.is_none(),
            "{code}: {:?}",
            rejected.session_error
        );
        assert!(rt.run_litex_code("square(3)=9").unwrap().success);
    }
    assert!(
        rt.run_litex_code("$has_deriv_at(square,3,6)")
            .unwrap()
            .success
    );
    assert!(rt.run_litex_code("derivative(square,3)=6").unwrap().success);
    assert!(rt.run_litex_code("deriv(square,3)=6").unwrap().success);
}

#[test]
fn builtin_short_names_execute_existing_theorem_fixtures() {
    for &(short, long, kind) in BUILTIN_ALIASES {
        if kind != BuiltinAliasKind::Theorem {
            continue;
        }
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("examples/stmt_nodes/release_and_expand/builtin_thm")
            .join(format!("{long}.lit"));
        let source = std::fs::read_to_string(path).unwrap();
        let source = source.replace(long, short);
        let mut rt = runtime();
        let run = rt.run_litex_code(&source).unwrap();
        assert!(
            run.success,
            "{short}: {}",
            crate::json_output::emit_run_normal(&run, &rt, short, None)
        );
    }
}

#[test]
fn builtin_short_names_tracer_keeps_canonical_json() {
    let short = include_str!("../../../examples/wd/builtin_short_names.lit");
    let mut rt = runtime();
    let run = rt.run_litex_code(short).unwrap();
    assert!(
        run.success,
        "{}",
        crate::json_output::emit_run_normal(&run, &rt, "short_names", None)
    );
    let normal = crate::json_output::emit_run_normal(&run, &rt, "short_names", None);
    let detailed = crate::json_output::emit_run_detailed(&run, &rt, "short_names", None);
    for name in [
        "derivative(",
        "integral(",
        "finite_set_sum(",
        "finite_set_product(",
    ] {
        assert!(normal.contains(name), "missing canonical output {name}");
        assert!(
            detailed.contains(name),
            "missing canonical detailed output {name}"
        );
    }
}

#[test]
fn builtin_short_names_keep_lean_output_and_existing_unsupported_routes() {
    let original_bt = include_str!(
        "../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_derivative_at_add.lit"
    );
    let short_bt = original_bt.replace("fn_derivative_at_add", "deriv_add");
    let compile = |source: &str| {
        let mut rt = runtime();
        let run = rt.run_litex_code(source).unwrap();
        assert!(run.success);
        crate::compile_to_lean::compile_run(&run, rt, "ShortNames")
            .map_err(|error| error.to_string())
    };
    for (short, canonical, supported) in [
        (
            "have fn square(x R)R=x^2\n$has_deriv_at(square,3,6)\nderiv(square,3)=6",
            "have fn square(x R)R=x^2\n$has_derivative_at(square,3,6)\nderivative(square,3)=6",
            true,
        ),
        (
            "have fn identity(x R)R=x\nset_sum({1,2,3},identity)=6\nset_prod({1,2,3},identity)=6",
            "have fn identity(x R)R=x\nfinite_set_sum({1,2,3},identity)=6\nfinite_set_product({1,2,3},identity)=6",
            true,
        ),
        (short_bt.as_str(), original_bt, true),
        (
            "have fn square(x R)R=x^2\nrelease thm riemann_integral_power(square,0,1,2)\ninteg(square,0,1)=1/3",
            "have fn square(x R)R=x^2\nrelease thm riemann_integral_power(square,0,1,2)\nintegral(square,0,1)=1/3",
            false,
        ),
        (
            "have fn square(x R)R=x^2\n$cont_left(square,3)",
            "have fn square(x R)R=x^2\n$is_continuous_left(square,3)",
            false,
        ),
    ] {
        let short_result = compile(short);
        let canonical_result = compile(canonical);
        assert_eq!(short_result.is_ok(), supported, "{short_result:?}");
        assert_eq!(short_result, canonical_result);
    }
}

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

fn parsed(source: &str) -> Vec<Stmt> {
    let mut rt = runtime();
    let blocks = crate::tokenize::Tokenizer::new()
        .tokenize(source, rt.current_file.clone())
        .unwrap();
    rt.parse(&blocks).unwrap()
}
