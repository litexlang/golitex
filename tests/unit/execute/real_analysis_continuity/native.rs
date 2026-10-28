use crate::launch_command::{LaunchCommand, OutputLanguage};
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
fn check(rt: &mut Runtime, code: &str, expected: bool) {
    let run = rt.run_litex_code(code).unwrap();
    assert_eq!(
        run.success,
        expected,
        "{code}\n{}",
        crate::json_output::emit_run_detailed(&run, rt, "test", None)
    );
    assert!(run.session_error.is_none(), "{code}");
}
fn fixture(path: &str) -> String {
    std::fs::read_to_string(std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(path)).unwrap()
}
#[test]
fn native_analysis_examples_are_strict_and_standalone() {
    for name in [
        "continuity_limits",
        "cauchy_definition",
        "lipschitz_uniform_continuous",
        "real_sequence_completeness",
    ] {
        check(
            &mut runtime(),
            &fixture(&format!("examples/real_analysis/{name}.lit")),
            true,
        );
    }
    for name in [
        "exp", "ln", "log", "sin", "cos", "tan", "cot", "sec", "csc", "arcsin", "arccos", "arctan",
        "arccot", "sinh", "cosh", "tanh", "coth", "sech", "csch", "sqrt",
    ] {
        check(
            &mut runtime(),
            &fixture(&format!(
                "examples/stmt_nodes/release_and_expand/builtin_thm/fn_continuous_{name}.lit"
            )),
            true,
        );
    }
}
#[test]
fn sequence_properties_accept_both_exact_interfaces_and_eliminate_definitions() {
    for ty in ["seq(R)", "fn(k N+) R"] {
        check(&mut runtime(),&format!("claim:\n    ? forall a {ty}:\n        $is_seq_nondecreasing(a)\n        =>:\n            a(1)<=a(2)\n    a(1)<=a(2)"),true);
        check(&mut runtime(),&format!("claim:\n    ? forall a {ty}:\n        $is_seq_bounded(a)\n        =>:\n            exist B R st {{$is_real_upper_bound(fn_range(a),B)}}\n    obtain upper from exist B R st {{$is_real_upper_bound(fn_range(a),B)}}\n    witness exist B R st {{$is_real_upper_bound(fn_range(a),B)}} from upper"),true);
    }
}
#[test]
fn property_tags_do_not_collapse_and_invalid_signatures_are_rejected() {
    for code in [
        "claim:\n    ? forall a seq(R):\n        $is_seq_nondecreasing(a)\n        =>:\n            $is_seq_nonincreasing(a)\n    $is_seq_nonincreasing(a)",
        "claim:\n    ? forall A power_set(R):\n        $is_real_bounded_above(A)\n        =>:\n            $is_real_bounded_below(A)\n    $is_real_bounded_below(A)",
        "have a finite_seq(R,3)\n$is_seq_cauchy(a)",
        "have a fn(k N) R\n$is_seq_convergent(a)",
        "have a seq(C)\n$is_seq_nondecreasing(a)",
    ] {check(&mut runtime(),code,false);}
}
#[test]
fn continuity_requires_point_domain_and_lipschitz_constant_is_nonnegative() {
    for code in [
        "release thm fn_continuous_at_identity(fn(x R+) R{x},0)",
        "release thm fn_continuous_at_constant(fn(x R) R{x},0,1)",
        "release thm fn_continuous_log(fn(x R+) R{log(2,x)},1)",
        "release thm fn_lipschitz_from_estimate(fn(x {}) R{x},-1)",
        "release thm fn_lipschitz_from_estimate(fn(x {}) R{x},i)",
        "release thm fn_continuous_at_to_limit(fn(x {0}) R{0},0)",
        "release thm fn_continuous_sqrt(fn(x R:x>=0) R{x})",
    ] {
        check(&mut runtime(), code, false);
    }
}
#[test]
fn false_inferences_and_failed_claims_do_not_leak() {
    let mut rt = runtime();
    check(&mut rt, "have anchor R=7", true);
    check(&mut rt, "have fn identity(x R) R=x", true);
    check(
        &mut rt,
        "release thm fn_continuous_identity(identity)",
        true,
    );
    check(&mut rt, "$is_uniformly_continuous(identity)", false);
    check(&mut rt, "$is_lipschitz(identity,1)", false);
    check(&mut rt, "have fn fresh_identity(x R) R=x", true);
    // Continuity of a definitional identity is directly searchable, so use a
    // Lipschitz release as the claim-local fact that must not escape rejection.
    check(
        &mut rt,
        "claim:\n    ? 0=1\n    release thm fn_lipschitz_from_estimate(fresh_identity,1)\n    0=1",
        false,
    );
    check(&mut rt, "$is_lipschitz(fresh_identity,1)", false);
    check(&mut rt, "anchor+1=8", true);
}
#[test]
fn bound_selectors_consume_candidates_and_keep_output_boundaries() {
    for name in ["sup", "inf"] {
        let cert = if name == "sup" {
            "is_real_least_upper_bound"
        } else {
            "is_real_greatest_lower_bound"
        };
        let code =
            format!("forall A power_set(R),L R:\n    ${cert}(A,L)\n    =>:\n        {name}(A)=L");
        let mut rt = runtime();
        let run = rt.run_litex_code(&code).unwrap();
        assert!(run.success);
        let output = crate::json_output::project_run_detailed(&run, &rt, "test", None).stringify();
        assert!(
            output.contains("selection")
                && output.contains("SelectedValue")
                && output.contains("premises")
        );
        let latex =
            crate::compile_to_latex::to_latex_from_source(&code, OutputLanguage::English).unwrap();
        assert!(latex.contains(&format!("\\{name}")));
        let lean = crate::compile_to_lean::LitexToLeanCompiler::new(rt)
            .compile_run(&run, "real_bound")
            .expect("bound selectors replay their checked candidate certificate");
        let selector = if name == "sup" { "supremum" } else { "infimum" };
        assert!(lean.contains(&format!("Litex.{selector}Value_eq_certificate")));
        assert!(!lean.contains("sorry"));
        for set in ["{}", "R", "{i}", "{0}"] {
            check(
                &mut runtime(),
                &format!("let candidate={name}({set})"),
                false,
            );
            check(&mut runtime(), &format!("0*{name}({set})=0"), false);
        }
    }
}
#[test]
fn continuity_evidence_is_retained_and_lean_fails_closed() {
    let code = fixture("examples/real_analysis/lipschitz_uniform_continuous.lit");
    let mut rt = runtime();
    let run = rt.run_litex_code(&code).unwrap();
    assert!(run.success);
    let json = crate::json_output::project_run_detailed(&run, &rt, "test", None).stringify();
    assert!(json.contains("checked_real_function_analysis") && json.contains("requirement"));
    let error = crate::compile_to_lean::LitexToLeanCompiler::new(rt)
        .compile_run(&run, "native_continuity")
        .unwrap_err();
    assert!(error.message.contains("not supported"), "{error}");
}
#[test]
fn checked_completeness_calls_keep_source_steps_and_actual_conclusion() {
    assert_eq!(
        fixture("src/execute/execute_by_stmt/builtin_thm/real_sequence_completeness.lit"),
        fixture("examples/real_analysis/real_sequence_completeness.lit")
    );
    for (name, premises, conclusion) in [
        (
            "sequence_monotone_bounded_above",
            "$is_seq_nondecreasing(a)\n        $is_seq_bounded_above(a)",
            "exist L R st {$has_seq_limit(a,L)}",
        ),
        (
            "sequence_monotone_bounded_below",
            "$is_seq_nonincreasing(a)\n        $is_seq_bounded_below(a)",
            "exist L R st {$has_seq_limit(a,L)}",
        ),
        (
            "sequence_cauchy_convergent",
            "$is_seq_cauchy(a)",
            "$is_seq_convergent(a)",
        ),
        (
            "sequence_cauchy_bounded",
            "$is_seq_cauchy(a)",
            "$is_seq_bounded(a)",
        ),
        (
            "sequence_convergent_bounded",
            "$is_seq_convergent(a)",
            "$is_seq_bounded(a)",
        ),
    ] {
        for ty in ["seq(R)", "fn(k N+) R"] {
            let code=format!("claim:\n    ? forall a {ty}:\n        {premises}\n        =>:\n            {conclusion}\n    release thm {name}(a)");
            let mut rt = runtime();
            let run = rt.run_litex_code(&code).unwrap();
            assert!(run.success, "{name} {ty}");
            let output =
                crate::json_output::project_run_detailed(&run, &rt, "test", None).stringify();
            assert!(
                output.contains("derivation_steps")
                    && output.contains(name)
                    && output.contains("conclusion"),
                "{name}"
            );
        }
    }
}

#[test]
fn every_new_analysis_builtin_has_a_runnable_standalone_contract() {
    for name in [
        "real_supremum_exists",
        "real_infimum_exists",
        "real_supremum_selected",
        "real_infimum_selected",
        "sequence_cauchy_from_epsilon",
        "sequence_cauchy_tail",
        "sequence_convergent_from_limit",
        "sequence_limit_from_convergent",
        "sequence_strict_increasing_nondecreasing",
        "sequence_strict_decreasing_nonincreasing",
        "sequence_bounded_from_bounds",
        "sequence_constant_properties",
        "sequence_limit_cauchy",
        "fn_continuous_from_pointwise",
        "fn_continuous_at",
        "fn_uniform_from_epsilon",
        "fn_uniform_control",
        "fn_lipschitz_from_estimate",
        "fn_lipschitz_uniform",
        "fn_uniform_continuous",
        "fn_continuous_at_from_epsilon",
        "fn_continuous_at_control",
        "fn_continuous_at_constant",
        "fn_continuous_at_identity",
        "fn_continuous_at_from_limit",
        "fn_continuous_at_to_limit",
        "fn_continuous_at_neg",
        "fn_continuous_at_abs",
        "fn_continuous_at_scale",
        "fn_continuous_at_power",
        "fn_continuous_at_add",
        "fn_continuous_at_subtract",
        "fn_continuous_at_multiply",
        "fn_continuous_at_divide",
        "fn_continuous_at_compose",
        "fn_continuous_left_from_epsilon",
        "fn_continuous_left_control",
        "fn_continuous_left_constant",
        "fn_continuous_left_identity",
        "fn_continuous_left_from_limit",
        "fn_continuous_left_to_limit",
        "fn_continuous_left_neg",
        "fn_continuous_left_abs",
        "fn_continuous_left_scale",
        "fn_continuous_left_power",
        "fn_continuous_left_add",
        "fn_continuous_left_subtract",
        "fn_continuous_left_multiply",
        "fn_continuous_left_divide",
        "fn_continuous_left_compose",
        "fn_continuous_right_from_epsilon",
        "fn_continuous_right_control",
        "fn_continuous_right_constant",
        "fn_continuous_right_identity",
        "fn_continuous_right_from_limit",
        "fn_continuous_right_to_limit",
        "fn_continuous_right_neg",
        "fn_continuous_right_abs",
        "fn_continuous_right_scale",
        "fn_continuous_right_power",
        "fn_continuous_right_add",
        "fn_continuous_right_subtract",
        "fn_continuous_right_multiply",
        "fn_continuous_right_divide",
        "fn_continuous_right_compose",
        "fn_continuous_at_to_left",
        "fn_continuous_at_to_right",
        "fn_continuous_from_sides",
        "fn_continuous_constant",
        "fn_continuous_identity",
        "fn_continuous_exp",
        "fn_continuous_ln",
        "fn_continuous_log",
        "fn_continuous_sin",
        "fn_continuous_cos",
        "fn_continuous_tan",
        "fn_continuous_cot",
        "fn_continuous_sec",
        "fn_continuous_csc",
        "fn_continuous_arcsin",
        "fn_continuous_arccos",
        "fn_continuous_arctan",
        "fn_continuous_arccot",
        "fn_continuous_sinh",
        "fn_continuous_cosh",
        "fn_continuous_tanh",
        "fn_continuous_coth",
        "fn_continuous_sech",
        "fn_continuous_csch",
        "fn_continuous_sqrt",
        "fn_limit_at_continuous_compose",
        "fn_limit_at_punctured_compose",
        "sequence_monotone_bounded_above",
        "sequence_monotone_bounded_below",
        "sequence_cauchy_bounded",
        "sequence_cauchy_convergent",
        "sequence_convergent_bounded",
    ] {
        let id = crate::builtin_theorem::BuiltinTheoremId::from_name(name).unwrap();
        assert_eq!(id.as_str(), name);
        check(
            &mut runtime(),
            &fixture(&format!(
                "examples/stmt_nodes/release_and_expand/builtin_thm/{name}.lit"
            )),
            true,
        );
    }
}
#[test]
fn persistent_counterexamples_and_nearest_negative_controls_are_checked() {
    for name in [
        "open_interval_bounds",
        "isolated_point_continuity",
        "continuous_not_uniform",
        "jump_discontinuity",
        "empty_set_bounded",
        "composition_needs_avoidance",
        "absolute_value_from_sides",
        "reciprocal_continuity",
        "unbounded_sequence",
        "harmonic_sequence_convergence",
        "real_bound_negations",
        "empty_domain_continuity",
        "local_composition_removable_centre",
    ] {
        check(
            &mut runtime(),
            &fixture(&format!("examples/real_analysis/{name}.lit")),
            true,
        );
    }
    for name in [
        "analysis_sup_unknown",
        "analysis_inf_unknown",
        "analysis_sup_empty_bounded",
        "analysis_inf_empty_bounded",
        "analysis_continuity_missing_point",
        "analysis_negative_lipschitz",
        "analysis_isolated_limit",
        "analysis_division_at_zero",
        "analysis_wrong_continuous_sum",
        "analysis_continuous_not_uniform_rule",
        "analysis_uniform_not_lipschitz_rule",
        "analysis_composition_missing_avoidance",
        "analysis_composition_missing_domain",
        "analysis_composition_undefined_centre",
        "analysis_unbounded_limit_selection",
        "analysis_no_limit_value_guess",
    ] {
        let mut rt = runtime();
        check(&mut rt, "have anchor R=7", true);
        let source = fixture(&format!("examples/wd_negative/{name}.lit"));
        let blocks = crate::tokenize::Tokenizer::new()
            .tokenize(&source, rt.current_file.clone())
            .unwrap();
        let stmts = rt.parse(&blocks).unwrap();
        for stmt in &stmts[..stmts.len() - 1] {
            assert!(
                !rt.exec_stmt(stmt).unwrap().is_failed(),
                "{name}: prefix must pass"
            );
        }
        let before: usize = rt
            .execution_environments_stack
            .iter()
            .map(|env| env.facts.facts_by_id.len())
            .sum();
        let failed = rt.exec_stmt(stmts.last().unwrap()).unwrap();
        assert!(failed.is_failed(), "{name}");
        let after: usize = rt
            .execution_environments_stack
            .iter()
            .map(|env| env.facts.facts_by_id.len())
            .sum();
        assert_eq!(before, after, "{name}: failed statement leaked facts");
        check(&mut rt, "anchor+1=8", true);
    }
}
