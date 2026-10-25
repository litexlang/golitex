use crate::execute::execute_fact_stmt::VerifyStateLevel;
use crate::prelude::*;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}
fn check(rt: &mut Runtime, source: &str, wanted: bool) {
    let result = rt.run_litex_code(source).expect("public statement entry");
    assert!(
        result.session_error.is_none(),
        "{source}: {:?}",
        result.session_error
    );
    assert_eq!(
        result.success,
        wanted,
        "{source}\n{}",
        crate::json_output::project_run_detailed(&result, rt, "eval", None).stringify_pretty()
    );
}

#[test]
fn side_limits_proof_before_selection_and_recovery() {
    for (side, other) in [("left", "right"), ("right", "left")] {
        let mut rt = runtime();
        check(&mut rt, "have fn c(x R) R=3", true);
        for fact in [
            format!("lim_{side}(c,0)=3"),
            format!("lim_{side}(c,0) $in R"),
            format!("0*lim_{side}(c,0)=0"),
        ] {
            check(&mut rt, &fact, false);
        }
        check(
            &mut rt,
            &format!("release thm fn_limit_{other}_real_accumulation(0)"),
            true,
        );
        check(
            &mut rt,
            &format!("release thm fn_limit_{other}_constant(c,0,3)"),
            true,
        );
        check(&mut rt, &format!("lim_{side}(c,0)=3"), false);
        check(
            &mut rt,
            &format!("release thm fn_limit_{side}_real_accumulation(0)"),
            true,
        );
        check(
            &mut rt,
            &format!("release thm fn_limit_{side}_constant(c,0,3)"),
            true,
        );
        check(&mut rt, &format!("lim_{side}(c,0)=3"), true);
        check(&mut rt, &format!("lim_{side}(c,0)+2=5"), true);
        check(&mut rt, &format!("0*lim_{side}(c,0)=0"), true);
        check(&mut rt, &format!("lim_{side}(c,0)=4"), false);
        check(&mut rt, &format!("lim_{side}(c,1)=3"), false);
        check(&mut rt, "fn_lim(c,0)=3", false);
        check(&mut rt, "c(2)=3", true);
    }
}

#[test]
fn side_limits_direction_is_fact_and_object_identity() {
    for source in [
        "forall f fn(x R) R,p,L R:\n    $has_limit_left(f,p,L)\n    =>:\n        $has_limit_right(f,p,L)",
        "forall f fn(x R) R,p,L R:\n    not $has_limit_left(f,p,L)\n    =>:\n        not $has_limit_right(f,p,L)",
        "forall f fn(x R) R,p R:\n    exist L R st {$has_limit_left(f,p,L)}\n    =>:\n        exist L R st {$has_limit_right(f,p,L)}",
        "forall f fn(x R) R,p,A,B R:\n    $has_limit_left(f,p,A)\n    $has_limit_right(f,p,B)\n    =>:\n        A=B",
        "forall f fn(x R) R,p,A,B R:\n    $has_limit_left(f,p,A)\n    $has_limit_right(f,p,B)\n    =>:\n        lim_left(f,p)=lim_right(f,p)",
        "forall f,g fn(x R) R,p,q,L R:\n    f=g\n    p=q\n    $has_limit_left(f,p,L)\n    =>:\n        $has_limit_right(g,q,L)",
    ] { check(&mut runtime(),source,false); }
}

#[test]
fn side_limits_cannot_borrow_later_claim_or_failed_scope() {
    for side in ["left", "right"] {
        let mut rt = runtime();
        check(&mut rt, "have fn c(x R) R=3", true);
        check(&mut rt,&format!("claim:\n    ? lim_{side}(c,0)=3\n    release thm fn_limit_{side}_real_accumulation(0)\n    release thm fn_limit_{side}_constant(c,0,3)"),false);
        check(&mut rt, &format!("lim_{side}(c,0)=3"), false);
        check(&mut rt, "c(2)=3", true);
    }
}

#[test]
fn side_limits_directional_epsilon_and_eventual_conclusions() {
    check(&mut runtime(),"thm wrong_control:\n    ? forall f fn(x R) R,p,L R:\n        forall epsilon R+:\n            exist delta R+ st {{x R:0<p-x and p-x<delta} $subset preimage_set(f,{v R:abs(v-L)<epsilon})}\n        =>:\n            $has_limit_right(f,p,L)\n    release thm fn_limit_right_real_accumulation(p)\n    by thm fn_limit_right_from_epsilon(f,p,L) => $has_limit_right(f,p,L)",false);
    check(&mut runtime(),"forall f fn(x R) R,p R,L R+:\n    $has_limit_left(f,p,L)\n    =>:\n        exist delta R+ st {{x R:0<x-p and x-p<delta} $subset preimage_set(f,R+)}",false);
}

#[test]
fn side_limits_ordinary_bridge_requires_own_accumulation() {
    check(&mut runtime(),"thm without_side:\n    ? forall f fn(x R+) R,L R:\n        $has_limit_at(f,0,L)\n        =>:\n            $has_limit_left(f,0,L)\n    by thm fn_limit_at_to_left(f,0,L) => $has_limit_left(f,0,L)",false);
    check(&mut runtime(),"thm wrong_point:\n    ? forall f fn(x R) R,p,L R:\n        $has_limit_left(f,p,L)\n        $has_limit_right(f,p+1,L)\n        =>:\n            $has_limit_at(f,p,L)\n    by thm fn_limit_from_sides(f,p,L) => $has_limit_at(f,p,L)",false);
    check(&mut runtime(),"thm equal_sides:\n    ? forall f fn(x R) R,p,L R:\n        $has_limit_left(f,p,L)\n        $has_limit_right(f,p,L)\n        =>:\n            not $has_limit_at(f,p,L)\n    release thm fn_limit_sides_mismatch(f,p,L,L)",false);
}

#[test]
fn side_limits_parser_and_reserved_names() {
    for source in [
        "lim_left(1)=0",
        "lim_right(1,2,3)=0",
        "$has_limit_left(1,2)",
        "$has_limit_right(1,2,3,4)",
        "have lim_left R=1",
        "have lim_right R=1",
        "prop has_limit_left(f fn(x R) R,p,L R):\n    L=L",
        "have fn_limit_right_add R=1",
    ] {
        let mut rt = runtime();
        let tokens = crate::tokenize::Tokenizer::new()
            .tokenize(source, rt.current_file.clone())
            .unwrap();
        assert!(rt.parse(&tokens).is_err(), "{source}");
    }
}

#[test]
fn side_limits_provenance_ceilings_latex_and_lean_boundary() {
    for side in ["left", "right"] {
        let source=format!("forall f fn(x R) R,p,L R:\n    $has_limit_{side}(f,p,L)\n    =>:\n        lim_{side}(f,p)=L");
        let mut rt = runtime();
        let tokens = crate::tokenize::Tokenizer::new()
            .tokenize(&source, rt.current_file.clone())
            .unwrap();
        let Stmt::Fact(fact) = rt.parse(&tokens).unwrap().remove(0) else {
            panic!("fact")
        };
        assert!(rt
            .verify_fact(&fact, VerifyState::new(VerifyStateLevel::Direct))
            .unwrap()
            .is_failed());
        assert!(!rt
            .verify_fact(&fact, VerifyState::new(VerifyStateLevel::BuiltinRule))
            .unwrap()
            .is_failed());
        let result = rt.run_litex_code(&source).unwrap();
        assert!(result.success && result.session_error.is_none());
        let json =
            crate::json_output::project_run_detailed(&result, &rt, "eval", None).stringify_pretty();
        for required in [
            "FunctionLimitSelectedValue",
            "function_domain",
            "point_real",
            "convergence",
            &format!("\"approach\": \"lim_{side}\""),
        ] {
            assert!(json.contains(required), "{required}: {json}");
        }
        let error = crate::compile_to_lean::LitexToLeanCompiler::new(rt)
            .compile_run(&result, "side_limit_boundary")
            .unwrap_err();
        assert!(error.message.contains("not supported"), "{error}");
        let latex = crate::compile_to_latex::to_latex_from_source(&source, OutputLanguage::English)
            .unwrap();
        assert!(
            latex.contains("\\lim_") && latex.contains("\\operatorname{dom}"),
            "{latex}"
        );
        assert!(
            latex.contains(if side == "left" { "^{-}" } else { "^{+}" }),
            "{latex}"
        );
    }
}

#[test]
fn side_limits_native_only_lean_boundaries() {
    for source in ["forall f fn(x R) R,p,L R:\n    $has_limit_left(f,p,L)\n    =>:\n        $has_limit_left(f,p,L)","release thm fn_limit_left_real_accumulation(0)","release thm fn_limit_right_real_accumulation(0)"] {
        let mut rt=runtime();let result=rt.run_litex_code(source).unwrap();assert!(result.success && result.session_error.is_none());
        let error=crate::compile_to_lean::LitexToLeanCompiler::new(rt).compile_run(&result,"side_native_boundary").unwrap_err();assert!(error.message.contains("not supported"),"{error}");
    }
}

#[test]
fn side_limits_preserve_ast_directions_under_instantiation() {
    for side in ["left", "right"] {
        let mut rt = runtime();
        check(&mut rt,&format!("thm select_side:\n    ? forall f fn(x R) R,p,L R:\n        $has_limit_{side}(f,p,L)\n        =>:\n            lim_{side}(f,p)=L"),true);
        check(&mut rt, "have fn c(x R) R=2", true);
        check(
            &mut rt,
            &format!("release thm fn_limit_{side}_real_accumulation(0)"),
            true,
        );
        check(
            &mut rt,
            &format!("release thm fn_limit_{side}_constant(c,0,2)"),
            true,
        );
        check(
            &mut rt,
            &format!("by thm select_side(c,0,2) => lim_{side}(c,0)=2"),
            true,
        );
    }
}

#[test]
fn side_limits_reserved_theorem_catalog() {
    for (name, arity) in [
        ("fn_limit_left_real_accumulation", 1),
        ("fn_limit_left_from_epsilon", 3),
        ("fn_limit_left_control", 4),
        ("fn_limit_left_accumulation", 3),
        ("fn_limit_left_constant", 3),
        ("fn_limit_left_identity", 2),
        ("fn_limit_left_unique", 4),
        ("fn_limit_left_exists", 3),
        ("fn_limit_left_selected", 2),
        ("fn_limit_left_neg", 4),
        ("fn_limit_left_abs", 4),
        ("fn_limit_left_scale", 5),
        ("fn_limit_left_power", 5),
        ("fn_limit_left_add", 6),
        ("fn_limit_left_subtract", 6),
        ("fn_limit_left_multiply", 6),
        ("fn_limit_left_divide", 6),
        ("fn_limit_left_local_equal", 5),
        ("fn_limit_left_compare", 6),
        ("fn_limit_left_squeeze", 6),
        ("fn_limit_left_eventually_positive", 3),
        ("fn_limit_left_eventually_nonzero", 3),
        ("fn_limit_right_real_accumulation", 1),
        ("fn_limit_right_from_epsilon", 3),
        ("fn_limit_right_control", 4),
        ("fn_limit_right_accumulation", 3),
        ("fn_limit_right_constant", 3),
        ("fn_limit_right_identity", 2),
        ("fn_limit_right_unique", 4),
        ("fn_limit_right_exists", 3),
        ("fn_limit_right_selected", 2),
        ("fn_limit_right_neg", 4),
        ("fn_limit_right_abs", 4),
        ("fn_limit_right_scale", 5),
        ("fn_limit_right_power", 5),
        ("fn_limit_right_add", 6),
        ("fn_limit_right_subtract", 6),
        ("fn_limit_right_multiply", 6),
        ("fn_limit_right_divide", 6),
        ("fn_limit_right_local_equal", 5),
        ("fn_limit_right_compare", 6),
        ("fn_limit_right_squeeze", 6),
        ("fn_limit_right_eventually_positive", 3),
        ("fn_limit_right_eventually_nonzero", 3),
        ("fn_limit_at_to_left", 3),
        ("fn_limit_at_to_right", 3),
        ("fn_limit_from_sides", 3),
        ("fn_limit_sides_mismatch", 4),
    ] {
        let id =
            crate::builtin_theorem::BuiltinTheoremId::from_name(name).expect("registered theorem");
        assert_eq!(id.to_string(), name);
        assert_eq!(id.arity(), arity);
    }
}

#[test]
fn run_examples_side_limit_tracers() {
    for source in [
        include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/function_limit_left_selected.lit"),
        include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/function_limit_left_unique.lit"),
        include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/function_limit_right_selected.lit"),
        include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/function_limit_right_unique.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_at_to_left.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_at_to_right.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_from_sides.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_left_abs.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_left_accumulation.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_left_add.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_left_compare.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_left_constant.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_left_control.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_left_divide.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_left_eventually_nonzero.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_left_eventually_positive.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_left_exists.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_left_from_epsilon.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_left_identity.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_left_local_equal.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_left_multiply.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_left_neg.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_left_power.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_left_real_accumulation.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_left_scale.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_left_selected.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_left_squeeze.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_left_subtract.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_left_unique.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_right_abs.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_right_accumulation.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_right_add.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_right_compare.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_right_constant.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_right_control.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_right_divide.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_right_eventually_nonzero.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_right_eventually_positive.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_right_exists.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_right_from_epsilon.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_right_identity.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_right_local_equal.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_right_multiply.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_right_neg.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_right_power.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_right_real_accumulation.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_right_scale.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_right_selected.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_right_squeeze.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_right_subtract.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_right_unique.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_sides_mismatch.lit"),
        include_str!("../../../../examples/wd/real_function_limit_sides.lit"),
        include_str!("../../../../examples/wd/real_function_limit_sides_agree.lit"),
        include_str!("../../../../examples/wd/real_function_limit_sides_endpoint.lit"),
        include_str!("../../../../examples/wd/real_function_limit_sides_interfaces.lit"),
    ] { check(&mut runtime(),source,true); }
    for source in [
        include_str!("../../../../examples/wd_negative/real_function_limit_sides_left_without_proof.lit"),
        include_str!("../../../../examples/wd_negative/real_function_limit_sides_right_cancel_without_proof.lit"),
        include_str!("../../../../examples/wd_negative/real_function_limit_sides_opposite_side.lit"),
        include_str!("../../../../examples/wd_negative/real_function_limit_sides_one_side_to_at.lit"),
        include_str!("../../../../examples/wd_negative/real_function_limit_sides_absent_side_bridge.lit"),
        include_str!("../../../../examples/wd_negative/real_function_limit_sides_cross_side_unique.lit"),
        include_str!("../../../../examples/wd_negative/real_function_limit_sides_mismatching_from_sides.lit"),
        include_str!("../../../../examples/wd_negative/real_function_limit_sides_wrong_point.lit"),
        include_str!("../../../../examples/wd_negative/real_function_limit_sides_empty_domain.lit"),
        include_str!("../../../../examples/wd_negative/real_function_limit_sides_isolated_domain.lit"),
        include_str!("../../../../examples/wd_negative/real_function_limit_sides_nonreal_domain.lit"),
        include_str!("../../../../examples/wd_negative/real_function_limit_sides_nonreal_point.lit"),
        include_str!("../../../../examples/wd_negative/real_function_limit_sides_wrong_constant.lit"),
        include_str!("../../../../examples/wd_negative/real_function_limit_sides_zero_denominator.lit"),
        include_str!("../../../../examples/wd_negative/real_function_limit_sides_local_sparse.lit"),
        include_str!("../../../../examples/wd_negative/real_function_limit_sides_punctured_without_proof.lit"),
    ] { check(&mut runtime(),source,false); }
}
