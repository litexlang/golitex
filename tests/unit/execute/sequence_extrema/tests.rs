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
fn check(rt: &mut Runtime, code: &str, wanted: bool) {
    let r = rt.run_litex_code(code).unwrap();
    assert!(r.session_error.is_none(), "{code}: {:?}", r.session_error);
    assert_eq!(
        r.success,
        wanted,
        "{code}\n{}",
        crate::json_output::project_run_detailed(&r, rt, "eval", None).stringify_pretty()
    );
}
#[test]
fn extrema_wd_is_proof_consuming_and_upper_lower_are_distinct() {
    for (side, other) in [("limsup", "liminf"), ("liminf", "limsup")] {
        let mut rt = runtime();
        check(&mut rt, "have fn c(k N+) R=3", true);
        check(&mut rt, &format!("{side}(c)=3"), false);
        check(&mut rt, &format!("0*{side}(c)=0"), false);
        check(
            &mut rt,
            &format!("release thm seq_{other}_constant(c,3)"),
            true,
        );
        check(&mut rt, &format!("{side}(c)=3"), false);
        check(
            &mut rt,
            &format!("release thm seq_{side}_constant(c,3)"),
            true,
        );
        check(&mut rt, &format!("{side}(c)=3"), true);
        check(&mut rt, &format!("{side}(c)+2=5"), true);
        check(&mut rt, &format!("{side}(c)=4"), false);
    }
}
#[test]
fn extrema_both_sequence_interfaces_without_global_boundedness() {
    for ty in ["seq(R)", "fn(k N+) R"] {
        for side in ["limsup", "liminf"] {
            check(&mut runtime(),&format!("forall a {ty},L R:\n    $has_seq_{side}(a,L)\n    =>:\n        {side}(a)=L\n        {side}(a) $in R"),true);
        }
    }
}
#[test]
fn extrema_convergence_bridges_and_order() {
    check(&mut runtime(),"thm converges:\n    ? forall a seq(R),L R:\n        $has_seq_limit(a,L)\n        =>:\n            $has_seq_limsup(a,L)\n            $has_seq_liminf(a,L)\n    release thm seq_limsup_from_limit(a,L)\n    release thm seq_liminf_from_limit(a,L)",true);
    check(&mut runtime(),"thm converse:\n    ? forall a seq(R),L R:\n        $has_seq_limsup(a,L)\n        $has_seq_liminf(a,L)\n        =>:\n            $has_seq_limit(a,L)\n    release thm seq_limit_from_extrema(a,L)",true);
    check(&mut runtime(),"thm ordered:\n    ? forall a seq(R),L,U R:\n        $has_seq_liminf(a,L)\n        $has_seq_limsup(a,U)\n        =>:\n            L<=U\n    release thm seq_extrema_order(a,L,U)",true);
}
#[test]
fn extrema_eventual_bound_alone_never_defines_candidate() {
    for side in ["limsup", "liminf"] {
        let relation = if side == "limsup" {
            "v<L+epsilon"
        } else {
            "L-epsilon<v"
        };
        check(&mut runtime(),&format!("thm bound_only:\n    ? forall a seq(R),L R:\n        forall epsilon R+:\n            exist n0 N+ st {{{{n N+:n>=n0}} $subset preimage_set(a,{{v R:{relation}}})}}\n        =>:\n            $has_seq_{side}(a,L)\n    by def $has_seq_{side}(a,L)"),false);
    }
}
#[test]
fn extrema_negation_swaps_and_negative_scaling_requires_sign() {
    for (side, other) in [("limsup", "liminf"), ("liminf", "limsup")] {
        check(&mut runtime(),&format!("thm negate:\n    ? forall a,b seq(R),L R:\n        $has_seq_{side}(a,L)\n        forall n N+:\n            b(n)=-a(n)\n        =>:\n            $has_seq_{other}(b,-L)\n    release thm seq_{side}_neg(a,b,L)"),true);
        check(&mut runtime(),&format!("thm bad_sign:\n    ? forall a,b seq(R),L R:\n        $has_seq_{side}(a,L)\n        forall n N+:\n            b(n)=-a(n)\n        =>:\n            $has_seq_{side}(b,-L)\n    release thm seq_{side}_scale_nonnegative(a,b,L,-1)"),false);
    }
}
#[test]
fn extrema_scope_does_not_leak_after_failed_claim() {
    let mut rt = runtime();
    check(&mut rt, "have fn c(k N+) R=3", true);
    check(
        &mut rt,
        "claim:\n    ? limsup(c)=3\n    release thm seq_limsup_constant(c,3)",
        false,
    );
    check(&mut rt, "limsup(c)=3", false);
    check(&mut rt, "c(1)=3", true);
}
#[test]
fn extrema_output_provenance_and_explicit_lean_boundary() {
    for side in ["limsup", "liminf"] {
        let source =
            format!("forall a seq(R),L R:\n    $has_seq_{side}(a,L)\n    =>:\n        {side}(a)=L");
        let mut rt = runtime();
        let r = rt.run_litex_code(&source).unwrap();
        assert!(r.success);
        let json =
            crate::json_output::project_run_detailed(&r, &rt, "eval", None).stringify_pretty();
        assert!(
            json.contains("sequence_domain") && json.contains("convergence") && json.contains(side)
        );
        let latex = crate::compile_to_latex::to_latex_from_source(&source, OutputLanguage::English)
            .unwrap();
        assert!(latex.contains(&format!("\\{side}")));
        let e = crate::compile_to_lean::LitexToLeanCompiler::new(rt)
            .compile_run(&r, "extrema")
            .unwrap_err();
        assert!(e.message.contains("not supported"));
    }
}

#[test]
fn extrema_bounded_existence_checks_completeness_derivation() {
    for ty in ["seq(R)", "fn(k N+) R"] {
        for side in ["limsup", "liminf"] {
            let code=format!("thm bounded_exists:\n    ? forall a {ty},M R+:\n        forall n N+:\n            abs(a(n))<=M\n        =>:\n            exist L R st {{$has_seq_{side}(a,L)}}\n    release thm seq_{side}_bounded_exists(a,M)");
            check(&mut runtime(), &code, true);
        }
    }
}
#[test]
fn extrema_bounded_existence_has_no_name_magic_or_helper_leak() {
    let mut rt = runtime();
    check(
        &mut rt,
        "prop extrema_bounded(a seq(R),M R+):\n    0=1",
        true,
    );
    check(&mut rt, "have fn a(k N+) R=3", true);
    check(
        &mut rt,
        "claim:\n    ? forall n N+:\n        abs(a(n))<=3\n    a(n)=3\n    abs(a(n))=abs(3)=3",
        true,
    );
    check(&mut rt, "limsup(a) $in R", false);
    check(&mut rt, "release thm seq_limsup_bounded_exists(a,2)", false);
    let derived = rt
        .run_litex_code("release thm seq_limsup_bounded_exists(a,3)")
        .unwrap();
    assert!(derived.success && derived.session_error.is_none());
    let json =
        crate::json_output::project_run_detailed(&derived, &rt, "eval", None).stringify_pretty();
    for required in [
        "theorem_derivation",
        "derivation_steps",
        "real_least_upper_bound_exists",
        "real_greatest_lower_bound_exists",
        "has_seq_limit",
        "application",
        "conclusion",
    ] {
        assert!(json.contains(required), "missing {required}");
    }
    check(&mut rt, "release thm seq_liminf_bounded_exists(a,3)", true);
    check(&mut rt, "limsup(a) $in R", true);
    check(&mut rt, "liminf(a) $in R", true);
    check(&mut rt, "$extrema_bounded(a,3)", false);
    check(&mut rt, "release thm seq_limsup_bounded_exists(a,0)", false);
}

#[test]
fn extrema_selection_retains_exact_value_equality_after_algebra() {
    let mut rt = runtime();
    for source in [
        "have fn a(k N+) R=3",
        "have fn b(k N+) R=-a(k)",
        "have fn c(k N+) R=-b(k)",
        "release thm seq_limsup_constant(a,3)",
        "forall n N+:\n    b(n)=-a(n)",
        "release thm seq_limsup_neg(a,b,3)",
        "forall n N+:\n    c(n)=-b(n)",
        "release thm seq_liminf_neg(b,c,-3)",
        "limsup(c)=3",
    ] {
        check(&mut rt, source, true);
    }
    check(&mut rt, "limsup(c)=4", false);
}

#[test]
fn extrema_completeness_source_matches_the_maintained_example() {
    assert_eq!(include_str!("../../../../src/execute/execute_by_stmt/builtin_thm/sequence_extrema_completeness.lit"),include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/sequence_extrema_completeness.lit"));
}

#[test]
fn extrema_rejects_incomplete_and_finite_sequence_interfaces() {
    for ty in [
        "fn(k N+:k>2) R",
        "finite_seq(R,3)",
        "fn(k Z) R",
        "fn(k N+) C",
    ] {
        for side in ["limsup", "liminf"] {
            check(
                &mut runtime(),
                &format!(
                    "forall a {ty},L R:\n    $has_seq_{side}(a,L)\n    =>:\n        {side}(a)=L"
                ),
                false,
            );
        }
    }
}

#[test]
fn extrema_bounded_derivation_preserves_export_origin_and_parse_bindings() {
    let mut rt = runtime();
    rt.abort_source();
    let origin = CodeSource::RootExport {
        path: "extremal_contract.lit".into(),
        export_file_id: 0,
    };
    rt.begin_source(origin.clone());
    check(&mut rt,"thm bounded_export:\n    ? forall a seq(R),M R+:\n        forall n N+:\n            abs(a(n))<=M\n        =>:\n            exist L R st {$has_seq_limsup(a,L)}\n    release thm seq_limsup_bounded_exists(a,M)",true);
    assert_eq!(rt.current_file, origin);
    assert!(rt.resolve_plain_atom("extrema_tail_sup").is_err());
    check(&mut rt, "have later R=2", true);
    check(&mut rt, "later+1=3", true);
}
