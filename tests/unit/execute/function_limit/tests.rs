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
    let run = rt
        .run_litex_code(source)
        .expect("public statement pipeline");
    assert!(
        run.session_error.is_none(),
        "{source}: {:?}",
        run.session_error
    );
    assert_eq!(
        run.success,
        wanted,
        "{source}\n{}",
        crate::json_output::project_run_detailed(&run, rt, "eval", None).stringify_pretty()
    );
}

#[test]
fn function_limit_tests_distinct_names_and_rendering() {
    let mut rt = runtime();
    check(&mut rt, "have fn c(x R) R=3", true);
    check(
        &mut rt,
        "release thm fn_limit_at_real_accumulation(0)",
        true,
    );
    check(&mut rt, "release thm fn_limit_at_constant(c,0,3)", true);
    for source in ["lim(c,0)=3", "lim(1,2)=0"] {
        let tokens = crate::tokenize::Tokenizer::new()
            .tokenize(source, rt.current_file.clone())
            .unwrap();
        let error = rt.parse(&tokens).unwrap_err();
        assert!(error.to_string().contains("fn_lim(f, x0)"), "{error}");
        check(&mut rt, source, false);
    }
    let run = rt.run_litex_code("fn_lim(c,0)=3").unwrap();
    assert!(run.success && run.session_error.is_none());
    let normal = crate::json_output::project_run_normal(&run, &rt, "eval", None).stringify_pretty();
    assert!(normal.contains("fn_lim(c, 0) = 3"), "{normal}");
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize("fn_lim(c,0)=3", rt.current_file.clone())
        .unwrap();
    let parsed = rt.parse(&tokens).unwrap().remove(0);
    let rendered = parsed.readable_string();
    assert_eq!(rendered, "fn_lim(c, 0) = 3");
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize(&rendered, rt.current_file.clone())
        .unwrap();
    assert_eq!(
        rt.parse(&tokens).unwrap().remove(0).readable_string(),
        rendered
    );
    check(&mut rt, "have fn a(k N+) R=3", true);
    check(&mut rt, "release thm seq_limit_constant(a,3)", true);
    check(&mut rt, "lim(a)=3", true);
    check(&mut rt, "fn_lim(a,0)=3", false);
    check(&mut rt, "fn_lim(c,0)=3", true);
}

#[test]
fn function_limit_tests_proof_before_selection_and_failure_recovery() {
    let mut rt = runtime();
    check(&mut rt, "have fn c(x R) R=3", true);
    for source in [
        "fn_lim(c,0)=3",
        "fn_lim(c,0) $in R",
        "0*fn_lim(c,0)=0",
        "release thm fn_limit_at_exists(c,0,3)",
    ] {
        check(&mut rt, source, false);
    }
    check(&mut rt, "c(2)=3", true);
    check(
        &mut rt,
        "release thm fn_limit_at_real_accumulation(0)",
        true,
    );
    check(&mut rt, "release thm fn_limit_at_constant(c,0,3)", true);
    for source in [
        "fn_lim(c,0)=3",
        "3=fn_lim(c,0)",
        "fn_lim(c,0)+2=5",
        "fn_lim(c,0) $in R",
        "0*fn_lim(c,0)=0",
    ] {
        check(&mut rt, source, true);
    }
    for source in [
        "fn_lim(c,0)=4",
        "fn_lim(c,1)=3",
        "release thm fn_limit_at_constant(c,0,4)",
    ] {
        check(&mut rt, source, false);
    }
    check(&mut rt, "fn_lim(c,0)=3", true);
}

#[test]
fn function_limit_tests_candidate_existence_uniqueness_and_generic_domains() {
    for signature in ["fn(x R) R", "fn(y R: y != 0) R", "fn(z R+) R"] {
        check(&mut runtime(),&format!("forall f {signature},x0,L R:\n    $has_limit_at(f,x0,L)\n    =>:\n        fn_lim(f,x0)=L\n        fn_lim(f,x0) $in R"),true);
        check(&mut runtime(),&format!("forall f {signature},x0 R:\n    exist L R st {{$has_limit_at(f,x0,L)}}\n    =>:\n        fn_lim(f,x0) $in R"),true);
    }
    check(&mut runtime(),"forall f fn(x R) R,x0,A,B R:\n    $has_limit_at(f,x0,A)\n    $has_limit_at(f,x0,B)\n    =>:\n        A=B",true);
    check(&mut runtime(),"forall f fn(x R) R,A,B R:\n    $has_limit_at(f,0,A)\n    $has_limit_at(f,1,B)\n    =>:\n        A=B",false);
    check(&mut runtime(),"thm selected:\n    ? forall f fn(x R) R,x0,L R:\n        $has_limit_at(f,x0,L)\n        =>:\n            $has_limit_at(f,x0,fn_lim(f,x0))\n    release thm fn_limit_at_exists(f,x0,L)\n    release thm fn_limit_at_selected(f,x0)",true);
}

#[test]
fn function_limit_tests_invalid_domains_and_no_vacuous_anchor() {
    for source in [
        "fn_lim(3,0)=0",
        "$has_limit_at(3,0,0)",
        "$has_limit_at(fn(x R) C {i},0,0)",
        "$has_limit_at(fn(x C) R {0},0,0)",
        "$has_limit_at(fn(x,y R) R {x+y},0,0)",
        "$has_limit_at(fn(x R) R {0},i,0)",
        "$has_limit_at(fn(x R) R {0},0,i)",
        "have fn f(x {}) R=7\nrelease thm fn_limit_at_constant(f,0,7)",
        "have fn f(x {0}) R=7\nrelease thm fn_limit_at_constant(f,0,7)",
        "have fn f(x R:x!=0) R=x^2/x\nf(0)=0",
        "have fn f(x R) R=0\nrelease thm fn_limit_at_add(f,f,f,0,0,0)",
    ] {
        check(&mut runtime(), source, false);
    }
    for carrier in ["{}", "{0}"] {
        check(
            &mut runtime(),
            &format!(
                "forall f fn(x {carrier}) R:\n    not $has_limit_at(f,0,0)\n    =>:\n        0=0"
            ),
            true,
        );
    }
}

#[test]
fn function_limit_tests_named_output_algebra_rules() {
    for (name, operation, value) in [
        ("add", "f(x)+g(x)", "A+B"),
        ("subtract", "f(x)-g(x)", "A-B"),
        ("multiply", "f(x)*g(x)", "A*B"),
    ] {
        let source=format!("thm algebra:\n    ? forall f,g,h fn(x R) R,x0,A,B R:\n        $has_limit_at(f,x0,A)\n        $has_limit_at(g,x0,B)\n        forall x R:\n            h(x)={operation}\n        =>:\n            $has_limit_at(h,x0,{value})\n    by thm fn_limit_at_{name}(f,g,h,x0,A,B) => $has_limit_at(h,x0,{value})");
        check(&mut runtime(), &source, true);
    }
    for (name, operation, value, args) in [
        ("neg", "-f(x)", "-A", "f,h,x0,A"),
        ("abs", "abs(f(x))", "abs(A)", "f,h,x0,A"),
        ("scale", "2*f(x)", "2*A", "f,h,x0,A,2"),
        ("power", "f(x)^2", "A^2", "f,h,x0,A,2"),
    ] {
        let source=format!("thm algebra:\n    ? forall f,h fn(x R) R,x0,A R:\n        $has_limit_at(f,x0,A)\n        forall x R:\n            h(x)={operation}\n        =>:\n            $has_limit_at(h,x0,{value})\n    by thm fn_limit_at_{name}({args}) => $has_limit_at(h,x0,{value})");
        check(&mut runtime(), &source, true);
    }
}

#[test]
fn function_limit_tests_negation_payload_substitution_and_parser_controls() {
    let mut rt = runtime();
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize("$has_limit_at(fn(x R) R {x},0,0)", rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(Fact::AtomicFact(positive)) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("candidate")
    };
    let id = rt.global_ids.allocate_fact_id();
    let negative = crate::ast::fact::negate_atomic_fact(&positive, id).unwrap();
    assert!(matches!(negative, AtomicFact::NotHasFunctionLimitFact(_)));
    assert_eq!(negative.fact_id(), id);
    let next = rt.global_ids.allocate_fact_id();
    let positive_again = crate::ast::fact::negate_atomic_fact(&negative, next).unwrap();
    assert_eq!(positive_again.readable_string(), positive.readable_string());
    check(&mut rt,"forall f,g fn(x R) R,a,b,L R:\n    f=g\n    a=b\n    $has_limit_at(f,a,L)\n    =>:\n        fn_lim(f,a)=fn_lim(g,b)",true);
    for source in [
        "have has_limit_at R=1",
        "prop has_limit_at(f fn(x R) R,a,L R):\n    L=L",
        "have fn_lim R=1",
        "prop fn_lim(f fn(x R) R,a,L R):\n    L=L",
        "$has_limit_at(1,2)",
        "fn_lim()=0",
        "fn_lim(1)=0",
        "fn_lim(1,2,3)=0",
    ] {
        let mut rt = runtime();
        let tokens = crate::tokenize::Tokenizer::new()
            .tokenize(source, rt.current_file.clone())
            .unwrap();
        assert!(rt.parse(&tokens).is_err(), "{source}");
    }
}

#[test]
fn function_limit_tests_provenance_ceiling_latex_and_lean_boundary() {
    let source =
        "forall f fn(x R) R,x0,L R:\n    $has_limit_at(f,x0,L)\n    =>:\n        fn_lim(f,x0)=L";
    let mut rt = runtime();
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize(source, rt.current_file.clone())
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
    let run = rt.run_litex_code(source).unwrap();
    assert!(run.success && run.session_error.is_none());
    let detailed =
        crate::json_output::project_run_detailed(&run, &rt, "eval", None).stringify_pretty();
    for fragment in [
        "FunctionLimitSelectedValue",
        "function_domain",
        "point_real",
        "convergence",
    ] {
        assert!(
            detailed.contains(fragment),
            "missing {fragment}: {detailed}"
        );
    }
    let error = crate::compile_to_lean::LitexToLeanCompiler::new(rt)
        .compile_run(&run, "function_limit_boundary")
        .unwrap_err();
    assert!(error.message.contains("not supported"), "{error}");
    let latex =
        crate::compile_to_latex::to_latex_from_source(source, OutputLanguage::English).unwrap();
    assert!(
        latex.contains("\\lim_") && latex.contains("\\operatorname{dom}"),
        "{latex}"
    );
}

#[test]
fn function_limit_tests_quotient_premises_and_local_laws() {
    check(&mut runtime(),"thm quotient:\n    ? forall f,g,h fn(x R) R,x0,A,B R:\n        $has_limit_at(f,x0,A)\n        $has_limit_at(g,x0,B)\n        B!=0\n        forall x R:\n            g(x)!=0\n        forall x R:\n            h(x)=f(x)/g(x)\n        =>:\n            $has_limit_at(h,x0,A/B)\n    release thm fn_limit_at_divide(f,g,h,x0,A,B)",true);
    check(&mut runtime(),"thm local:\n    ? forall f,g fn(x R) R,x0,L R,r R+:\n        $has_limit_at(f,x0,L)\n        forall x {t R:0<abs(t-x0) and abs(t-x0)<r}:\n            f(x)=g(x)\n        =>:\n            $has_limit_at(g,x0,L)\n    release thm fn_limit_at_real_accumulation(x0)\n    release thm fn_limit_at_local_equal(f,g,x0,L,r)",true);
    check(&mut runtime(),"thm compare:\n    ? forall f,g fn(x R) R,x0,A,B R,r R+:\n        $has_limit_at(f,x0,A)\n        $has_limit_at(g,x0,B)\n        forall x {t R:0<abs(t-x0) and abs(t-x0)<r}:\n            f(x)<=g(x)\n        =>:\n            A<=B\n    release thm fn_limit_at_compare(f,g,x0,A,B,r)",true);
    check(&mut runtime(),"thm squeeze:\n    ? forall f,g,h fn(x R) R,x0,L R,r R+:\n        $has_limit_at(f,x0,L)\n        $has_limit_at(h,x0,L)\n        forall x {t R:0<abs(t-x0) and abs(t-x0)<r}:\n            f(x)<=g(x)<=h(x)\n        =>:\n            $has_limit_at(g,x0,L)\n    release thm fn_limit_at_squeeze(f,g,h,x0,L,r)",true);
}

#[test]
fn function_limit_tests_eventual_signs() {
    for (name, carrier) in [("positive", "R+"), ("nonzero", "R*")] {
        let source=format!("thm eventual:\n    ? forall f fn(x R) R,x0 R,L {carrier}:\n        $has_limit_at(f,x0,L)\n        =>:\n            exist delta R+ st {{{{x R:0<abs(x-x0) and abs(x-x0)<delta}} $subset preimage_set(f,{carrier})}}\n    release thm fn_limit_at_eventually_{name}(f,x0,L)");
        check(&mut runtime(), &source, true);
    }
}

#[test]
fn function_limit_tests_selected_candidate_exact_calculation() {
    let mut rt = runtime();
    check(&mut rt, "have fn id(x R) R=x", true);
    check(&mut rt, "have fn sq(x R) R=x^2", true);
    check(
        &mut rt,
        "release thm fn_limit_at_real_accumulation(3)",
        true,
    );
    check(&mut rt, "release thm fn_limit_at_identity(id,3)", true);
    check(
        &mut rt,
        "claim:\n    ? forall x R:\n        sq(x)=id(x)^2\n    id(x)=x\n    sq(x)=x^2=id(x)^2",
        true,
    );
    check(&mut rt, "release thm fn_limit_at_power(id,sq,3,3,2)", true);
    check(&mut rt, "fn_lim(sq,3)=9", true);
    check(&mut rt, "fn_lim(sq,3)=10", false);
    check(&mut rt, "fn_lim(sq,3)+1=10", true);
}

#[test]
fn run_examples_function_limit_tracers() {
    for source in [
        include_str!("../../../../examples/wd/function_limit_distinct_name.lit"),
        include_str!("../../../../examples/wd/real_function_limit_at.lit"),
        include_str!("../../../../examples/wd/real_function_limit_common_proofs.lit"),
        include_str!("../../../../examples/wd/real_function_limit_endpoints.lit"),
        include_str!("../../../../examples/wd/real_function_limit_interfaces.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_at_abs.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_at_accumulation.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_at_add.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_at_compare.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_at_constant.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_at_control.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_at_divide.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_at_eventually_nonzero.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_at_eventually_positive.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_at_exists.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_at_from_epsilon.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_at_identity.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_at_local_equal.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_at_multiply.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_at_neg.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_at_power.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_at_real_accumulation.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_at_scale.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_at_selected.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_at_squeeze.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_at_subtract.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_at_unique.lit"),
        include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/function_limit_selected.lit"),
        include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/function_limit_unique.lit"),
] { check(&mut runtime(),source,true); }
    for source in [
        include_str!(
            "../../../../examples/wd_negative/real_function_limit_cancellation_without_proof.lit"
        ),
        include_str!("../../../../examples/wd_negative/real_function_limit_empty_domain.lit"),
        include_str!("../../../../examples/wd_negative/real_function_limit_illegal_base_call.lit"),
        include_str!("../../../../examples/wd_negative/real_function_limit_isolated_domain.lit"),
        include_str!("../../../../examples/wd_negative/real_function_limit_nonreal_domain.lit"),
        include_str!(
            "../../../../examples/wd_negative/real_function_limit_punctured_without_proof.lit"
        ),
        include_str!("../../../../examples/wd_negative/real_function_limit_without_proof.lit"),
        include_str!("../../../../examples/wd_negative/real_function_limit_wrong_output.lit"),
        include_str!("../../../../examples/wd_negative/real_function_limit_wrong_point.lit"),
        include_str!("../../../../examples/wd_negative/real_function_limit_zero_denominator.lit"),
    ] {
        check(&mut runtime(), source, false);
    }
}

#[test]
fn function_limit_tests_native_candidate_and_bt_lean_boundaries() {
    for source in [
        "forall af fn(x R) R,p,L R:\n    $has_limit_at(af,p,L)\n    =>:\n        $has_limit_at(af,p,L)",
        "release thm fn_limit_at_real_accumulation(0)",
    ] {
        let mut rt=runtime();
        let run=rt.run_litex_code(source).unwrap();
        assert!(run.success && run.session_error.is_none());
        let error=crate::compile_to_lean::LitexToLeanCompiler::new(rt).compile_run(&run,"function_limit_native_boundary").unwrap_err();
        assert!(error.message.contains("not supported"),"{error}");
    }
}

#[test]
fn function_limit_tests_cannot_use_later_claim_proof_for_value_wd() {
    let mut rt = runtime();
    check(&mut rt, "have fn c(x R) R=3", true);
    check(&mut rt,"claim:\n    ? fn_lim(c,0)=3\n    release thm fn_limit_at_real_accumulation(0)\n    release thm fn_limit_at_constant(c,0,3)",false);
    check(&mut rt, "fn_lim(c,0)=3", false);
    check(&mut rt, "c(0)=3", true);
}

#[test]
fn function_limit_tests_invalid_point_reports_carrier_not_convergence() {
    let mut rt = runtime();
    check(&mut rt, "have fn c(x R) R=3", true);
    let run = rt.run_litex_code("fn_lim(c,i)=3").unwrap();
    assert!(!run.success && run.session_error.is_none());
    let detailed =
        crate::json_output::project_run_detailed(&run, &rt, "eval", None).stringify_pretty();
    assert!(detailed.contains("point_real"), "{detailed}");
    assert!(detailed.contains("i $in R"), "{detailed}");
    assert!(
        !detailed.contains("requires proved finite convergence"),
        "{detailed}"
    );
    check(&mut rt, "c(2)=3", true);
}
