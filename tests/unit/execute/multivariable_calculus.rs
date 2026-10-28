use crate::prelude::*;

#[test]
fn directional_derivative_explicit_bridges_and_provenance() {
    let mut rt = runtime();
    check(&mut rt, "have fn bowl(x cart_n(R,2)) R=x(1)^2+x(2)^2", true);
    check(&mut rt, "$is_multi_differentiable_at(bowl,(1,2),2)", true);
    check(&mut rt, "$has_gradient_at(bowl,(1,2),2,(2,4))", true);
    let run = check(
        &mut rt,
        "by thm differentiable_gradient_along_line(bowl,(1,2),(3,-1),2,(2,4))",
        true,
    );
    let json = crate::json_output::project_run_detailed(&run, &rt, "directional", None).stringify();
    assert!(
        json.contains("differentiable_gradient_along_line"),
        "{json}"
    );
    assert!(json.contains("inner_product"), "{json}");
    check(&mut rt, "$has_derivative_at(fn(t R) R {bowl(fn(k closed_range(1,2)) R {(1,2)(k)+t*(3,-1)(k)})},0,inner_product((2,4),(3,-1),2))", true);
    check(&mut rt, "inner_product((2,4),(3,-1),2)=2", true);
    let run = check(&mut rt, "by thm scalar_differential_along_line(bowl,(1,2),(3,-1),2,fn(row closed_range(1,1),col closed_range(1,2)) R {(2,4)(col)})", true);
    let json = crate::json_output::project_run_detailed(&run, &rt, "directional", None).stringify();
    assert!(json.contains("scalar_differential_along_line"), "{json}");
    assert!(json.contains("matrix_apply"), "{json}");
}

#[test]
fn directional_derivative_opaque_premises_and_missing_differentiability() {
    let mut rt = runtime();
    check(&mut rt, "thm gradient_direction:\n    ? forall n N+,f fn(x cart_n(R,n)) R,p,v,g cart_n(R,n),L R:\n        $is_multi_differentiable_at(f,p,n)\n        $has_gradient_at(f,p,n,g)\n        inner_product(g,v,n)=L\n        =>:\n            $has_derivative_at(fn(t R) R {f(fn(k closed_range(1,n)) R {p(k)+t*v(k)})},0,L)\n    inner_product(g,v,n) $in R\n    by thm differentiable_gradient_along_line(f,p,v,n,g)", true);
    check(&mut rt, "thm unsupported_gradient_only_direction:\n    ? forall n N+,f fn(x cart_n(R,n)) R,p,v,g cart_n(R,n),L R:\n        $has_gradient_at(f,p,n,g)\n        inner_product(g,v,n)=L\n        =>:\n            $has_derivative_at(fn(t R) R {f(fn(k closed_range(1,n)) R {p(k)+t*v(k)})},0,L)\n    inner_product(g,v,n) $in R\n    by thm differentiable_gradient_along_line(f,p,v,n,g)", false);
    check(&mut rt, "0=0", true);
}

#[test]
fn directional_derivative_full_domain_and_dimension_boundaries() {
    let mut rt = runtime();
    check(
        &mut rt,
        "have fn guarded(x cart_n(R,2): x(1)>=0) R=x(1)^2+x(2)^2",
        true,
    );
    check(
        &mut rt,
        "by thm differentiable_gradient_along_line(guarded,(1,2),(3,-1),2,(2,4))",
        false,
    );
    check(
        &mut rt,
        "have fn exact(x fn(k closed_range(1,2)) R) R=x(1)^2+x(2)^2",
        true,
    );
    check(
        &mut rt,
        "by thm differentiable_gradient_along_line(exact,(1,2),(3,-1),2,(2,4))",
        true,
    );
    check(
        &mut rt,
        "by thm differentiable_gradient_along_line(exact,(1,2),(3,-1,0),2,(2,4))",
        false,
    );
    check(
        &mut rt,
        "by thm differentiable_gradient_along_line(exact,(1,2),(3,-1),3,(2,4))",
        false,
    );
    check(
        &mut rt,
        "by thm scalar_differential_along_line(exact,(1,2),(3,-1),2,identity_matrix(2))",
        false,
    );
    check(&mut rt, "0=0", true);
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
fn check(rt: &mut Runtime, source: &str, expected: bool) -> crate::run::RunLitexCodeResult {
    let run = rt.run_litex_code(source).unwrap();
    assert!(run.session_error.is_none(), "{source}");
    assert_eq!(run.success, expected, "{source}");
    run
}
fn parse_object(rt: &mut Runtime, source: &str) -> Obj {
    let code = format!("{source}={source}");
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize(&code, rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(f))) =
        rt.parse(&tokens).unwrap().remove(0)
    else {
        panic!("equality")
    };
    f.left
}
#[test]
fn multivariable_calculus_bounded_reduction_reuses_exact_matrix_and_trig_evidence() {
    let mut rt = runtime();
    for (source, expected) in [
        ("2*identity_matrix(2)(1,1)", "2"),
        ("2*identity_matrix(2)(1,2)", "0"),
        ("cos(0*2)*2", "2"),
    ] {
        let object = parse_object(&mut rt, source);
        let result = rt
            .reduce_multivariable_expression(
                &object,
                VerifyState::new(VerifyStateLevel::BuiltinRule),
            )
            .unwrap()
            .unwrap();
        assert_eq!(
            result.result.readable_string(),
            expected,
            "{source}: {}",
            result.result.readable_string()
        );
        assert!(!result.steps.is_empty());
    }
}
#[test]
fn multivariable_calculus_wd_never_discovers_candidates_and_failed_statements_do_not_publish() {
    let mut rt = runtime();
    check(&mut rt, "have fn f(x cart_n(R,2)) R=x(1)^2+x(2)^2", true);
    check(
        &mut rt,
        "have fn F(x cart_n(R,3)) cart_n(R,3)=(x(1),x(2),x(3))",
        true,
    );
    for goal in [
        "lim_multi_at(f,(1,2),2) $in R",
        "lim_vector_at(F,(1,2,3),3,3) $in cart_n(R,3)",
        "partial_derivative(f,(1,2),2,1) $in R",
        "scalar_differential(f,(1,2),2) $in matrix(R,1,2)",
        "differential(F,(1,2,3),3,3) $in matrix(R,3,3)",
        "gradient_at(f,(1,2),2) $in cart_n(R,2)",
        "jacobian(F,(1,2,3),3,3) $in matrix(R,3,3)",
        "hessian(f,(1,2),2) $in matrix(R,2,2)",
        "divergence(F,(1,2,3),3) $in R",
        "curl(F,(1,2,3)) $in cart_n(R,3)",
        "laplacian(f,(1,2),2) $in R",
    ] {
        let run = check(&mut rt, goal, false);
        let json = crate::json_output::project_run_detailed(&run, &rt, "WD", None).stringify();
        assert!(
            json.contains("previously proved candidate") || json.contains("Selection"),
            "{goal}: {json}"
        );
    }
    check(&mut rt, "$has_partial_derivative_at(f,(1,2),2,1,3)", false);
    check(&mut rt, "partial_derivative(f,(1,2),2,1)=3", false);
    check(&mut rt, "$has_partial_derivative_at(f,(1,2),2,1,2)", true);
    check(&mut rt, "partial_derivative(f,(1,2),2,1)=2", true);
    check(&mut rt, "$has_partial_derivative_at(f,(1,2),2,3,0)", false);
    check(&mut rt, "$has_partial_derivative_at(f,(1,2),0,1,2)", false);
    check(&mut rt, "partial_derivative(f,(2,2),2,1)=4", false);
    check(&mut rt, "0=0", true);
}
#[test]
fn multivariable_calculus_partials_are_not_total_differentiability() {
    let mut rt = runtime();
    check(&mut rt,"thm unsupported_from_partials:\n    ? forall f fn(x cart_n(R,2)) R,p cart_n(R,2),a,b R:\n        $has_partial_derivative_at(f,p,2,1,a)\n        $has_partial_derivative_at(f,p,2,2,b)\n        =>:\n            $is_multi_differentiable_at(f,p,2)",false);
    check(
        &mut rt,
        "have fn boundary(x cart_n(R,2): x(1)>=0) R=x(1)^2+x(2)",
        true,
    );
    check(&mut rt, "(0,2)(1)=0", true);
    check(&mut rt, "(0,2) $in cart_n(R,2)", true);
    check(&mut rt, "(0,2)(1)>=0", true);
    check(&mut rt, "(0,2) $in {x cart_n(R,2): x(1)>=0}", true);
    check(
        &mut rt,
        "$is_multi_differentiable_at(boundary,(0,2),2)",
        false,
    );
    check(
        &mut rt,
        "have fn two_dimensional(x cart_n(R,2)) cart_n(R,2)=(x(1),x(2))",
        true,
    );
    check(
        &mut rt,
        "$has_curl_at(two_dimensional,(1,2),(0,0,0))",
        false,
    );
    check(&mut rt, "0=0", true);
}
#[test]
fn multivariable_calculus_parser_names_and_capture_avoiding_substitution() {
    let mut rt = runtime();
    check(&mut rt, "have a R=2", true);
    let original = parse_object(&mut rt, "gradient_at(fn(x cart_n(R,2)) R {x(1)+a},(a,1),2)");
    check(&mut rt, "have x R=7", true);
    let a = rt.resolve_plain_atom("a").unwrap();
    let x = rt.resolve_plain_atom("x").unwrap();
    let replacement = Obj::Identifier(IdentifierObj::plain(x, "x".into()));
    let replaced = rt
        .inst_obj(
            &original,
            &std::collections::HashMap::from([(a, replacement)]),
        )
        .unwrap();
    let mut free = std::collections::HashSet::new();
    crate::instantiate::collect_free_plain_ids(
        &replaced,
        &std::collections::HashSet::new(),
        &mut free,
    );
    assert!(free.contains(&x));
    assert!(!free.contains(&a));
    for source in [
        "lim(fn(k N+) R {k},0)=0",
        "fn_lim(fn(z cart_n(R,2)) R {z(1)},(0,0))=0",
        "gradient_at(fn(z cart_n(R,2)) R {z(1)},(0,0))=(0,0)",
        "partial_derivative(fn(z cart_n(R,2)) R {z(1)},(0,0),2)=0",
    ] {
        check(&mut rt, source, false);
    }
}

#[test]
fn multivariable_calculus_accepts_exact_function_space_coordinates() {
    let mut rt = runtime();
    check(
        &mut rt,
        "have fn f(x fn(k closed_range(1,2)) R) R=x(1)^2+x(2)^2",
        true,
    );
    check(&mut rt, "$has_partial_derivative_at(f,(1,2),2,1,2)", true);
    check(&mut rt, "partial_derivative(f,(1,2),2,1)=2", true);
}

#[test]
fn multivariable_calculus_all_operators_and_detailed_provenance() {
    let mut rt = runtime();
    let source = r#"have fn bowl(x cart_n(R,2)) R=x(1)^2+x(2)^2
$has_multi_limit_at(bowl,(1,2),2,5)
lim_multi_at(bowl,(1,2),2)=5
$is_multi_continuous_at(bowl,(1,2),2)
$has_partial_derivative_at(bowl,(1,2),2,1,2)
partial_derivative(bowl,(1,2),2,1)=2
$has_gradient_at(bowl,(1,2),2,(2,4))
gradient_at(bowl,(1,2),2)(2)=4
$has_scalar_differential_at(bowl,(1,2),2,fn(row closed_range(1,1),col closed_range(1,2)) R {(2,4)(col)})
scalar_differential(bowl,(1,2),2)(1,1)=2
$is_multi_differentiable_at(bowl,(1,2),2)
$has_second_partial_derivative_at(bowl,(1,2),2,1,2,0)
$has_hessian_at(bowl,(1,2),2,fn(row,col closed_range(1,2)) R {2*identity_matrix(2)(row,col)})
hessian(bowl,(1,2),2)(1,2)=0
$has_laplacian_at(bowl,(1,2),2,4)
laplacian(bowl,(1,2),2)=4
have fn field(x cart_n(R,3)) cart_n(R,3)=(x(1),x(2),x(3))
$has_vector_limit_at(field,(1,2,3),3,3,(1,2,3))
lim_vector_at(field,(1,2,3),3,3)(2)=2
$is_vector_continuous_at(field,(1,2,3),3,3)
$has_total_derivative_at(field,(1,2,3),3,3,identity_matrix(3))
differential(field,(1,2,3),3,3)(2,2)=1
$is_vector_differentiable_at(field,(1,2,3),3,3)
$has_jacobian_at(field,(1,2,3),3,3,identity_matrix(3))
jacobian(field,(1,2,3),3,3)(1,2)=0
$has_divergence_at(field,(1,2,3),3,3)
divergence(field,(1,2,3),3)=3
$has_curl_at(field,(1,2,3),(0,0,0))
curl(field,(1,2,3))(1)=0
have fn oscillation(x cart_n(R,2)) R=sin(x(1)*x(2))
$has_partial_derivative_at(oscillation,(0,2),2,1,2)
$has_second_partial_derivative_at(oscillation,(0,2),2,1,2,1)"#;
    let run = check(&mut rt, source, true);
    let json =
        crate::json_output::project_run_detailed(&run, &rt, "multivariable", None).stringify();
    for label in [
        "SmoothMultivariableExpression",
        "body_well_defined",
        "MultivariableSelectedValue",
        "MultivariableSelectedComponent",
        "finite_set_evaluation",
        "periodic_trig",
        "value_source_well_defined",
    ] {
        assert!(json.contains(label), "{label}");
    }
    check(&mut rt, "gradient_at(bowl,(1,2),2) $in R", false);
    check(&mut rt, "gradient_at(bowl,(1,2),2)(3)=0", false);
    check(&mut rt, "$has_laplacian_at(bowl,(1,2),2,5)", false);
    let latex =
        crate::compile_to_latex::to_latex_from_source(source, OutputLanguage::English).unwrap();
    for symbol in ["\\nabla", "\\partial", "\\lim", "\\Delta"] {
        assert!(latex.contains(symbol), "{symbol}");
    }
}
#[test]
fn multivariable_calculus_lean_boundary_and_polarity() {
    let mut rt = runtime();
    let source="forall f fn(x cart_n(R,2)) R,p cart_n(R,2),L R:\n    $has_partial_derivative_at(f,p,2,1,L)\n    =>:\n        partial_derivative(f,p,2,1)=L";
    let run = check(&mut rt, source, true);
    let error = crate::compile_to_lean::LitexToLeanCompiler::new(rt)
        .compile_run(&run, "multivariable_boundary")
        .unwrap_err();
    assert!(
        error.message.contains("not supported") || error.message.contains("Unsupported"),
        "{error}"
    );
    let mut rt = runtime();
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize(
            "$has_partial_derivative_at(fn(x cart_n(R,2)) R {x(1)},(0,0),2,1,1)",
            rt.current_file.clone(),
        )
        .unwrap();
    let Stmt::Fact(Fact::AtomicFact(atom)) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("atom")
    };
    let id = rt.global_ids.allocate_fact_id();
    let negative = crate::ast::fact::negate_atomic_fact(&atom, id).unwrap();
    assert!(matches!(
        negative,
        AtomicFact::NotMultivariableAnalysisFact(_)
    ));
    assert_eq!(negative.fact_id(), id);
    let id = rt.global_ids.allocate_fact_id();
    let restored = crate::ast::fact::negate_atomic_fact(&negative, id).unwrap();
    assert_eq!(restored.readable_string(), atom.readable_string());
}

#[test]
fn multivariable_calculus_opaque_function_matrices_and_grouping() {
    let mut rt = runtime();
    check(&mut rt,"forall f fn(x cart_n(R,2)) R,p cart_n(R,2),A fn(row,col closed_range(1,2)) R:\n    $has_hessian_at(f,p,2,A)\n    =>:\n        hessian(f,p,2)=A",true);
    check(&mut rt,"forall f fn(x cart_n(R,2)) R,p cart_n(R,2),A fn(row,col closed_range(1,2): row!=col) R:\n    $has_hessian_at(f,p,2,A)\n    =>:\n        hessian(f,p,2)=A",false);
}

#[test]
fn multivariable_calculus_definition_projection_and_scoped_coordinate_carriers() {
    let mut rt = runtime();
    check(
        &mut rt,
        "forall v cart_n(R,2),k closed_range(1,2):\n    (v(k)-(1,2)(k)) $in R",
        true,
    );
    check(
        &mut rt,
        "forall k closed_range(1,2):\n    (1,i)(k) $in R",
        false,
    );
    check(&mut rt, "(1,2)(3) $in R", false);
    check(
        &mut rt,
        include_str!("../../../examples/real_analysis/multivariable/main.lit"),
        true,
    );
    check(
        &mut rt,
        "release thm multi_limit_at_to_definition(bowl,(1,2),2,5)",
        true,
    );
    check(
        &mut rt,
        "release thm multi_limit_at_from_definition(bowl,(1,2),2,5)",
        true,
    );
    check(
        &mut rt,
        "forall A matrix(R,1,2),v cart_n(R,2):\n    (1-matrix_apply(A,v,1,2)(1)) $in R",
        true,
    );
    check(
        &mut rt,
        "matrix_apply(fn(row closed_range(1,1),col closed_range(1,2)) C {i},(1,2),1,2)(1) $in R",
        false,
    );
    check(&mut rt,"release thm scalar_differential_at_to_definition(bowl,(1,2),2,fn(row closed_range(1,1),col closed_range(1,2)) R {(2,4)(col)})",true);
    check(&mut rt,"forall y cart_n(R,3):\n    fn(k closed_range(1,3)) R {field(y)(k)-matrix_apply(identity_matrix(3),y,3,3)(k)} $in cart_n(C,3)",true);
    check(
        &mut rt,
        "fn(k closed_range(1,3): k!=2) R {0} $in cart_n(C,3)",
        false,
    );
    check(
        &mut rt,
        "fn(k closed_range(1,3)) C {i} $in cart_n(R,3)",
        false,
    );
    check(
        &mut rt,
        "release thm total_derivative_at_to_definition(field,(1,2,3),3,3,identity_matrix(3))",
        true,
    );
}
