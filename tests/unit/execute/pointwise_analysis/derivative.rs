use crate::prelude::*;
use std::collections::{HashMap, HashSet};
#[test]
fn pointwise_derivative_tests_capture_avoidance_and_alpha_equivalence() {
    let mut rt = runtime();
    check(&mut rt, "have a R=2", true);
    let AtomicFact::HasDerivativeAtFact(candidate) =
        parse_atomic(&mut rt, "$has_derivative_at(fn(x R) R {x+a},a,1)")
    else {
        panic!("candidate")
    };
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(body)) = &candidate.function else {
        panic!("literal")
    };
    let binder = body.body.set_bound_parameters.groups[0].params[0].clone();
    // Same spelling, distinct scope/identity. The insertion must remain free
    // inside the function and in the derivative's separate point argument.
    check(&mut rt, "have x R=7", true);
    let a_id = rt.resolve_plain_atom("a").unwrap();
    let x_id = rt.resolve_plain_atom("x").unwrap();
    assert_ne!(x_id, binder.id);
    let replacement = Obj::Identifier(IdentifierObj::plain(x_id, "x".into()));
    let zero = Obj::Literal(Literal::Number(Number::new("0".into())));
    let original: Obj = DerivativeAt::new(candidate.function, candidate.point).into();
    let inst = rt
        .inst_obj(
            &original,
            &HashMap::from([
                (a_id, replacement.clone()),
                (x_id, zero.clone()),
                (binder.id, zero),
            ]),
        )
        .unwrap();
    let Obj::DerivativeOperator(DerivativeOperator::AtPoint(inst)) = inst else {
        panic!("derivative")
    };
    assert_eq!(*inst.point, replacement);
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(body)) = inst.function.as_ref() else {
        panic!("literal")
    };
    let new_binder = &body.body.set_bound_parameters.groups[0].params[0];
    assert_eq!(new_binder.id, binder.id);
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = body.equal_to.as_ref() else {
        panic!("sum")
    };
    assert_eq!(
        *sum.left,
        Obj::Identifier(IdentifierObj::from_bound_name(new_binder))
    );
    assert_eq!(*sum.right, replacement);
    let mut free = HashSet::new();
    crate::instantiate::collect_free_plain_ids(
        &Obj::DerivativeOperator(DerivativeOperator::AtPoint(inst.clone())),
        &HashSet::new(),
        &mut free,
    );
    assert_eq!(free, HashSet::from([x_id]));
    let AtomicFact::HasDerivativeAtFact(a) =
        parse_atomic(&mut rt, "$has_derivative_at(fn(y R) R {y},0,1)")
    else {
        panic!("candidate")
    };
    let left: Obj = DerivativeAt::new(
        a.function,
        Obj::Literal(Literal::Number(Number::new("0".into()))),
    )
    .into();
    let AtomicFact::HasDerivativeAtFact(b) =
        parse_atomic(&mut rt, "$has_derivative_at(fn(z R) R {z},0,1)")
    else {
        panic!("candidate")
    };
    let right: Obj = DerivativeAt::new(
        b.function,
        Obj::Literal(Literal::Number(Number::new("0".into()))),
    )
    .into();
    assert!(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::compound_objs_alpha_equal(&left,&right));
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
fn parse_atomic(rt: &mut Runtime, source: &str) -> AtomicFact {
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize(source, rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(Fact::AtomicFact(f)) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("atomic")
    };
    f
}
#[test]
fn pointwise_derivative_tests_tracer_generic_closure_and_evidence() {
    let mut rt = runtime();
    let run = check(
        &mut rt,
        include_str!(
            "../../../../examples/proof_nodes/atomic/by_builtin_strategy/pointwise_derivative.lit"
        ),
        true,
    );
    let json = crate::json_output::project_run_detailed(&run, &rt, "pointwise", None).stringify();
    for tag in [
        "PointwiseDerivative",
        "DerivativeSelectedValue",
        "body_well_defined",
        "interior",
        "StableOpenGuards",
        "ProductRule",
        "QuotientRule",
        "NaturalPower",
        "ChainRule",
        "outer_point",
        "derivative_real",
    ] {
        assert!(json.contains(tag), "{tag}");
    }
}
#[test]
fn pointwise_derivative_tests_nearest_negatives_and_session_survival() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/unit/execute/pointwise_analysis/fixtures");
    for entry in std::fs::read_dir(dir).unwrap() {
        let file = entry.unwrap().path();
        if file.extension().is_none_or(|s| s != "lit") {
            continue;
        }
        let mut rt = runtime();
        check(&mut rt, "have anchor R=7", true);
        check(&mut rt, &std::fs::read_to_string(&file).unwrap(), false);
        check(&mut rt, "anchor+1=8", true);
    }
}
#[test]
fn pointwise_derivative_tests_selection_requires_proof_and_is_not_an_evaluator() {
    let mut rt = runtime();
    check(&mut rt, "have fn square(x R) R=x^2", true);
    check(&mut rt, "derivative(square,3)=6", false);
    check(&mut rt, "0*derivative(square,3)=0", false);
    check(&mut rt, "$has_derivative_at(square,3,6)", true);
    check(&mut rt, "$is_differentiable_at(square,3)", true);
    check(&mut rt, "derivative(square,3)=6", true);
    check(&mut rt, "derivative(square,3)+2=8", true);
    check(&mut rt, "derivative(square,3)=5", false);
    check(&mut rt, "derivative(square,4)=8", false);
    check(&mut rt, "derivative(square,3)=6", true);
    check(&mut runtime(),"forall f fn(x R) R,p R:\n    $is_differentiable_at(f,p)\n    =>:\n        derivative(f,p) $in R",true);
    check(&mut runtime(),"forall f,g fn(x R) R,p,q,L R:\n    f=g\n    p=q\n    $has_derivative_at(f,p,L)\n    =>:\n        derivative(f,p)=derivative(g,q)",true);
}
#[test]
fn pointwise_derivative_tests_classical_interior_is_distinct_from_relative_continuity() {
    let mut rt = runtime();
    check(&mut rt, "have fn isolated(x {0}) R=x*x", true);
    check(&mut rt, "$is_continuous_at(isolated,0)", true);
    check(&mut rt, "$is_differentiable_at(isolated,0)", false);
    check(&mut rt, "$has_derivative_at(fn(x R:x>0) R {x*x},2,4)", true);
    check(&mut rt, "$has_derivative_at(fn(x R*) R {1/x},2,-1/4)", true);
    check(&mut rt, "$has_derivative_at(fn(x R) R {x^0},0,0)", true);
    check(&mut rt, "$has_derivative_at(fn(x R) R {x^1},0,1)", true);
}
#[test]
fn pointwise_derivative_tests_search_ceiling_and_failed_scope() {
    let mut rt = runtime();
    check(&mut rt, "have fn square(x R) R=x*x", true);
    let goal: Fact = parse_atomic(&mut rt, "$has_derivative_at(square,3,6)").into();
    assert!(rt
        .verify_fact(&goal, VerifyState::new(VerifyStateLevel::BuiltinRule))
        .unwrap()
        .is_failed());
    check(
        &mut rt,
        "claim:\n    ? 0=1\n    $has_derivative_at(square,3,6)\n    0=1",
        false,
    );
    check(&mut rt, "derivative(square,3)=6", false);
    assert!(rt
        .verify_fact(&goal, VerifyState::new(VerifyStateLevel::BuiltinRule))
        .unwrap()
        .is_failed());
    check(&mut rt, "$has_derivative_at(square,3,6)", true);
    check(&mut rt, "derivative(square,3)=6", true);
}
#[test]
fn pointwise_derivative_tests_explicit_catalog_and_premise_controls() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples/stmt_nodes/release_and_expand/builtin_thm");
    let mut count = 0;
    for entry in std::fs::read_dir(dir).unwrap() {
        let file = entry.unwrap().path();
        let Some(name) = file.file_name().and_then(|n| n.to_str()) else {
            continue;
        };
        if !name.starts_with("fn_derivative_at_") && !name.starts_with("fn_differentiable_at_") {
            continue;
        }
        check(
            &mut runtime(),
            &std::fs::read_to_string(file).unwrap(),
            true,
        );
        count += 1;
    }
    assert_eq!(count, 27);
    for source in [
        "have fn square(x R) R=x*x\nrelease thm fn_derivative_at_constant(square,0,1)",
        "have fn isolated(x {0}) R=1\nrelease thm fn_derivative_at_constant(isolated,0,1)",
        "have fn f(x R) R=x\nrelease thm fn_derivative_at_exists(f,0,2)",
        "have fn f(x R) R=x\nrelease thm fn_derivative_at_selected(f,0)",
    ] {
        check(&mut runtime(), source, false);
    }
}
#[test]
fn pointwise_derivative_tests_polarity_arguments_and_substitution() {
    let mut rt = runtime();
    for source in [
        "$has_derivative_at(fn(x R) R {x},0,1)",
        "$is_differentiable_at(fn(x R) R {x},0)",
    ] {
        let original = parse_atomic(&mut rt, source);
        let id = rt.global_ids.allocate_fact_id();
        let negative = crate::ast::fact::negate_atomic_fact(&original, id).unwrap();
        assert_eq!(negative.fact_id(), id);
        assert!(matches!(
            negative,
            AtomicFact::NotHasDerivativeAtFact(_) | AtomicFact::NotFunctionDifferentiableAtFact(_)
        ));
        let next = rt.global_ids.allocate_fact_id();
        let restored = crate::ast::fact::negate_atomic_fact(&negative, next).unwrap();
        assert_eq!(restored.readable_string(), original.readable_string());
        let copy = rt.inst_atomic_fact_rec(&negative, &HashMap::new()).unwrap();
        assert_ne!(copy.fact_id(), negative.fact_id());
        assert_eq!(copy.readable_string(), negative.readable_string());
    }
    let f = rt.fresh_internal_param();
    let p = rt.fresh_internal_param();
    let v = rt.fresh_internal_param();
    let obj = |b: &crate::ast::names::BoundName| Obj::Identifier(IdentifierObj::from_bound_name(b));
    let original: AtomicFact = HasDerivativeAtFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        function: obj(&f),
        point: obj(&p),
        value: obj(&v),
        line_file: None,
    }
    .into();
    let n = |s: &str| Obj::Literal(Literal::Number(Number::new(s.into())));
    let args = HashMap::from([(f.id, n("2")), (p.id, n("3")), (v.id, n("4"))]);
    let inst = rt.inst_atomic_fact_rec(&original, &args).unwrap();
    let AtomicFact::HasDerivativeAtFact(inst) = inst else {
        panic!("candidate")
    };
    assert_eq!(inst.function, n("2"));
    assert_eq!(inst.point, n("3"));
    assert_eq!(inst.value, n("4"));
    let op: Obj = DerivativeAt::new(obj(&f), obj(&p)).into();
    let mut free = HashSet::new();
    crate::instantiate::collect_free_plain_ids(&op, &HashSet::new(), &mut free);
    assert_eq!(free, HashSet::from([f.id, p.id]));
    let inst = rt.inst_obj(&op, &args).unwrap();
    assert_eq!(inst, DerivativeAt::new(n("2"), n("3")).into());
}
#[test]
fn pointwise_derivative_tests_parser_latex_and_lean_boundary() {
    for source in [
        "have derivative R=1",
        "prop has_derivative_at(f fn(x R) R,p,L R):\n    L=L",
        "prop is_differentiable_at(f fn(x R) R,p R):\n    p=p",
        "derivative()=0",
        "derivative(1,2,3)=0",
        "$has_derivative_at(1,2)",
        "$is_differentiable_at(1,2,3)",
    ] {
        let mut rt = runtime();
        let tokens = crate::tokenize::Tokenizer::new()
            .tokenize(source, rt.current_file.clone())
            .unwrap();
        assert!(rt.parse(&tokens).is_err(), "{source}");
    }
    let source="forall f fn(x R) R,p,L R:\n    $has_derivative_at(f,p,L)\n    =>:\n        derivative(f,p)=L";
    let latex =
        crate::compile_to_latex::to_latex_from_source(source, OutputLanguage::English).unwrap();
    assert!(latex.contains("^{\\prime}"), "{latex}");
    let mut rt = runtime();
    let run = check(&mut rt, source, true);
    let json = crate::json_output::project_run_detailed(&run, &rt, "test", None).stringify();
    for tag in [
        "DerivativeSelectedValue",
        "function_wd",
        "point_wd",
        "convergence",
    ] {
        assert!(json.contains(tag), "{tag}");
    }
    let error = crate::compile_to_lean::LitexToLeanCompiler::new(rt)
        .compile_run(&run, "derivative_boundary")
        .unwrap_err();
    assert!(
        error.message.contains("not supported") || error.message.contains("Unsupported"),
        "{error}"
    );
}
#[test]
fn pointwise_derivative_tests_min_max_carriers_and_safe_natural_difference() {
    let mut rt = runtime();
    let run=check(&mut rt,"forall a,b N:\n    min(a,b) $in N\n    max(a,b) $in Z\n    max(a,b)-a $in N\n    max(a,b)-b $in N",true);
    let json = crate::json_output::project_run_detailed(&run, &rt, "test", None).stringify();
    assert!(json.contains("natural_max_difference"));
    check(
        &mut rt,
        "forall a,b Z:\n    min(a,b) $in Z\n    max(a,b) $in Z",
        true,
    );
    check(
        &mut rt,
        "forall a,b Q:\n    min(a,b) $in Q\n    max(a,b) $in Q",
        true,
    );
}
