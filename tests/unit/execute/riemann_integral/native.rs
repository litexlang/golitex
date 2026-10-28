use crate::prelude::*;

#[test]
fn riemann_integral_native_valid_functions_need_integrability_proofs() {
    for source in [
        "have fn rational_flag(x R) R by cases:\n    case x $in Q: 1\n    case not x $in Q: 0\n",
        "have fn filled_reciprocal(x R) R by cases:\n    case x=0: 0\n    case x!=0: 1/x\n",
    ] {
        let mut rt = runtime();
        check(&mut rt, source, true);
        let name = if source.contains("rational_flag") {
            "rational_flag"
        } else {
            "filled_reciprocal"
        };
        let candidate = format!("$has_riemann_integral({name},0,1,0)");
        let tokens = crate::tokenize::Tokenizer::new()
            .tokenize(&candidate, rt.current_file.clone())
            .unwrap();
        let Stmt::Fact(Fact::AtomicFact(fact)) = rt.parse(&tokens).unwrap().remove(0) else {
            panic!("candidate")
        };
        let wd = rt
            .verify_atomic_fact_well_definedness(&fact, VerifyState::top_level())
            .unwrap();
        assert!(!wd.is_failed(),"A total real function is a legal candidate input; lack of a proof is distinct from ill-formed input.");
        check(&mut rt, &candidate, false);
        check(&mut rt, &format!("integral({name},0,1)=0"), false);
    }
}

#[test]
fn riemann_integral_representation_negation_substitution_and_capture() {
    use std::collections::{HashMap, HashSet};
    let mut rt = runtime();
    check(&mut rt, "have a R=2\nhave b R=3", true);
    let source = "$has_riemann_integral(fn(x R) R {x+a},a,b,5)";
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize(source, rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(Fact::AtomicFact(fact)) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("candidate")
    };
    let AtomicFact::HasRiemannIntegralFact(c) = &fact else {
        panic!("candidate")
    };
    let op: Obj = RiemannIntegral::new(c.function.clone(), c.lower.clone(), c.upper.clone()).into();
    check(&mut rt, "have x R=7", true);
    let a = rt.resolve_plain_atom("a").unwrap();
    let x = rt.resolve_plain_atom("x").unwrap();
    let replacement = Obj::Identifier(IdentifierObj::plain(x, "x".into()));
    let inst = rt
        .inst_obj(&op, &HashMap::from([(a, replacement.clone())]))
        .unwrap();
    let Obj::IntegralOperator(IntegralOperator::Riemann(i)) = &inst else {
        panic!("integral")
    };
    assert_eq!(*i.lower, replacement);
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(body)) = i.function.as_ref() else {
        panic!("literal")
    };
    let binding = &body.body.set_bound_parameters.groups[0].params[0];
    assert_ne!(binding.id, x);
    let mut free = HashSet::new();
    crate::instantiate::collect_free_plain_ids(&inst, &HashSet::new(), &mut free);
    assert!(free.contains(&x));
    assert!(!free.contains(&binding.id));
    for source in [
        "$has_riemann_integral(fn(t R) R {t},0,1,1/2)",
        "$is_riemann_integrable(fn(t R) R {t},0,1)",
    ] {
        let tokens = crate::tokenize::Tokenizer::new()
            .tokenize(source, rt.current_file.clone())
            .unwrap();
        let Stmt::Fact(Fact::AtomicFact(f)) = rt.parse(&tokens).unwrap().remove(0) else {
            panic!("fact")
        };
        let id = rt.global_ids.allocate_fact_id();
        let neg = crate::ast::fact::negate_atomic_fact(&f, id).unwrap();
        assert_eq!(neg.fact_id(), id);
        assert!(!crate::ast::fact::atomic_fact_has_positive_polarity(&neg));
        let back =
            crate::ast::fact::negate_atomic_fact(&neg, rt.global_ids.allocate_fact_id()).unwrap();
        assert_eq!(back.readable_string(), f.readable_string());
        let copy = rt.inst_atomic_fact_rec(&neg, &HashMap::new()).unwrap();
        assert_ne!(copy.fact_id(), neg.fact_id());
        assert_eq!(copy.readable_string(), neg.readable_string());
    }
}
#[test]
fn riemann_integral_representation_parser_latex_and_lean_boundary() {
    for source in [
        "have integral R=1",
        "integral()=0",
        "integral(1,2)=0",
        "integral(1,2,3,4)=0",
        "$has_riemann_integral(1,2,3)",
        "$is_riemann_integrable(1,2)",
        "prop has_riemann_integral(f fn(x R) R,a,b,I R):\n    I=I",
        "prop is_riemann_integrable(f fn(x R) R,a,b R):\n    a=a",
        "prop is_darboux_enclosure(f fn(x R) R,a,b,n,p,l,u R):\n    a=a",
    ] {
        let mut rt = runtime();
        let tokens = crate::tokenize::Tokenizer::new()
            .tokenize(source, rt.current_file.clone())
            .unwrap();
        assert!(rt.parse(&tokens).is_err(), "{source}");
    }
    let source="forall f fn(x R) R,a,b,I R:\n    $has_riemann_integral(f,a,b,I)\n    =>:\n        integral(f,a,b)=I";
    let latex =
        crate::compile_to_latex::to_latex_from_source(source, OutputLanguage::English).unwrap();
    assert!(latex.contains("\\int_"));
    assert!(latex.contains("\\mathrm{d}\\xi"));
    let mut rt = runtime();
    let run = check(&mut rt, source, true);
    let json = crate::json_output::project_run_detailed(&run, &rt, "riemann", None).stringify();
    assert!(json.contains("RiemannIntegralSelectedValue"));
    let error = crate::compile_to_lean::LitexToLeanCompiler::new(rt)
        .compile_run(&run, "riemann_boundary")
        .unwrap_err();
    assert!(
        error.message.contains("not supported") || error.message.contains("Unsupported"),
        "{error}"
    );
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
    if run.success != expected {
        panic!(
            "{source}\n{}",
            crate::json_output::project_run_detailed(&run, rt, "riemann", None).stringify()
        );
    }
    run
}
#[test]
fn riemann_integral_native_candidate_selection_and_provenance() {
    let mut rt = runtime();
    check(&mut rt, "have fn square(x R) R=x^2", true);
    check(&mut rt, "integral(square,0,1)=1/3", false);
    check(&mut rt, "0*integral(square,0,1)=0", false);
    check(
        &mut rt,
        "release thm riemann_integral_power(square,0,1,2)",
        true,
    );
    check(&mut rt, "$has_riemann_integral(square,0,1,1/3)", true);
    check(&mut rt, "$is_riemann_integrable(square,0,1)", true);
    let run = check(&mut rt, "integral(square,0,1)=1/3", true);
    let json = crate::json_output::project_run_detailed(&run, &rt, "riemann", None).stringify();
    assert!(json.contains("IntegralOperator"));
    assert!(json.contains("selection"));
    assert!(json.contains("RiemannIntegralSelectedValue"));
    check(&mut rt, "integral(square,0,1)+2=7/3", true);
    check(&mut rt, "$has_riemann_integral(square,0,1,1/2)", false);
    check(
        &mut rt,
        "release thm riemann_integral_to_definition(square,0,1,1/3)",
        true,
    );
    check(
        &mut rt,
        "release thm riemann_integral_reverse(square,0,1,1/3)",
        true,
    );
    check(&mut rt, "integral(square,1,0)=-1/3", true);
    check(&mut rt, "release thm riemann_integral_zero(square,2)", true);
    check(&mut rt, "integral(square,2,2)=0", true);
}
#[test]
fn riemann_integral_native_existence_does_not_guess_a_value() {
    let mut rt = runtime();
    check(&mut rt, "have fn square(x R) R=x^2", true);
    check(
        &mut rt,
        "release thm riemann_integrable_continuous(square,0,1)",
        true,
    );
    assert!(rt.known_riemann_integral_candidates().is_empty());
    check(&mut rt, "integral(square,0,1)=integral(square,0,1)", true);
    check(&mut rt, "integral(square,0,1)=1/3", false);
    check(
        &mut rt,
        "release thm riemann_integral_selected(square,0,1)",
        true,
    );
    check(
        &mut rt,
        "$has_riemann_integral(square,0,1,integral(square,0,1))",
        true,
    );
}
#[test]
fn riemann_integral_native_domain_and_missing_premises_survive_rejection() {
    for source in [
        "have fn reciprocal(x R*) R=1/x\nrelease thm riemann_integral_zero(reciprocal,0)",
        "have fn reciprocal(x R*) R=1/x\n$has_riemann_integral(reciprocal,-1,1,0)",
        "have fn complex_input(x C) R=0\nrelease thm riemann_integral_constant(complex_input,0,1,0)",
        "have fn complex_output(x R) C=i\nrelease thm riemann_integral_constant(complex_output,0,1,0)",
        "have fn sequence(k N+) R=k\nrelease thm riemann_integral_power(sequence,1,2,1)",
        "have fn square(x R) R=x^2\nrelease thm riemann_integral_constant(square,0,1,0)",
        "have fn square(x R) R=x^2\nrelease thm riemann_integral_from_definition(square,0,1,1/3)",
        "have fn square(x R) R=x^2\nrelease thm riemann_integral_newton_leibniz(square,square,0,1)",
    ] {
        let mut rt=runtime();check(&mut rt,"have anchor R=7",true);
        check(&mut rt,source,false);check(&mut rt,"anchor+1=8",true);
    }
}
#[test]
fn riemann_integral_native_actual_closed_and_guarded_domains() {
    let mut rt = runtime();
    check(&mut rt, "have fn local_square(x '[0,1]) R=x^2", true);
    check(
        &mut rt,
        "release thm riemann_integral_power(local_square,0,1,2)",
        true,
    );
    check(&mut rt, "integral(local_square,0,1)=1/3", true);
    check(&mut rt, "have fn guarded(x R:x>=0,x<=1) R=x^2", true);
    check(&mut rt,"claim:\n    ? '[0,1] $subset {x R:x>=0,x<=1}\n    forall x '[0,1]:\n        x>=0\n        x<=1\n        x $in {t R:t>=0,t<=1}\n    by def '[0,1] $subset {x R:x>=0,x<=1}\n",true);
    check(
        &mut rt,
        "release thm riemann_integral_power(guarded,0,1,2)",
        true,
    );
    check(&mut rt, "integral(guarded,0,1)=1/3", true);
    check(
        &mut rt,
        "release thm riemann_integral_extensional(local_square,guarded,0,1,1/3)",
        true,
    );
    check(
        &mut rt,
        "$has_riemann_integral(local_square,0,2,8/3)",
        false,
    );
}
#[test]
fn riemann_integral_native_linearity_split_comparison_and_bound() {
    let mut rt = runtime();
    check(&mut rt,"have fn square(x R) R=x^2\nhave fn one(x R) R=1\nhave fn total(x R) R=x^2+1\nhave fn difference(x R) R=x^2-1\nhave fn scaled(x R) R=3*x^2",true);
    check(&mut rt,"release thm riemann_integral_power(square,0,1,2)\nrelease thm riemann_integral_constant(one,0,1,1)",true);
    check(
        &mut rt,
        "release thm riemann_integral_add(square,one,total,0,1,1/3,1)",
        true,
    );
    check(&mut rt, "integral(total,0,1)=4/3", true);
    check(
        &mut rt,
        "release thm riemann_integral_subtract(square,one,difference,0,1,1/3,1)",
        true,
    );
    check(&mut rt, "integral(difference,0,1)=-2/3", true);
    check(
        &mut rt,
        "release thm riemann_integral_scale(square,scaled,0,1,3,1/3)",
        true,
    );
    check(&mut rt, "integral(scaled,0,1)=1", true);
    check(
        &mut rt,
        "release thm riemann_integral_power(square,1,2,2)",
        true,
    );
    check(
        &mut rt,
        "release thm riemann_integral_split(square,0,1,2,1/3,7/3)",
        true,
    );
    check(&mut rt, "integral(square,0,2)=8/3", true);
    check(
        &mut rt,
        "release thm riemann_integral_compare(square,total,0,1,1/3,4/3)",
        true,
    );
    check(
        &mut rt,
        "claim:\n    ? forall x R:\n        abs(one(x))<=1\n    one(x)=1\n    abs(one(x))=1\n",
        true,
    );
    check(
        &mut rt,
        "release thm riemann_integral_bound(one,0,1,1,1)",
        true,
    );
    check(
        &mut rt,
        "release thm riemann_integral_compare(total,square,0,1,4/3,1/3)",
        false,
    );
}
#[test]
fn riemann_integral_native_darboux_enclosure_and_false_bounds() {
    let mut rt = runtime();
    check(&mut rt,"have fn two(x R) R=2\nhave fn p(k Z:0<=k,k<=1) R=k\nhave fn lo(k Z:1<=k,k<=1) R=2\nhave fn hi(k Z:1<=k,k<=1) R=2",true);
    check(
        &mut rt,
        "release thm darboux_enclosure_from_definition(two,0,1,1,p,lo,hi)",
        true,
    );
    check(&mut rt, "$is_darboux_enclosure(two,0,1,1,p,lo,hi)", true);
    check(
        &mut rt,
        "release thm darboux_enclosure_to_definition(two,0,1,1,p,lo,hi)",
        true,
    );
    check(&mut rt, "have fn wrong(k Z:1<=k,k<=1) R=3", true);
    check(
        &mut rt,
        "release thm darboux_enclosure_from_definition(two,0,1,1,p,wrong,wrong)",
        false,
    );
}
#[test]
fn riemann_integral_native_newton_leibniz_and_discontinuous_step() {
    let mut rt = runtime();
    check(
        &mut rt,
        "have fn unity(x R) R=1\nhave fn linear(x R) R=x",
        true,
    );
    check(
        &mut rt,
        "release thm riemann_integrable_continuous(unity,0,1)",
        true,
    );
    check(&mut rt,"claim:\n    ? forall x R:\n        $has_derivative_at(linear,x,unity(x))\n    unity(x)=1\n    $has_derivative_at(linear,x,1)\n    $has_derivative_at(linear,x,unity(x))\n",true);
    check(
        &mut rt,
        "release thm riemann_integral_newton_leibniz(unity,linear,0,1)",
        true,
    );
    check(
        &mut rt,
        "linear(1)=1\nlinear(0)=0\nlinear(1)-linear(0)=1\nintegral(unity,0,1)=1",
        true,
    );
    check(&mut rt, "have fn jump(x R) R=sign(x)", true);
    check(
        &mut rt,
        "release thm riemann_integral_step(jump,-1,0,1,-1,1)",
        true,
    );
    check(&mut rt, "integral(jump,-1,1)=0", true);
}
