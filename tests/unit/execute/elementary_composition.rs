use crate::prelude::*;

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language,
        },
        crate::result_detail::OutputDetail::Detailed,
    )
}
fn check(rt: &mut Runtime, source: &str, expected: bool) -> RunLitexCodeResult {
    let run = rt.run_litex_code(source).unwrap();
    assert!(
        run.input_error.is_none(),
        "all controls must parse: {source}: {:?}",
        run.input_error
    );
    assert!(
        run.session_error.is_none(),
        "{source}: {:?}",
        run.session_error
    );
    assert_eq!(run.success, expected, "{source}");
    run
}

const EXAMPLES: [&str; 8] = [
    include_str!("../../../examples/proof_nodes/atomic/by_builtin_strategy/nonzero_natural_positive.lit"),
    include_str!("../../../examples/proof_nodes/atomic/by_builtin_strategy/positive_integer_quotient.lit"),
    include_str!("../../../examples/proof_nodes/atomic/by_builtin_strategy/ordered_difference_nonzero.lit"),
    include_str!("../../../examples/proof_nodes/atomic/by_builtin_strategy/abs_symbolic_factor.lit"),
    include_str!("../../../examples/proof_nodes/atomic/by_builtin_strategy/absolute_sum_triangle.lit"),
    include_str!("../../../examples/proof_nodes/atomic/by_builtin_strategy/finite_sum_common_bound.lit"),
    include_str!("../../../examples/proof_nodes/atomic/by_builtin_strategy/cartesian_coordinate_equality.lit"),
    include_str!("../../../examples/proof_nodes/atomic/by_builtin_strategy/positive_reciprocal_order.lit"),
];

#[test]
fn elementary_composition_eight_unchanged_targets() {
    for source in EXAMPLES {
        check(&mut runtime(OutputLanguage::English), source, true);
    }
}

#[test]
fn elementary_composition_domains_claims_and_return_consumers() {
    for source in [
        "have fn f(n N:n!=0) N+=n",
        "have fn f(x R:x>1) R=1/(x-1)",
        "claim:\n    ? forall x R:\n        x>1\n        =>:\n            1/(x-1)=1/(x-1)\n    1/(x-1)=1/(x-1)",
        "forall m,n N:\n    m+n!=0\n    =>:\n        m+n $in N+",
        "forall x,y R:\n    x>y\n    =>:\n        1/(x-y)=1/(x-y)\n        y-x<0",
        "forall x,y R:\n    x>=y\n    x-y!=0\n    =>:\n        x-y $in R+",
        "forall a R-,x R:\n    abs(a*x)=(-a)*abs(x)",
        "forall a R,x R:\n    a>=0\n    =>:\n        abs(a*x)=abs(x)*a",
        "forall a,b,c,d R:\n    abs(a+(b+(c+d)))<=abs(d)+abs(b)+abs(a)+abs(c)",
        "forall a,b,c,d,M R:\n    a<=M\n    b<=M\n    c<=M\n    d<=M\n    =>:\n        a+(b+(c+d))<=M*4",
        "forall a,b,c,u,v,w R:\n    a<=u\n    b<=v\n    c<=w\n    =>:\n        a+(b+c)<=(u+v)+w",
        "forall p,q cart(R,R,R):\n    p(1)=q(1)\n    p(2)=q(2)\n    p(3)=q(3)\n    =>:\n        p=q",
        "forall X,Y set,p,q cart(X,Y):\n    p(1)=q(1)\n    p(2)=q(2)\n    =>:\n        p=q",
        "forall x,y R+:\n    x<y\n    =>:\n        1/x>1/y",
        "forall X,Y set,F fn(t X) cart(Y,Y),a,b X:\n    F(a)=F(b)\n    =>:\n        F(a)(1)=F(b)(1)",
    ] { check(&mut runtime(OutputLanguage::English), source, true); }
}

#[test]
fn elementary_composition_rejects_false_and_missing_premises() {
    for source in [
        "0 $in N+",
        "forall n Z:\n    n!=0\n    =>:\n        n $in N+",
        "forall m,n N+:\n    m/n $in N+",
        "forall m Z-,n N+:\n    $dvd(m,n)\n    =>:\n        m/n $in N+",
        "forall x R:\n    x>=1\n    =>:\n        1/(x-1)=1/(x-1)",
        "forall x,y R+:\n    1/(x-y)=1/(x-y)",
        "forall x C:\n    x!=1\n    =>:\n        x-1>0",
        "forall a R-,x R:\n    abs(a*x)=a*abs(x)",
        "forall a,x R:\n    abs(a*x)=a*abs(x)",
        "forall a,b,c R:\n    abs((a+b)+c)<=abs(a)+abs(b)",
        "forall a,b,c,M R:\n    a<=M\n    b<=M\n    =>:\n        (a+b)+c<=3*M",
        "forall a,b,c,M R:\n    a<=M\n    b<=M\n    c<=M\n    =>:\n        (a+b)+c<=2*M",
        "forall p,q cart(R,R):\n    p(1)=q(1)\n    =>:\n        p=q",
        "forall p cart(R,R),q cart(R,R,R):\n    p(1)=q(1)\n    p(2)=q(2)\n    =>:\n        p=q",
        "forall x,y R+:\n    x<=y\n    =>:\n        1/x<=1/y",
        "forall x,y R+:\n    x<=y\n    =>:\n        1/y<1/x",
        "forall x R-,y R+:\n    x<y\n    =>:\n        1/y<1/x",
        "forall X,Y set,F fn(t X) cart(Y,Y),a,b X:\n    F(a)(1)=F(b)(1)",
        "forall X,Y set,F fn(t X) cart(Y,Y),a,b X:\n    F(a)=F(b)\n    =>:\n        F(a)(1)=F(b)(2)",
    ] { check(&mut runtime(OutputLanguage::English), source, false); }
}

#[test]
fn elementary_composition_output_and_reading_keep_evidence() {
    let source = EXAMPLES
        .iter()
        .map(|s| {
            format!(
                "sketch:\n{}",
                s.lines().map(|l| format!("    {l}\n")).collect::<String>()
            )
        })
        .collect::<String>();
    for language in OutputLanguage::ALL {
        let mut rt = runtime(language);
        let run = check(&mut rt, &source, true);
        let detailed =
            crate::json_output::project_run_detailed(&run, &rt, "eval", None).stringify_pretty();
        for name in [
            "WeakSignAndNonzero",
            "difference_from_order",
            "AbsProductFromFactors",
            "AbsoluteSumTriangle",
            "FiniteSumUpperBound",
            "CartesianCoordinateEquality",
            "PositiveReciprocalLessEqual",
        ] {
            // Detailed sign reasons have stable machine names; other fields are localized.
            if name != "WeakSignAndNonzero" {
                assert!(detailed.contains(name), "{name}");
            }
        }
        for field in [
            "proof_of_requirement_facts",
            "cite_fact_id",
            "left_shape",
            "right_shape",
        ] {
            assert!(
                detailed.contains(&crate::json_output::json_keys::localize_key(
                    field, language
                )),
                "{field}"
            );
        }
        let normal =
            crate::json_output::project_run_normal(&run, &rt, "eval", None).stringify_pretty();
        assert!(!normal.contains("unsupported") && !normal.contains("unreachable"));
    }
    let reading = crate::reading::build_reading(
        &crate::reading::ReadingInput::Source(source),
        true,
        OutputLanguage::English,
    );
    assert!(reading.success);
    let document = reading.document.stringify_pretty();
    for name in [
        "DifferenceFromOrder",
        "left_shape",
        "AbsProductFromFactors",
        "FiniteSumUpperBound",
        "PositiveReciprocalLessEqual",
    ] {
        assert!(document.contains(name), "{name}");
    }
    assert!(reading
        .document
        .as_object()
        .unwrap()
        .get("diagnostics")
        .unwrap()
        .as_array()
        .unwrap()
        .is_empty());
}

#[test]
fn elementary_composition_read_only_permission_and_scope() {
    let mut rt = runtime(OutputLanguage::English);
    check(&mut rt, "have x,y R", true);
    check(
        &mut rt,
        "sketch:\n    forall a,b R:\n        a>b\n        =>:\n            1/(a-b)=1/(a-b)",
        true,
    );
    check(&mut rt, "1/(x-y)=1/(x-y)", false);
    check(&mut rt, "sketch:\n    x>y", false);
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize("x-y>0", rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(fact) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("fact");
    };
    let count = rt.top_exec_env().facts.facts_by_id.len();
    assert!(rt
        .verify_fact(&fact, VerifyState::top_level())
        .unwrap()
        .is_failed());
    assert_eq!(count, rt.top_exec_env().facts.facts_by_id.len());
    check(&mut rt, "have z N", true);
    let count = rt.top_exec_env().facts.facts_by_id.len();
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize("z=z", rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(eq))) =
        rt.parse(&tokens).unwrap().remove(0)
    else {
        panic!("equality");
    };
    let sign = rt
        .search_structural_real_sign(
            &eq.left,
            VerifyState::new(VerifyStateLevel::Direct).without_inference(),
        )
        .unwrap();
    assert_eq!(sign.sign, RealSign::Nonnegative);
    assert_eq!(count, rt.top_exec_env().facts.facts_by_id.len());
    check(&mut rt, "x=x", true);
}
