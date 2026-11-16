use crate::prelude::*;

fn check(rt: &mut Runtime, source: &str, expected: bool) {
    let result = rt.run_litex_code(source).unwrap();
    assert_eq!(
        result.success,
        expected,
        "{source}\n{}",
        crate::json_output::emit_run_detailed(&result, rt, "improper", None)
    );
    assert!(result.session_error.is_none());
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

#[test]
fn improper_polynomial_tracer() {
    let mut rt = runtime();
    check(&mut rt, "integ_oc(x,0,1,x^2)=1/3", true);
    check(&mut rt, "integ_co(x,0,1,x^2)=1/3", true);
    check(&mut rt, "integ_oo(x,0,1,x^2)=1/3", true);
    check(&mut rt, "integ_oc(x,1,0,x^2)=-1/3", true);
    check(&mut rt, "integ_co(x,1,0,x^2)=-1/3", true);
    check(&mut rt, "integ_oo(x,1,0,x^2)=-1/3", true);
}

#[test]
fn improper_singular_tracer_and_controls() {
    let mut rt = runtime();
    check(&mut rt, "integ_oc(x,0,1,1/sqrt(x))=2", true);
    check(&mut rt, "integ_pos_inf(x,1,1/x^2)=1", true);
    check(&mut rt, "integ_neg_inf(x,-1,1/x^2)=1", true);
    check(&mut rt, "integ_oc(x,0,1,1/x)=0", false);
    check(&mut rt, "integ_oc(x,0,0,1)=0", false);
    check(&mut rt, "integ(x,0,0,1)=0", true);
    check(&mut rt, "integ(x,1,1,1/x)=0", true);
    check(&mut rt, "integ(x,0,0,1/x)=0", false);
}

#[test]
fn improper_candidate_laws_keep_all_premises() {
    let mut rt = runtime();
    check(
        &mut rt,
        r#"have fn square(x R) R=x^2
$has_integ_oc(square,0,1,1/3)
release thm integral_open_closed_selected(square,0,1)
release thm integral_open_closed_unique(square,0,1,1/3,1/3)
release thm integral_open_closed_reverse(square,0,1,1/3)
integral_closed_open(square,1,0)=-1/3
have fn total(x R) R=x^2+x^2
have fn scaled(x R) R=2*x^2
forall x R:
    total(x)=square(x)+square(x)
    scaled(x)=2*square(x)
release thm integral_open_closed_add(square,square,total,0,1,1/3,1/3)
release thm integral_open_closed_scale(square,scaled,0,1,2,1/3)
release thm integral_open_closed_congr(square,fn(x R) R {x*x},0,1,1/3)
"#,
        true,
    );
    check(
        &mut rt,
        "release thm integral_open_closed_unique(square,0,1,1/3,7)",
        false,
    );
    check(
        &mut rt,
        "release thm integral_open_closed_add(square,square,fn(x R) R {x^2},0,1,1/3,1/3)",
        false,
    );
    check(&mut rt, "integral_closed_open(square,1,0)=-1/3", true);
}

#[test]
fn improper_declared_function_candidate_selects_value() {
    let mut rt = runtime();
    check(
        &mut rt,
        r#"thm candidate_value:
    ? forall f fn(x R) R:
        $has_integ_oc(f,0,1,2)
        =>:
            integral_open_closed(f,0,1)=2
"#,
        true,
    );
}

#[test]
fn improper_negative_domain_components() {
    let mut rt = runtime();
    check(&mut rt, "forall x '(,-1]:\n    x $in R-\n", true);
    check(
        &mut rt,
        "forall u,v '(,-1]:\n    min(u,v) $in R-\n    max(u,v) $in R-\n",
        true,
    );
    check(
        &mut rt,
        "forall u,v '(,-1]:\n    integral(fn(x '(,-1]) R {1/x^2},u,v)=(1/u-1/v)\n",
        true,
    );
    check(
        &mut rt,
        "forall u,v '(,-1]:\n    $integrable(fn(x '(,-1]) R {1/x^2},u,v)\n",
        true,
    );
}

#[test]
fn improper_expression_scopes_and_invalid_domains() {
    let mut rt = runtime();
    check(&mut rt, "have x R=2", true);
    check(&mut rt, "integ(x,x,3,x^2)=(3^3-x^3)/3", true);
    check(&mut rt, "x=2", true);
    check(&mut rt, "integ_oc(t,0,1,1/t)=0", false);
    check(&mut rt, "integ_oo(t,-1,1,1/t)=0", false);
    check(&mut rt, "integ_pos_inf(t,1,1)=0", false);
    check(&mut rt, "integ_co(t,0,1,1/(1-t))=0", false);
    check(&mut rt, "integ_oc(t,0,1,1/sqrt(t))=3", false);
    check(&mut rt, "integ(t,0,1,1/sqrt(t))=2", false);
    check(&mut rt, "integ_oc(t,0,i,t)=0", false);
    check(&mut rt, "integ(t,2,0,4*t^2)=-32/3", true);
}

#[test]
fn improper_generic_laws_for_every_shape() {
    for (canonical, short, endpoints) in [
        ("integral_open_closed", "oc", "0,1"),
        ("integral_closed_open", "co", "0,1"),
        ("integral_open", "oo", "0,1"),
        ("integral_pos_inf", "pos_inf", "0"),
        ("integral_neg_inf", "neg_inf", "0"),
    ] {
        let mut rt = runtime();
        let source = format!(
            r#"thm laws:
    ? forall f,g,h fn(x R) R,I,J,c R:
        $has_integ_{short}(f,{endpoints},I)
        $has_integ_{short}(g,{endpoints},J)
        forall x R:
            h(x)=f(x)+g(x)
        =>:
            $has_integ_{short}(h,{endpoints},I+J)
    release thm {canonical}_add(f,g,h,{endpoints},I,J)
"#
        );
        check(&mut rt, &source, true);
        let source = format!(
            r#"thm selected:
    ? forall f fn(x R) R,I R:
        $has_integ_{short}(f,{endpoints},I)
        =>:
            {canonical}(f,{endpoints})=I
"#
        );
        check(&mut rt, &source, true);
        let source = format!(
            r#"thm scale:
    ? forall f,h fn(x R) R,I,c R:
        $has_integ_{short}(f,{endpoints},I)
        forall x R:
            h(x)=c*f(x)
        =>:
            $has_integ_{short}(h,{endpoints},c*I)
    release thm {canonical}_scale(f,h,{endpoints},c,I)
thm congruent:
    ? forall f,g fn(x R) R,I R:
        $has_integ_{short}(f,{endpoints},I)
        forall x R:
            g(x)=f(x)
        =>:
            $has_integ_{short}(g,{endpoints},I)
    release thm {canonical}_congr(f,g,{endpoints},I)
thm unique:
    ? forall f fn(x R) R,I,J R:
        $has_integ_{short}(f,{endpoints},I)
        $has_integ_{short}(f,{endpoints},J)
        =>:
            I=J
    release thm {canonical}_unique(f,{endpoints},I,J)
"#
        );
        check(&mut rt, &source, true);
    }
}

#[test]
fn improper_definition_round_trip_for_every_shape() {
    for (canonical, bounds, body, value) in [
        ("integral_open_closed", "0,1", "t^2", "1/3"),
        ("integral_closed_open", "0,1", "t^2", "1/3"),
        ("integral_open", "0,1", "t^2", "1/3"),
        ("integral_pos_inf", "1", "1/t^2", "1"),
        ("integral_neg_inf", "-1", "1/t^2", "1"),
    ] {
        let mut rt = runtime();
        let function = if canonical.ends_with("neg_inf") {
            format!("fn(t '(,-1]) R {{{body}}}")
        } else if canonical.ends_with("pos_inf") {
            format!("fn(t '[1,)) R {{{body}}}")
        } else {
            format!("fn(t R) R {{{body}}}")
        };
        check(
            &mut rt,
            &format!("{canonical}({function},{bounds})={value}"),
            true,
        );
        check(
            &mut rt,
            &format!("release thm {canonical}_to_definition({function},{bounds},{value})"),
            true,
        );
        check(
            &mut rt,
            &format!("release thm {canonical}_from_definition({function},{bounds},{value})"),
            true,
        );
    }
}

#[test]
fn improper_symbolic_endpoint_contract() {
    let mut rt = runtime();
    check(
        &mut rt,
        r#"thm generic_value:
    ? forall f fn(t R) R,a,b,I R:
        a!=b
        $has_integ_oc(f,a,b,I)
        =>:
            integral_open_closed(f,a,b)=I
"#,
        true,
    );
    for short in ["oc", "co", "oo"] {
        check(
            &mut rt,
            &format!(
                "forall a,b R:\n    a!=b\n    =>:\n        integ_{short}(t,a,b,t^2)=(b^3-a^3)/3\n"
            ),
            true,
        );
    }
}
