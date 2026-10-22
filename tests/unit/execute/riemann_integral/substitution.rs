use crate::prelude::*;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}
fn run(rt: &mut Runtime, source: &str, expected: bool) -> crate::run::RunLitexCodeResult {
    let result = rt.run_litex_code(source).unwrap();
    assert!(result.session_error.is_none(), "{source}");
    assert_eq!(
        result.success,
        expected,
        "{source}\n{}",
        crate::json_output::project_run_detailed(&result, rt, "substitution", None).stringify()
    );
    result
}

#[test]
fn calculus_substitution_whole_image_and_failed_candidate_are_checked() {
    let mut rt = runtime();
    run(&mut rt, SQUARE_SETUP, true);
    run(&mut rt,"have fn one(x R) R=1\nrelease thm riemann_integral_zero(one,1)\nsquare(-1)=1\nsquare(1)=1\nsquare(0)=0\nnot square(0) $in '[1,1]",true);
    // Both endpoints lie in [1,1], but the middle of the path does not.
    run(
        &mut rt,
        "release thm riemann_integral_substitution(one,square,twice,twice,'[1,1],-1,1,0)",
        false,
    );
    let failed = run(&mut rt, "integral(twice,-1,1)=0", false);
    assert!(
        crate::json_output::project_run_normal(&failed, &rt, "substitution", None)
            .stringify()
            .contains("well_defined")
    );
    // The same nonmonotone map is legitimate with full image coverage.
    run(
        &mut rt,
        "release thm riemann_integral_substitution(one,square,twice,twice,R,-1,1,0)",
        true,
    );
    run(&mut rt, "integral(twice,-1,1)=0", true);
}

#[test]
fn calculus_substitution_chain_provenance_and_lean_boundary() {
    let mut rt = runtime();
    let source="thm chain_relation:\n    ? forall F,f,g,dg,H,h fn(x R) R:\n        $is_antiderivative_on(F,f,R)\n        forall x R:\n            $has_derivative_at(g,x,dg(x))\n        forall x R:\n            H(x)=F(g(x))\n            h(x)=f(g(x))*dg(x)\n        =>:\n            $is_antiderivative_on(H,h,R)\n    release thm antiderivative_compose(F,f,g,dg,H,h,R,R)";
    let result = run(&mut rt, source, true);
    let json =
        crate::json_output::project_run_detailed(&result, &rt, "substitution", None).stringify();
    assert!(json.contains("antiderivative_compose"));
    assert!(json.contains("is_antiderivative_on"));
    assert!(crate::compile_to_lean::LitexToLeanCompiler::new(rt)
        .compile_run(&result, "chain_relation_boundary")
        .is_err());
}

#[test]
fn calculus_substitution_outer_domain_is_the_image_region() {
    let mut rt = runtime();
    run(
        &mut rt,
        "have fn local_identity(t '[4,5]) R=t\nhave fn shifted(x R) R=x+4\nhave fn one(x R) R=1",
        true,
    );
    run(&mut rt,"claim:\n    ? forall x R:\n        $has_derivative_at(shifted,x,one(x))\n    one(x)=1\n    $has_derivative_at(shifted,x,1)\n    $has_derivative_at(shifted,x,one(x))",true);
    run(&mut rt,"forall x '[0,1]:\n    x<=1\n    x+4<=1+4\n    1+4=5\n    x+4<=5\n    shifted(x)=x+4\n    shifted(x)>=4\n    shifted(x)<=5\n    shifted(x) $in '[4,5]",true);
    run(
        &mut rt,
        "release thm riemann_integral_power(local_identity,4,5,1)\nshifted(0)=4\nshifted(1)=5",
        true,
    );
    run(&mut rt,"claim:\n    ? forall x '[0,1]:\n        shifted(x)=local_identity(shifted(x))*one(x)\n    shifted(x) $in '[4,5]\n    one(x)=1\n    local_identity(shifted(x))=shifted(x)\n    local_identity(shifted(x))*one(x)=shifted(x)",true);
    // The outer function is undefined on [0,1] and perfectly valid on [4,5].
    run(&mut rt,"release thm riemann_integral_substitution(local_identity,shifted,one,shifted,'[4,5],0,1,(5^(1+1)-4^(1+1))/(1+1))",true);
    run(&mut rt, "integral(shifted,0,1)=9/2", true);
}

const SQUARE_SETUP: &str = r#"
have fn identity(x R) R=x
have fn square(x R) R=x^2
have fn twice(x R) R=2*x
claim:
    ? forall x R:
        $has_derivative_at(square,x,twice(x))
    release thm fn_derivative_at_real_interior(x)
    release thm fn_derivative_at_identity(identity,x)
    release thm fn_derivative_at_multiply(identity,identity,square,x,1,1)
    identity(x)=x
    twice(x)=2*x
    1*identity(x)+identity(x)*1=twice(x)
    $has_derivative_at(square,x,twice(x))
"#;
