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
        crate::json_output::project_run_detailed(&result, rt, "antiderivative", None).stringify()
    );
    result
}

#[test]
fn antiderivative_parts_relation_wd_requires_both_real_domains_and_open_region() {
    let mut rt = runtime();
    run(&mut rt,"have fn identity(x R) R=x\nhave fn one(x R) R=1\nhave fn rational_one(x R) Q=1\nhave fn missing(x R*) R=1\nhave fn complex_one(x R) C=1\nhave fn binary(x,y R) R=x+y",true);
    for (source, expected) in [
        ("$is_antiderivative_on(identity,one,R)", true),
        ("$is_antiderivative_on(identity,rational_one,'(0,1))", true),
        ("not $is_antiderivative_on(identity,one,R)", true),
        ("$is_antiderivative_on(identity,missing,R)", false),
        ("$is_antiderivative_on(identity,complex_one,R)", false),
        ("$is_antiderivative_on(binary,one,R)", false),
        ("$is_antiderivative_on(1,one,R)", false),
        ("$is_antiderivative_on(identity,one,{0})", false),
        ("$is_antiderivative_on(identity,one,'[0,1])", false),
        ("$is_antiderivative_on(identity,one,'(1,1))", false),
    ] {
        let tokens = crate::tokenize::Tokenizer::new()
            .tokenize(source, rt.current_file.clone())
            .unwrap();
        let Stmt::Fact(Fact::AtomicFact(fact)) = rt.parse(&tokens).unwrap().remove(0) else {
            panic!("atomic relation")
        };
        let wd = rt
            .verify_atomic_fact_well_definedness(&fact, VerifyState::top_level())
            .unwrap();
        assert_eq!(!wd.is_failed(), expected, "{source}");
    }
    // A signature and legal domain do not establish the relation's truth.
    run(&mut rt, "$is_antiderivative_on(identity,one,R)", false);
    run(
        &mut rt,
        "prop is_antiderivative_on(F,f,I set):\n    I=I",
        false,
    );
    run(&mut rt, "$is_antiderivative_on(identity,one)", false);
    run(&mut rt, "1+1=2", true);
}

#[test]
fn antiderivative_parts_explicit_projection_preserves_provenance_and_lean_boundary() {
    let mut rt = runtime();
    let source="thm antiderivative_elimination:\n    ? forall F,f fn(x R) R:\n        $is_antiderivative_on(F,f,R)\n        =>:\n            $has_derivative_at(F,0,f(0))\n    release thm antiderivative_to_definition(F,f,R)";
    let result = run(&mut rt, source, true);
    let json =
        crate::json_output::project_run_detailed(&result, &rt, "antiderivative", None).stringify();
    assert!(json.contains("antiderivative_to_definition"));
    assert!(json.contains("has_derivative_at"));
    assert!(crate::compile_to_lean::LitexToLeanCompiler::new(rt)
        .compile_run(&result, "antiderivative_boundary")
        .is_err());
}

#[test]
fn antiderivative_parts_failed_product_does_not_publish_an_integral() {
    let mut rt = runtime();
    run(&mut rt, PARTS_SETUP, true);
    run(&mut rt, "have fn bad(x R) R=0", true);
    run(
        &mut rt,
        "release thm riemann_integral_by_parts(identity,one,ex,ex,bad,ex,0,1,ex(1)-ex(0))",
        false,
    );
    let rejected = run(&mut rt, "integral(bad,0,1)=0", false);
    let json =
        crate::json_output::project_run_normal(&rejected, &rt, "antiderivative", None).stringify();
    assert!(json.contains("well_defined"));
    run(
        &mut rt,
        "release thm riemann_integral_by_parts(identity,one,ex,ex,weighted_exp,ex,0,1,ex(1)-ex(0))",
        true,
    );
    run(
        &mut rt,
        "integral(weighted_exp,0,1)=integral(weighted_exp,0,1)",
        true,
    );
}

const PARTS_SETUP: &str = r#"
have fn identity(x R) R=x
have fn one(x R) R=1
have fn ex(x R) R=exp(x)
have fn weighted_exp(x R) R=x*exp(x)
claim:
    ? forall x R:
        $has_derivative_at(identity,x,one(x))
        $has_derivative_at(ex,x,ex(x))
    release thm fn_derivative_at_real_interior(x)
    release thm fn_derivative_at_identity(identity,x)
    release thm fn_derivative_at_exp(ex,x)
    one(x)=1
    ex(x)=exp(x)
    $has_derivative_at(identity,x,one(x))
    $has_derivative_at(ex,x,ex(x))
release thm riemann_integrable_continuous(ex,0,1)
release thm riemann_integral_newton_leibniz(ex,ex,0,1)
"#;
