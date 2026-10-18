use crate::execute::execute_fact_stmt::VerifyStateLevel;
use crate::prelude::*;
use crate::tokenize::Tokenizer;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}
fn check(rt: &mut Runtime, code: &str, accepted: bool) -> crate::run::RunLitexCodeResult {
    let run = rt.run_litex_code(code).expect("public runtime");
    assert!(run.session_error.is_none(), "hard error: {code}");
    assert_eq!(run.success, accepted, "{code}");
    run
}

#[test]
fn native_latex_operations_durable_examples() {
    for path in [
        "complex_conjugation",
        "reciprocal_trigonometry",
        "hyperbolic_functions",
        "symmetric_difference",
    ] {
        let file = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("examples/proof_nodes/equal/by_builtin_rule")
            .join(format!("{path}.lit"));
        check(
            &mut runtime(),
            &std::fs::read_to_string(file).unwrap(),
            true,
        );
    }
}

#[test]
fn native_latex_operations_domains_and_false_neighbors() {
    for code in [
        "conj(i)=i",
        "conj({1})=1",
        "conj(1/0)=0",
        "0*conj(1/0)=0",
        "forall z C:\n    conj(z)=z",
        "forall z,w C:\n    conj(z+w)=conj(z)-conj(w)",
        "forall z,w C:\n    conj(z/w)=conj(z)/conj(w)",
        "sec(pi/2)=0",
        "csc(0)=0",
        "0*csc(0)=0",
        "sec(i)=1",
        "csc(-pi/2)=csc(pi/2)",
        "forall x R:\n    sec(x)*cos(x)=1",
        "forall x R:\n    csc(x)*sin(x)=1",
        "sinh(i)=i",
        "cosh(i)=1",
        "tanh(i)=i",
        "sech(i)=1",
        "coth(0)=0",
        "csch(0)=0",
        "coth(i)=coth(i)",
        "csch(i)=csch(i)",
        "0*coth(0)=0",
        "cosh(0)=0",
        "sinh(0)=1",
        "tanh(0)=1",
        "sech(0)=0",
        "forall x R:\n    coth(x)*sinh(x)=cosh(x)",
        "forall x R:\n    cosh(x)^2+sinh(x)^2=1",
        "forall x,y R:\n    sinh(x+y)=sinh(x)+sinh(y)",
        "forall x R:\n    sinh(-x)=sinh(x)",
        "sym_diff({1},{1})={1}",
        "sym_diff({1,2},{2,3})={1,2,3}",
        "2 $in sym_diff({1,2},{2,3})",
        "not 1 $in sym_diff({1,2},{2,3})",
        "forall A,B set:\n    sym_diff(A,B)=union(A,B)",
    ] {
        check(&mut runtime(), code, false);
    }
}

#[test]
fn native_latex_operations_failure_keeps_prior_context() {
    let mut rt = runtime();
    check(&mut rt, "have a R = 2", true);
    check(&mut rt, "csch(0)=0", false);
    check(&mut rt, "cosh(0)=0", false);
    check(&mut rt, "cosh(0)=1", true);
    check(&mut rt, "conj(a)=2", true);
    check(&mut rt, "forall x R*:\n    -x != 0", true);
    check(
        &mut rt,
        "forall x R:\n    x!=0\n    =>:\n        coth(x)=cosh(x)/sinh(x)",
        true,
    );
}

#[test]
fn native_latex_operations_substitution_congruence_and_carriers() {
    for code in [
        "have fn f(x R) R = cosh(x)\nf(0)=1",
        "have fn f(z C) C = conj(z)\nf(i)=-i",
        "forall x,y R:\n    x=y\n    =>:\n        sinh(x)=sinh(y)",
        "forall A,B,D set:\n    A=B\n    =>:\n        sym_diff(A,D)=sym_diff(B,D)",
        "forall x R:\n    sinh(x) $in R\n    cosh(x) $in R+\n    tanh(x) $in R\n    sech(x) $in R+",
        "forall x R*:\n    coth(x) $in R*\n    csch(x) $in R*",
        "forall z C:\n    conj(z) $in C",
        "sym_diff({1,2},{2,3})={3,1}",
        "sym_diff({1/2,2},{0.5,3})={2,3}",
        "forall x R:\n    cos(x)!=0\n    =>:\n        sec(x) $in R*",
        "forall x R:\n    sin(x)!=0\n    =>:\n        csc(x) $in R*",
        "forall x R:\n    tanh(x)*cosh(x)=sinh(x)\n    sech(x)*cosh(x)=1",
        "forall x R*:\n    coth(x)*sinh(x)=cosh(x)\n    csch(x)*sinh(x)=1\n    coth(x)=cosh(x)*csch(x)",
        "forall x R:\n    cos(x)!=0\n    =>:\n        csc(pi/2-x)=sec(x)",
    ] {check(&mut runtime(),code,true);}
}

#[test]
fn native_latex_operations_reserved_names_and_arity() {
    for name in [
        "conj", "sec", "csc", "sinh", "cosh", "tanh", "coth", "sech", "csch", "sym_diff",
    ] {
        let mut rt = runtime();
        let tokens = Tokenizer::new()
            .tokenize(&format!("have {name} R = 1"), rt.current_file.clone())
            .unwrap();
        assert!(rt.parse(&tokens).is_err(), "reserved {name}");
        let tokens = Tokenizer::new()
            .tokenize(
                &format!("forall {name} R:\n    {name}={name}"),
                rt.current_file.clone(),
            )
            .unwrap();
        assert!(rt.parse(&tokens).is_err(), "reserved binder {name}");
    }
    for code in [
        "conj(1,2)=1",
        "sec()=1",
        "sinh(0,0)=0",
        "sym_diff({})={}",
        "sym_diff({},{},{})={}",
    ] {
        let mut rt = runtime();
        let tokens = Tokenizer::new()
            .tokenize(code, rt.current_file.clone())
            .unwrap();
        assert!(rt.parse(&tokens).is_err(), "arity: {code}");
    }
}

#[test]
fn native_latex_operations_typed_evidence_and_search_ceiling() {
    for (source, rule) in [
        ("forall z C:\n    conj(conj(z))=z", "ConjugateInvolution"),
        (
            "forall x R:\n    cosh(x)^2-sinh(x)^2=1",
            "HyperbolicPythagorean",
        ),
        ("forall A set:\n    sym_diff(A,A)={}", "SymDiffSelf"),
    ] {
        let mut rt = runtime();
        let tokens = Tokenizer::new()
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
        let run = check(&mut rt, source, true);
        let json = crate::json_output::project_run_detailed(&run, &rt, "eval", None);
        assert!(format!("{json:?}").contains(rule), "missing {rule}");
    }
}

#[test]
fn native_latex_operations_latex_projection_and_lean_fail_closed() {
    let latex=crate::compile_to_latex::to_latex_from_source(
        "conj(i)=-i\nsec(0)=1\ncsc(pi/2)=1\nsinh(0)=0\ncosh(0)=1\ntanh(0)=0\ncoth(1)=coth(1)\nsech(0)=1\ncsch(1)=csch(1)\nsym_diff({1},{2})={1,2}",
        OutputLanguage::English).unwrap();
    for fragment in [
        "\\overline",
        "\\operatorname{sec}",
        "\\operatorname{csc}",
        "\\operatorname{sinh}",
        "\\operatorname{cosh}",
        "\\operatorname{tanh}",
        "\\operatorname{coth}",
        "\\operatorname{sech}",
        "\\operatorname{csch}",
        "\\triangle",
    ] {
        assert!(latex.contains(fragment), "{fragment}: {latex}");
    }
    // A verified native theorem must not acquire an invented Lean proof.
    let command = crate::launch_command::parse_launch_command(&[
        "-lean".into(),
        "-f".into(),
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("examples/proof_nodes/equal/by_builtin_rule/complex_conjugation.lit")
            .to_string_lossy()
            .into_owned(),
    ])
    .unwrap();
    let error = crate::run::run_command(command)
        .err()
        .expect("unsupported native Lean replay");
    assert!(error.to_string().contains("WD/ComplexOperator"), "{error}");
}
