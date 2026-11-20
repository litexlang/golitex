use crate::prelude::*;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

fn parsed(source: &str) -> RuntimeResult<Vec<Stmt>> {
    let mut rt = runtime();
    let tokens = crate::tokenize::Tokenizer::new().tokenize(source, rt.current_file.clone())?;
    rt.parse(&tokens)
}

#[test]
fn run_examples_bound_expressions() {
    let run = runtime()
        .run_litex_code(include_str!("../../../examples/wd/bound_expressions.lit"))
        .unwrap();
    assert!(run.success, "{:?}", run.normal_json);
    assert!(run.input_error.is_none());
    assert!(run.session_error.is_none());
}

#[test]
fn bound_expressions_keep_canonical_well_definedness_requirements() {
    for source in [
        "let value = sum_of(k,3,1,7)",
        "let value = prod_of(k,3,1,7)",
        "let value = set_sum_of(x,R,x)",
        "let value = set_prod_of(k,{1},i*k)",
        "let value = lim_of(n,n/(n+1))",
        "let value = fn_lim_of(x,{0},0,x)",
    ] {
        let run = runtime().run_litex_code(source).unwrap();
        assert!(!run.success, "{source}");
        assert!(run.input_error.is_none(), "{:?}", run.normal_json);
        assert!(run.session_error.is_none(), "{:?}", run.normal_json);
    }
}

#[test]
fn bound_expressions_match_their_expanded_ast() {
    for (short, expanded) in [
        ("sum_of(k,1,3,k^2)", "sum(1,3,fn(k 1...3) R {k^2})"),
        ("prod_of(k,1,4,k)", "product(1,4,fn(k 1...4) R {k})"),
        (
            "set_sum_of(k,{1,3,5},k^2)",
            "finite_set_sum({1,3,5},fn(k {1,3,5}) R {k^2})",
        ),
        (
            "set_prod_of(k,{2,3,5},k)",
            "finite_set_product({2,3,5},fn(k {2,3,5}) R {k})",
        ),
        ("lim_of(n,1/n)", "lim(fn(n N+) R {1/n})"),
        (
            "fn_lim_of(x,set_minus(R,{0}),0,x^2/x)",
            "fn_lim(fn(x set_minus(R,{0})) R {x^2/x},0)",
        ),
        (
            "sum_of(k,1,3,set_sum_of(j,{k},j+k))",
            "sum(1,3,fn(k 1...3) R {finite_set_sum({k},fn(j {k}) R {j+k})})",
        ),
    ] {
        assert_eq!(
            parsed(&format!("eval {short}")).unwrap(),
            parsed(&format!("eval {expanded}")).unwrap(),
            "{short}"
        );
    }
}

#[test]
fn bound_expressions_enforce_fixed_arity_and_ordinary_function_scope() {
    for (source, message) in [
        ("eval sum_of(k,1,3)", "expected `sum_of(k, a, b, E)`"),
        ("eval prod_of(k,1,3,k,4)", "expected `prod_of(k, a, b, E)`"),
        ("eval set_sum_of(k,{1})", "expected `set_sum_of(k, S, E)`"),
        (
            "eval set_prod_of(1,{1},1)",
            "expects a bound variable first",
        ),
        ("eval lim_of(n,1,2)", "expected `lim_of(n, E)`"),
        (
            "eval fn_lim_of(x,R,0,)",
            "expected `fn_lim_of(x, D, x0, E)`",
        ),
        ("eval sum_of(k,k,3,k)", "undefined name `k`"),
        ("eval set_sum_of(k,{k},k)", "undefined name `k`"),
        ("eval fn_lim_of(x,R,x,x)", "undefined name `x`"),
        ("eval lim_of(n,n)\neval n", "undefined name `n`"),
        (
            "have k Z = 2\neval set_sum_of(k,{k},k^2)",
            "name `k` is already bound in an enclosing parse scope",
        ),
    ] {
        let error = parsed(source).unwrap_err();
        assert!(error.to_string().contains(message), "{source}: {error:?}");
    }

    for name in [
        "sum_of",
        "prod_of",
        "set_sum_of",
        "set_prod_of",
        "lim_of",
        "fn_lim_of",
    ] {
        let error = parsed(&format!("have {name} R")).unwrap_err();
        assert!(error.to_string().contains("reserved builtin name"));
    }
}
