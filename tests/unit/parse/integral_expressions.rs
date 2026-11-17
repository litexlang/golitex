use crate::prelude::*;

fn parsed(source: &str) -> Result<Vec<Stmt>, RuntimeError> {
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let tokens = crate::tokenize::Tokenizer::new().tokenize(source, rt.current_file.clone())?;
    rt.parse(&tokens)
}

#[test]
fn integral_expression_parser_preserves_fixed_arity_and_canonical_name() {
    for (source, expected) in [
        ("eval integ(x,0,2,x^2)", "integral("),
        ("eval integ_oc(x,0,1,x^2)", "integral_open_closed("),
        ("eval integ_co(x,0,1,x^2)", "integral_closed_open("),
        ("eval integ_oo(x,0,1,x^2)", "integral_open("),
        ("eval integ_pos_inf(x,1,1/x^2)", "integral_pos_inf("),
        ("eval integ_neg_inf(x,-1,1/x^2)", "integral_neg_inf("),
    ] {
        let result = parsed(source).unwrap();
        assert!(result[0].readable_string().contains(expected), "{source}");
    }
    for source in [
        "eval integ(f,0,1)",
        "eval integ(x,0,1)",
        "eval integ_oc(x,0,1)",
        "eval integ_pos_inf(x,0,1,x)",
        "eval integral_open_closed(1,2)",
        "eval integ(x,0,1,x)\neval x",
    ] {
        assert!(parsed(source).is_err(), "{source}");
    }
}

#[test]
fn integral_expression_parser_resolves_endpoints_before_introducing_variable() {
    assert!(parsed("eval integ(x,x,1,x^2)").is_err());
    assert!(parsed("have a R\neval integ(x,a,2,x^2+a)").is_ok());
    assert!(parsed("have x R\neval integ(x,x,2,x^2)").is_ok());
    assert!(parsed("eval integ(x,0,1,integ(y,0,x,x+y))").is_ok());
}
