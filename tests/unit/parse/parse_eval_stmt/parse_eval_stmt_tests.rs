use crate::parse::Tokenizer;
use crate::prelude::*;
use std::rc::Rc;

#[test]
fn eval_rejects_trailing_tokens() {
    let mut runtime = Runtime::new();
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks("eval a extra", Rc::from("parse_eval_trailing_tokens.lit"))
        .expect("tokenize eval statement");

    let error = runtime.parse_eval_stmt(&mut blocks[0]).unwrap_err();
    let RuntimeError::ParseError(parse_error) = error else {
        panic!("expected parse error");
    };
    assert_eq!(parse_error.msg, "eval: expected one expression");
}
