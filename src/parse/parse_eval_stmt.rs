use crate::prelude::*;

impl Runtime {
    pub fn parse_eval_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(EVAL)?;
        let obj_to_eval = self.parse_obj(tb)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "eval: expected one expression".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(EvalStmt::new(obj_to_eval, tb.line_file.clone()).into())
    }
}

#[cfg(test)]
mod parse_eval_stmt_tests {
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
}
