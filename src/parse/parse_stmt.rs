use crate::prelude::*;

impl Runtime {
    pub fn parse_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        match tb.current()? {
            ALIAS => self.parse_alias_stmt(tb),
            PROP => self.parse_def_prop_stmt(tb),
            ABSTRACT_PROP => self.parse_def_abstract_prop_stmt(tb),
            HAVE => match tb.token_at_add_index(1) {
                ALGO => match tb.token_at_add_index(2) {
                    FOR => self.parse_have_algo_for_stmt(tb),
                    _ => Err(parse_stmt_error(tb, "have algo: expected `for f(...)`")),
                },
                TUPLE => self.parse_have_tuple_stmt(tb),
                CART => self.parse_have_cart_stmt(tb),
                SEQ => self.parse_have_seq_stmt(tb),
                FINITE_SEQ => self.parse_have_finite_seq_stmt(tb),
                MATRIX => self.parse_have_matrix_stmt(tb),
                FN_LOWER_CASE => self.parse_have_fn_stmt(tb),
                BY => match tb.token_at_add_index(2) {
                    PREIMAGE => self.parse_have_preimage(tb),
                    _ => Err(parse_stmt_error(tb, "have by: expected `preimage`")),
                },
                "" => Err(parse_stmt_error(
                    tb,
                    "have: expected object definition, `fn`, or `by preimage`",
                )),
                _ => self.parse_have_obj_stmt(tb),
            },
            OBTAIN => self.parse_obtain_exist_stmt(tb),
            CLEAR => self.parse_clear_stmt(tb),
            CLAIM => self.parse_claim_stmt(tb),
            THM => self.parse_def_thm_stmt(tb),
            AXIOM => self.parse_def_axiom_stmt(tb),
            STRATEGY => self.parse_def_strategy_stmt(tb),
            USE => self.parse_use_strategy_stmt(tb),
            STOP => match tb.token_at_add_index(1) {
                STRATEGY => self.parse_stop_strategy_stmt(tb),
                _ => Err(parse_stmt_error(tb, "stop: expected `strategy`")),
            },
            SKETCH => self.parse_sketch_stmt(tb),
            TRY => self.parse_try_stmt(tb),
            QUESTION_GOAL => Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "top-level `?` is not supported; use it as a goal block inside claim/thm/by/strategy statements".to_string(),
                    tb.line_file.clone(),
                ),
            ))),
            TRUST => self.parse_trust_stmt(tb),
            IMPORT => self.parse_import_stmt(tb),
            LOCAL => Err(parse_stmt_error(
                tb,
                "local import has been removed; place the referenced source earlier in litex.config [export] and use its canonical name",
            )),
            DO_NOTHING => self.parse_do_nothing_stmt(tb),
            EVAL => self.parse_eval_stmt(tb),
            WITNESS => self.parse_witness_stmt(tb),
            STRUCT => self.parse_def_struct_stmt(tb),
            TEMPLATE => self.parse_def_template_stmt(tb),
            ALGO => Err(parse_stmt_error(
                tb,
                "algorithm implementations must use `have algo for f(...)`",
            )),
            STRONG_INDUC => Err(parse_stmt_error(
                tb,
                "strong_induc is only valid after `by`",
            )),
            BY => self.parse_by_prefixed_stmt(tb),
            _ => {
                let fact = self.parse_fact(tb)?;
                Ok(fact.into())
            }
        }
    }
}

fn parse_stmt_error(tb: &TokenBlock, msg: &str) -> RuntimeError {
    RuntimeError::from(ParseRuntimeError(
        RuntimeErrorStruct::new_with_msg_and_line_file(msg.to_string(), tb.line_file.clone()),
    ))
}

#[cfg(test)]
mod parse_stmt_diagnostic_tests {
    use crate::parse::Tokenizer;
    use crate::prelude::*;
    use std::rc::Rc;

    fn parse_one_stmt_error_message(source_code: &str) -> String {
        let mut runtime = Runtime::new();
        let mut tokenizer = Tokenizer::new();
        let mut blocks = tokenizer
            .parse_blocks(source_code, Rc::from("parse_stmt_diagnostic_test.lit"))
            .expect("tokenize statement");
        assert_eq!(blocks.len(), 1, "{source_code:?}");
        let err = runtime.parse_stmt(&mut blocks[0]).unwrap_err();
        let RuntimeError::ParseError(parse_error) = err else {
            panic!("expected parse error, got {err:?}");
        };
        parse_error.msg
    }

    fn parse_one_stmt(source_code: &str) -> Result<Stmt, RuntimeError> {
        let mut runtime = Runtime::new();
        let mut tokenizer = Tokenizer::new();
        let mut blocks = tokenizer
            .parse_blocks(source_code, Rc::from("parse_stmt_diagnostic_test.lit"))
            .expect("tokenize statement");
        assert_eq!(blocks.len(), 1, "{source_code:?}");
        runtime.parse_stmt(&mut blocks[0])
    }

    #[test]
    fn incomplete_have_and_stop_dispatch_report_syntax_errors() {
        let cases = [
            (
                "have",
                "have: expected object definition, `fn`, or `by preimage`",
            ),
            ("have by", "have by: expected `preimage`"),
            ("stop", "stop: expected `strategy`"),
        ];

        for (source_code, expected_message) in cases {
            let message = parse_one_stmt_error_message(source_code);
            assert_eq!(message, expected_message);
            assert!(
                !message.contains("Expected token: at index"),
                "{source_code:?} leaked a token-index error: {message}",
            );
        }
    }

    #[test]
    fn trust_forms_and_import_boundaries_parse_as_expected() {
        for source_code in [
            "trust 1 = 1",
            "trust:\n    1 = 1",
            "trust have x R:\n    x = 1",
        ] {
            assert!(parse_one_stmt(source_code).is_ok(), "{source_code:?}");
        }
        for source_code in ["local import chapter", "trust local import chapter"] {
            let message = parse_one_stmt_error_message(source_code);
            assert!(message.contains("has been removed"), "{message}");
        }
        let message = parse_one_stmt_error_message("import std basics");
        assert!(
            message.contains("only available in an isolated REPL"),
            "{message}"
        );

        let mut runtime = Runtime::new();
        runtime.isolated = true;
        let mut tokenizer = Tokenizer::new();
        let mut blocks = tokenizer
            .parse_blocks(
                "import \"../algebra\" as Algebra\nimport std basics",
                Rc::from("isolated_import_test.lit"),
            )
            .expect("tokenize imports");
        assert!(runtime.parse_stmt(&mut blocks[0]).is_ok());
        assert!(runtime.parse_stmt(&mut blocks[1]).is_ok());
    }

    #[test]
    fn by_def_rejects_body_trailing_tokens_and_non_normal_props() {
        let message = parse_one_stmt_error_message("by def $P(1):\n    1 = 1");
        assert!(message.contains("single-line"), "{}", message);

        let mut tokenizer = Tokenizer::new();
        let error = tokenizer
            .parse_blocks(
                "by def $P(1)\n    1 = 1",
                Rc::from("parse_stmt_diagnostic_test.lit"),
            )
            .expect_err("an indented body without `:` should fail tokenization");
        let RuntimeError::ParseError(error) = error else {
            panic!("expected parse error");
        };
        assert!(error.msg.contains("unexpected indent"), "{}", error.msg);

        for source_code in ["by def not $P(1)", "by def $in(1, R)", "by def 1 = 1"] {
            let message = parse_one_stmt_error_message(source_code);
            assert!(
                message.contains("expects one positive concrete prop fact"),
                "{}: {}",
                source_code,
                message
            );
        }
    }

    #[test]
    fn function_implementation_syntax_has_targeted_migrations() {
        assert_eq!(
            parse_one_stmt_error_message("algo f(x):\n    x"),
            "algorithm implementations must use `have algo for f(...)`"
        );
        assert_eq!(
            parse_one_stmt_error_message("have algo f(x):\n    x"),
            "have algo: expected `for f(...)`"
        );
        assert_eq!(
            parse_one_stmt_error_message("have fn as algo f(x R) R = x"),
            "`have fn as algo` has been replaced by `have fn ...` followed by `have algo for f(...)`"
        );
    }
}
