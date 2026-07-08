use crate::prelude::*;

impl Runtime {
    pub fn parse_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        match tb.current()? {
            ALIAS => self.parse_alias_stmt(tb),
            PROP => self.parse_def_prop_stmt(tb),
            ABSTRACT_PROP => self.parse_def_abstract_prop_stmt(tb),
            SUPPOSE => self.parse_def_let_stmt(tb),
            LET => Err(parse_stmt_error(
                tb,
                "`let` has been removed; use `suppose` for unproved local object assumptions",
            )),
            HAVE => match tb.token_at_add_index(1) {
                TUPLE => self.parse_have_tuple_stmt(tb),
                CART => self.parse_have_cart_stmt(tb),
                SEQ => self.parse_have_seq_stmt(tb),
                FINITE_SEQ => self.parse_have_finite_seq_stmt(tb),
                MATRIX => self.parse_have_matrix_stmt(tb),
                FN_LOWER_CASE => self.parse_have_fn_stmt(tb),
                BY => match tb.token_at_add_index(2) {
                    PREIMAGE => self.parse_have_preimage(tb),
                    EXIST => Err(parse_stmt_error(
                        tb,
                        "`have by exist ...: name` has been removed; use `obtain name from exist ...`",
                    )),
                    _ => Err(parse_stmt_error(tb, "have by: expected `preimage`")),
                },
                "" => Err(parse_stmt_error(
                    tb,
                    "have: expected object definition, `fn`, or `by preimage`",
                )),
                _ => self.parse_have_obj_stmt(tb),
            },
            OBTAIN => self.parse_obtain_exist_stmt(tb),
            PROOF_DEBT => self.parse_proof_debt_stmt(tb),
            CLEAR => self.parse_clear_stmt(tb),
            CLAIM => self.parse_claim_stmt(tb),
            THM => self.parse_def_thm_stmt(tb),
            AXIOM => self.parse_def_axiom_stmt(tb),
            STRATEGY => self.parse_def_strategy_stmt(tb),
            USE => self.parse_use_strategy_stmt(tb),
            STOP => match tb.token_at_add_index(1) {
                IMPORT => self.parse_stop_import_stmt(tb),
                STRATEGY => self.parse_stop_strategy_stmt(tb),
                _ => Err(parse_stmt_error(tb, "stop: expected `import` or `strategy`")),
            },
            SKETCH => self.parse_sketch_stmt(tb),
            TRY => self.parse_try_stmt(tb),
            SCRATCH => Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "top-level `scratch:` has been replaced by `sketch:`".to_string(),
                    tb.line_file.clone(),
                ),
            ))),
            PROVE => Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "top-level `prove:` is not supported; use `sketch:` for a local checked block, or use `prove:` inside claim/thm/by/strategy statements".to_string(),
                    tb.line_file.clone(),
                ),
            ))),
            QUESTION_GOAL => Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "top-level `?` is not supported; use it as a goal block inside claim/thm/by/strategy statements".to_string(),
                    tb.line_file.clone(),
                ),
            ))),
            IMPORT => self.parse_import_stmt(tb),
            DO_NOTHING => self.parse_do_nothing_stmt(tb),
            DOT_DOT_DOT => self.parse_do_nothing_stmt(tb),
            RUN_FILE => self.parse_run_file_stmt(tb),
            TRUST_FILE => self.parse_trust_file_stmt(tb),
            EVAL => self.parse_eval_stmt(tb),
            WITNESS => self.parse_witness_stmt(tb),
            STRUCT => self.parse_def_struct_stmt(tb),
            TEMPLATE => self.parse_def_template_stmt(tb),
            ALGO => self.parse_def_algorithm_stmt(tb),
            STRONG_INDUC => self.parse_strong_induc_stmt(tb),
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

    #[test]
    fn incomplete_have_and_stop_dispatch_report_syntax_errors() {
        let cases = [
            (
                "have",
                "have: expected object definition, `fn`, or `by preimage`",
            ),
            ("have by", "have by: expected `preimage`"),
            ("stop", "stop: expected `import` or `strategy`"),
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
}
