use crate::common::keywords::{
    ABSTRACT_PROP, ALGO, AXIOM, BY, CART, CLAIM, CLEAR, DO_NOTHING, EVAL, EXAMPLE, FINITE_SEQ,
    FN_LOWER_CASE, FOR, HAVE, IMPORT, LET, MATRIX, OBTAIN, PREIMAGE, PROP, QUESTION_GOAL, SEQ,
    SETTING, SKETCH, STOP, STRATEGY, STRONG_INDUC, STRUCT, TEMPLATE, THM, TRUST, TRY, TUPLE, USE,
    WITNESS,
};
use crate::error::{ParseRuntimeError, RuntimeError, RuntimeErrorStruct};
use crate::parse::TokenBlock;
use crate::pipeline::record_pipeline_step;
use crate::runtime::Runtime;
use crate::stmt::Stmt;

impl Runtime {
    pub fn parse_statement(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        record_pipeline_step(
            "parse",
            "Runtime::parse_statement",
            "src/parse/statement_parsing.rs",
        );
        self.ensure_execution_frame_for_parse();
        let saved_parse_context = self.current_parse_context().clone();
        let result = self.parse_statement_from_leading_token(tb);
        if result.is_err() {
            *self.current_parse_context_mut() = saved_parse_context;
        }
        result
    }

    fn parse_statement_from_leading_token(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        match tb.current()? {
            PROP => self.parse_def_prop_stmt(tb),
            ABSTRACT_PROP => self.parse_def_abstract_prop_stmt(tb),
            LET => self.parse_let_obj_stmt(tb),
            HAVE => match tb.token_at_add_index(1) {
                ALGO => match tb.token_at_add_index(2) {
                    FOR => self.parse_have_algo_for_stmt(tb),
                    _ => Err(statement_dispatch_error(
                        tb,
                        "have algo: expected `for f(...)`",
                    )),
                },
                TUPLE => self.parse_have_tuple_stmt(tb),
                CART => self.parse_have_cart_stmt(tb),
                SEQ => self.parse_have_seq_stmt(tb),
                FINITE_SEQ => self.parse_have_finite_seq_stmt(tb),
                MATRIX => self.parse_have_matrix_stmt(tb),
                FN_LOWER_CASE => self.parse_have_fn_stmt(tb),
                BY => match tb.token_at_add_index(2) {
                    PREIMAGE => self.parse_have_preimage(tb),
                    _ => Err(statement_dispatch_error(tb, "have by: expected `preimage`")),
                },
                "" => Err(statement_dispatch_error(
                    tb,
                    "have: expected object definition, `fn`, or `by preimage`",
                )),
                _ => self.parse_have_obj_stmt(tb),
            },
            OBTAIN => self.parse_obtain_obj(tb),
            CLEAR => self.parse_clear_stmt(tb),
            CLAIM => self.parse_claim_stmt(tb),
            EXAMPLE => self.parse_example_stmt(tb),
            THM => self.parse_def_thm_stmt(tb),
            AXIOM => self.parse_def_axiom_stmt(tb),
            STRATEGY => self.parse_def_strategy_stmt(tb),
            USE => self.parse_use_strategy_stmt(tb),
            STOP => match tb.token_at_add_index(1) {
                STRATEGY => self.parse_stop_strategy_stmt(tb),
                _ => Err(statement_dispatch_error(tb, "stop: expected `strategy`")),
            },
            SKETCH => self.parse_sketch_stmt(tb),
            TRY => self.parse_try_stmt(tb),
            QUESTION_GOAL => Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "top-level `?` is not supported; use it as a goal block inside claim/example/thm/by/strategy statements".to_string(),
                    tb.line_file.clone(),
                ),
            ))),
            TRUST => self.parse_trust_stmt(tb),
            IMPORT => self.parse_import_stmt(tb),
            DO_NOTHING => self.parse_do_nothing_stmt(tb),
            EVAL => self.parse_eval_stmt(tb),
            WITNESS => self.parse_witness_stmt(tb),
            STRUCT => self.parse_def_struct_stmt(tb),
            TEMPLATE => self.parse_def_template_stmt(tb),
            SETTING => self.parse_def_setting_stmt(tb),
            STRONG_INDUC => Err(statement_dispatch_error(
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

fn statement_dispatch_error(tb: &TokenBlock, msg: &str) -> RuntimeError {
    RuntimeError::from(ParseRuntimeError(
        RuntimeErrorStruct::new_with_msg_and_line_file(msg.to_string(), tb.line_file.clone()),
    ))
}

#[cfg(test)]
#[path = "../../tests/unit/parse/statement_parsing/diagnostics.rs"]
mod diagnostic_tests;
