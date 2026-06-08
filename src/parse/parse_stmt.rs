use crate::prelude::*;

impl Runtime {
    pub fn parse_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        match tb.current()? {
            ALIAS => self.parse_alias_stmt(tb),
            PROP => self.parse_def_prop_stmt(tb),
            ABSTRACT_PROP => self.parse_def_abstract_prop_stmt(tb),
            LET => self.parse_def_let_stmt(tb),
            HAVE => {
                if tb.token_at_index(1)? == FN_LOWER_CASE {
                    self.parse_have_fn_stmt(tb)
                } else if tb.token_at_index(1)? == BY && tb.token_at_index(2)? == PREIMAGE {
                    self.parse_have_preimage(tb)
                } else if tb.token_at_index(1)? == BY && tb.token_at_index(2)? == EXIST {
                    self.parse_have_exist(tb)
                } else {
                    self.parse_have_obj_stmt(tb)
                }
            }
            KNOW => self.parse_know_stmt(tb),
            CLEAR => self.parse_clear_stmt(tb),
            CLAIM => self.parse_claim_stmt(tb),
            THM => self.parse_def_thm_stmt(tb),
            STRATEGY => self.parse_def_strategy_stmt(tb),
            USE => self.parse_use_strategy_stmt(tb),
            STOP if tb.token_at_index(1)? == IMPORT => self.parse_stop_import_stmt(tb),
            STOP => self.parse_stop_strategy_stmt(tb),
            SKETCH => self.parse_sketch_stmt(tb),
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
            IMPORT => self.parse_import_stmt(tb),
            DO_NOTHING => self.parse_do_nothing_stmt(tb),
            DOT_DOT_DOT => self.parse_do_nothing_stmt(tb),
            RUN_FILE => self.parse_run_file_stmt(tb),
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
