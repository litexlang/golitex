use crate::prelude::*;

impl Runtime {
    pub fn parse_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        match tb.current()? {
            PROP => self.parse_def_prop_stmt(tb),
            ABSTRACT_PROP => self.parse_def_abstract_prop_stmt(tb),
            LET => self.parse_def_let_stmt(tb),
            HAVE => {
                if tb.token_at_index(1)? == FN_LOWER_CASE {
                    self.parse_have_fn_stmt(tb)
                } else if tb.token_at_index(1)? == BY && tb.token_at_index(2)? == EXIST {
                    self.parse_have_exist(tb)
                } else {
                    self.parse_have_obj_stmt(tb)
                }
            }
            KNOW => self.parse_know_stmt(tb),
            CLEAR => self.parse_clear_stmt(tb),
            CLAIM => self.parse_claim_stmt(tb),
            PROVE => self.parse_prove_stmt(tb),
            IMPORT => self.parse_import_stmt(tb),
            DO_NOTHING => self.parse_do_nothing_stmt(tb),
            RUN_FILE => self.parse_run_file_stmt(tb),
            EVAL => self.parse_eval_stmt(tb),
            WITNESS => self.parse_witness_stmt(tb),
            FAMILY => self.parse_def_family_stmt(tb),
            STRUCT => Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file("`struct` definitions are not supported in this version".to_string(), tb.line_file.clone()),
            ))),
            ALGO => self.parse_def_algorithm_stmt(tb),
            BY => self.parse_by_prefixed_stmt(tb),
            _ => {
                let fact = self.parse_fact(tb)?;
                Ok(fact.into())
            }
        }
    }
}
