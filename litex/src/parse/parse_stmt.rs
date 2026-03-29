use crate::prelude::*;

impl Runtime {
    pub fn parse_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        match tb.current()? {
            PROP => self.parse_def_prop_with_meaning_stmt_or_prop_without_meaning(tb),
            LET => self.parse_def_let_stmt(tb),
            HAVE => {
                if tb.token_at_index(1)? == FN_FOR_FN_WITH_PARAMS {
                    self.parse_have_fn_stmt(tb)
                } else if tb.token_at_index(1)? == EXIST {
                    self.parse_have_exist(tb)
                } else {
                    self.parse_have_obj_stmt(tb)
                }
            }
            KNOW => self.parse_know_stmt(tb),
            CLAIM => self.parse_claim_stmt(tb),
            PROVE => self.parse_prove_stmt(tb),
            IMPORT => self.parse_import_stmt(tb),
            DO_NOTHING => self.parse_do_nothing_stmt(tb),
            RUN_FILE => self.parse_run_file_stmt(tb),
            EVAL => self.parse_eval_stmt(tb),
            WITNESS => self.parse_witness_stmt(tb),
            STRUCT => self.parse_def_struct_stmt(tb),
            ALGO => self.parse_def_algorithm_stmt(tb),
            BY_CASES => self.parse_by_cases_axiom_stmt(tb),
            BY_CONTRA => self.parse_by_contra_axiom_stmt(tb),
            ENUMERATE => self.parse_enumerate_axiom_stmt(tb),
            INDUC => self.parse_by_induc_axiom_stmt(tb),
            FOR => self.parse_for_axiom_stmt(tb),
            BY_EXTENSION => self.parse_by_extension_axiom_stmt(tb),
            BY_FN_DEF => self.parse_by_fn_def_axiom_stmt(tb),
            BY_CART_DEF => self.parse_by_cart_def_axiom_stmt(tb),
            _ => {
                let fact = self.parse_fact(tb)?;
                Ok(Stmt::Fact(fact))
            }
        }
    }
}
