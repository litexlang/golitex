use crate::error::ParsingError;
use crate::common::keywords::{ALGO, CLAIM, CLEAR, DO_NOTHING, EVAL, EXIST, FN, HAVE, IMPORT, KNOW, LET, PROP, PROVE, RUN_FILE, STRUCT, VIEW_FN_AS_SET, WITNESS, CASES, CONTRA, ENUM, INDUC, FOR, EQUAL_SET}; use super::Parser;
use crate::stmt::Stmt;
use super::TokenBlock;

impl Parser {
    pub fn parse_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        match tb.current()? {
            PROP => self.def_prop_stmt_or_prop_without_meaning(tb),
            LET => self.def_let_stmt(tb),
            HAVE => {
                if tb.token_at_index(1)? == FN {
                    self.have_fn_stmt(tb)
                } else if tb.token_at_index(1)? == EXIST {
                    self.have_exist(tb)
                } else {
                    self.have_obj_stmt(tb)
                }
            },
            KNOW => self.know_stmt(tb),
            CLAIM => self.claim_stmt(tb),
            PROVE => self.prove_stmt(tb),
            IMPORT => self.import_stmt(tb),
            CLEAR => self.clear_stmt(tb),
            DO_NOTHING => self.do_nothing_stmt(tb),
            RUN_FILE => self.run_file_stmt(tb),
            EVAL => self.eval_stmt(tb),
            WITNESS => self.witness_stmt(tb),
            STRUCT => self.def_struct_stmt(tb),
            ALGO => self.def_algorithm_stmt(tb),
            CASES => self.prove_case_by_case_stmt(tb),
            CONTRA => self.prove_by_contradiction_stmt(tb),
            ENUM => self.prove_by_enumeration_stmt(tb),
            INDUC => self.prove_by_induction_stmt(tb),
            FOR => self.prove_for_stmt(tb),
            EQUAL_SET => self.prove_equal_set_by_def_stmt(tb),
            VIEW_FN_AS_SET => self.view_fn_as_set_stmt(tb),
            _ => {
                let fact = self.parse_fact(tb)?;
                Ok(Stmt::Fact(fact))
            }
        }
    }
}