use crate::errors::ParsingError;
use crate::keywords::{CLAIM, CLEAR, DO_NOTHING, EXIST, FN, HAVE, IMPORT, KNOW, LET, PROP, PROVE, RUN_FILE, EVAL, WITNESS, SET_TEMPLATE, ALGO};
use crate::parser::Parser;
use crate::stmt::Stmt;
use crate::token_block::TokenBlock;

impl Parser {
    pub fn stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        match tb.current()? {
            PROP => self.def_prop_stmt(tb),
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
            SET_TEMPLATE => self.def_set_template_stmt(tb),
            ALGO => self.def_algorithm_stmt(tb),
            _ => {
                let fact = self.fact(tb)?;
                Ok(Stmt::Fact(fact))
            }
        }
    }
}