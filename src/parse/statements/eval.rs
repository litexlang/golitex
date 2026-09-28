use super::super::keywords::EVAL;
use super::super::object::parse_obj;
use crate::ast::line_file::SourceLine;
use crate::ast::stmt::{CommandStmt, EvalStmt, Stmt};
use crate::runtime::{Runtime, RuntimeResult};
use crate::tokenize::TokenBlock;

impl Runtime {
    // eval <obj>
    pub(in super::super) fn parse_eval_stmt(&mut self, block: &TokenBlock) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(EVAL)?;
        let obj_to_eval = parse_obj(self, &mut tb)?;
        if !tb.exceed_end_of_head() {
            return Err(tb.parse_error("eval: expected one expression"));
        }
        if !tb.body.is_empty() {
            return Err(tb.parse_error("eval cannot have an indented body"));
        }
        Ok(Stmt::Command(CommandStmt::EvalStmt(EvalStmt {
            obj_to_eval,
            line_file: SourceLine::new(block.line, self.code_source.clone()),
        })))
    }
}
