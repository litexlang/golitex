//! `have algo for fn f(x):` — executable presentation for an existing function.

use super::super::keywords::{
    ALGO, CASE, COLON, COMMA, FN, FOR, LEFT_PAREN, RIGHT_PAREN,
};
use super::super::object::{is_simple_name, parse_obj};
use crate::new_pipeline::ast::line_file::SourceLine;
use crate::new_pipeline::ast::stmt::{
    AlgoCase, AlgoReturn, DefAlgoStmt, DefinitionStmt, Stmt,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeParseError, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

impl Runtime {
    // have algo for fn f(x, y):
    //     case …: …
    //     …
    //     default_return_expr
    pub(in crate::new_pipeline::parse) fn parse_have_algo_for_fn_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.advance()?; // `have`
        tb.expect(ALGO)?;
        tb.expect(FOR)?;
        tb.expect(FN)?;

        let name = tb.advance().map_err(|_| {
            RuntimeParseError::new(
                "`have algo for fn` expects a function name",
                block.line,
                block.source_path.clone(),
            )
        })?;
        if !is_simple_name(&name) {
            return Err(RuntimeParseError::new(
                format!("invalid algo target fn name `{name}`"),
                block.line,
                block.source_path.clone(),
            )
            .into());
        }

        self.push_parse_scope();
        let result = (|| {
            tb.expect(LEFT_PAREN)?;
            let mut param_bindings: Vec<String> = Vec::new();
            if tb.peek() != Some(RIGHT_PAREN) {
                loop {
                    let param = tb.advance().map_err(|_| {
                        tb.parse_error("`have algo for fn`: expected parameter name")
                    })?;
                    if !is_simple_name(&param) {
                        return Err(tb.parse_error(format!(
                            "invalid algo parameter name `{param}`"
                        )));
                    }
                    let _bound = self.define_plain_atom_as_parse(&tb, param.clone())?;
                    param_bindings.push(param);
                    if tb.peek() == Some(COMMA) {
                        tb.advance()?;
                        continue;
                    }
                    break;
                }
            }
            tb.expect(RIGHT_PAREN)?;
            tb.expect(COLON)?;
            if !tb.exceed_end_of_head() {
                return Err(tb.parse_error(
                    "unexpected token after `have algo for fn …:`",
                ));
            }

            let mut cases: Vec<AlgoCase> = Vec::new();
            let mut default_return: Option<AlgoReturn> = None;
            match block.body.split_last() {
                None => {}
                Some((last, leading)) => {
                    for child in leading {
                        cases.push(self.parse_algo_case_arm(child)?);
                    }
                    let mut last_tb = last.clone();
                    if last_tb.peek() == Some(CASE) {
                        cases.push(self.parse_algo_case_arm(last)?);
                    } else {
                        let value = parse_obj(self, &mut last_tb)?;
                        if !last_tb.exceed_end_of_head() {
                            return Err(last_tb.parse_error(
                                "algo default return: trailing tokens",
                            ));
                        }
                        if !last_tb.body.is_empty() {
                            return Err(last_tb.parse_error(
                                "algo default return cannot have an indented body",
                            ));
                        }
                        default_return = Some(AlgoReturn {
                            value,
                            line_file: SourceLine::new(last.line, self.code_source.clone()),
                        });
                    }
                }
            }

            if cases.is_empty() && default_return.is_none() {
                return Err(RuntimeParseError::new(
                    "have algo for fn: expects at least one `case` or a default return",
                    block.line,
                    block.source_path.clone(),
                )
                .into());
            }

            Ok(Stmt::Definition(DefinitionStmt::DefAlgoStmt(DefAlgoStmt {
                name,
                param_bindings,
                default_return,
                cases,
                line_file: SourceLine::new(block.line, self.code_source.clone()),
            })))
        })();
        self.pop_parse_scope();
        result
    }

    fn parse_algo_case_arm(&mut self, block: &TokenBlock) -> RuntimeResult<AlgoCase> {
        let mut tb = block.clone();
        tb.expect(CASE)?;
        let condition = self.parse_atomic_fact(&mut tb, true)?;
        tb.expect(COLON)?;
        let value = parse_obj(self, &mut tb)?;
        if !tb.exceed_end_of_head() {
            return Err(tb.parse_error("algo case: trailing tokens after return value"));
        }
        if !tb.body.is_empty() {
            return Err(tb.parse_error("algo case: return value must be on the case line"));
        }
        Ok(AlgoCase {
            condition,
            return_stmt: AlgoReturn {
                value,
                line_file: SourceLine::new(block.line, self.code_source.clone()),
            },
            line_file: SourceLine::new(block.line, self.code_source.clone()),
        })
    }
}
