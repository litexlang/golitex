//! `have fn name(...) ret = body` parse (expression form only).

use super::super::keywords::{BY, COLON, EQUAL, FN};
use super::super::object::{is_simple_name, parse_obj};
use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::ast::obj::{AnonymousFn, FnSet};
use crate::new_pipeline::ast::stmt::{DefinitionStmt, HaveFnEqualStmt, Stmt};
use crate::new_pipeline::runtime::{Runtime, RuntimeParseError, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

impl Runtime {
    // `have fn f(x R) R = x + 1`
    // Cases / induc / exist! stay unwired in this slice.
    pub(in crate::new_pipeline::parse) fn parse_have_fn_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        if !block.body.is_empty() {
            return Err(RuntimeParseError::new(
                "`have fn ... =` cannot have an indented body",
                block.line,
                block.source_path.clone(),
            )
            .into());
        }

        let mut tb = block.clone();
        tb.advance()?; // `have`
        tb.expect(FN)?;

        let name = tb.advance().map_err(|_| {
            RuntimeParseError::new(
                "`have fn` expects a function name",
                block.line,
                block.source_path.clone(),
            )
        })?;
        if !is_simple_name(&name) {
            return Err(RuntimeParseError::new(
                format!("invalid have fn name `{name}`"),
                block.line,
                block.source_path.clone(),
            )
            .into());
        }

        // Occupy at the enclosing scope before param binders (file-root first).
        let _bound = self.define_plain_atom_as_parse(&tb, name.clone())?;

        self.push_parse_scope();
        let result = (|| {
            let (params, dom_facts) = self.parse_fn_set_header(&mut tb)?;
            let ret_set = parse_obj(self, &mut tb)?;

            if tb.peek() == Some(BY) || tb.peek() == Some(COLON) {
                return Err(RuntimeParseError::new(
                    "have fn by cases / by induc / by exist! / colon body: not wired yet in new_pipeline",
                    block.line,
                    block.source_path.clone(),
                )
                .into());
            }

            tb.expect(EQUAL)?;
            let equal_to = parse_obj(self, &mut tb)?;
            if !tb.exceed_end_of_head() {
                return Err(tb.parse_error("trailing tokens after have fn equal body"));
            }

            let equal_to_anonymous_fn = AnonymousFn {
                body: FnSet {
                    set_bound_parameters: params,
                    dom_facts,
                    ret_set: Box::new(ret_set),
                },
                equal_to: Box::new(equal_to),
            };
            Ok(Stmt::Definition(DefinitionStmt::HaveFnEqualStmt(
                HaveFnEqualStmt {
                    name,
                    equal_to_anonymous_fn,
                    line_file: LineFile::new(block.line, block.source_path.clone()),
                },
            )))
        })();
        self.pop_parse_scope();
        result
    }
}
