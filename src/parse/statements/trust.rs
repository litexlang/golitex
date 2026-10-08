use super::super::keywords::{COLON, HAVE, TRUST};
use crate::ast::line_file::SourceLine;
use crate::ast::stmt::{Stmt, TrustBoundaryStmt, TrustHaveStmt, TrustStmt};
use crate::runtime::{Runtime, RuntimeResult};
use crate::tokenize::TokenBlock;

impl Runtime {
    // trust <fact> | trust: <body facts> | trust have …
    pub(in super::super) fn parse_trust_stmt(&mut self, block: &TokenBlock) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(TRUST)?;
        if tb.peek() == Some(HAVE) {
            return self.parse_trust_have_stmt(&mut tb, block);
        }
        if tb.peek() == Some(COLON) {
            tb.expect(COLON)?;
            if !tb.exceed_end_of_head() {
                return Err(tb.parse_error("`trust:` facts must be written in an indented body"));
            }
            let facts = self.parse_facts_in_body(&tb.body)?;
            return Ok(Stmt::Trust(TrustBoundaryStmt::TrustStmt(TrustStmt {
                facts,
                line_file: SourceLine::new(block.line, self.code_source.clone()),
            })));
        }

        let fact = self.parse_complete_fact(&mut tb)?;
        if !tb.body.is_empty() {
            return Err(tb.parse_error("inline `trust` cannot have an indented body; use `trust:`"));
        }
        Ok(Stmt::Trust(TrustBoundaryStmt::TrustStmt(TrustStmt {
            facts: vec![fact],
            line_file: SourceLine::new(block.line, self.code_source.clone()),
        })))
    }

    fn parse_trust_have_stmt(
        &mut self,
        tb: &mut TokenBlock,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        tb.expect(HAVE)?;
        self.push_parse_scope();
        let result = (|| {
            let param_def = self.parse_typed_param_list_until_eq_colon_or_end(tb)?;
            let facts = if tb.peek() == Some(COLON) {
                tb.expect(COLON)?;
                if !tb.exceed_end_of_head() {
                    return Err(tb.parse_error(
                        "`trust have ...:` facts must be written in an indented body",
                    ));
                }
                self.parse_facts_in_body(&tb.body)?
            } else {
                if !tb.exceed_end_of_head() {
                    return Err(tb.parse_error(
                        "trust have: expected `:` or end of header after parameters",
                    ));
                }
                if !tb.body.is_empty() {
                    return Err(
                        tb.parse_error("trust have without `:` cannot have an indented body")
                    );
                }
                Vec::new()
            };
            let identifiers: Vec<crate::ast::names::BoundName> = param_def
                .groups
                .iter()
                .flat_map(|g| g.params.iter().cloned())
                .collect();
            Ok((param_def, facts, identifiers))
        })();
        self.pop_parse_scope();
        let (param_def, facts, identifiers) = result?;
        for identifier in &identifiers {
            self.occupy_bound_name_as_parse(block, identifier)?;
        }
        Ok(Stmt::Trust(TrustBoundaryStmt::TrustHaveStmt(
            TrustHaveStmt {
                param_def,
                facts,
                line_file: SourceLine::new(block.line, self.code_source.clone()),
            },
        )))
    }
}
