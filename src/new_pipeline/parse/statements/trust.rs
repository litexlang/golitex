use super::super::keywords::{COLON, HAVE, TRUST};
use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::ast::stmt::{Stmt, TrustHaveStmt, TrustStmt, UnsafeStmt};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

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
                return Err(tb.parse_error(
                    "`trust:` facts must be written in an indented body",
                ));
            }
            let facts = self.parse_facts_in_body(&tb.body)?;
            return Ok(Stmt::UnsafeStmt(UnsafeStmt::TrustStmt(TrustStmt {
                facts,
                line_file: LineFile::new(block.line, block.source_path.clone()),
            })));
        }

        let fact = self.parse_fact(&mut tb)?;
        if !tb.body.is_empty() {
            return Err(tb.parse_error(
                "inline `trust` cannot have an indented body; use `trust:`",
            ));
        }
        Ok(Stmt::UnsafeStmt(UnsafeStmt::TrustStmt(TrustStmt {
            facts: vec![fact],
            line_file: LineFile::new(block.line, block.source_path.clone()),
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
                    return Err(tb.parse_error(
                        "trust have without `:` cannot have an indented body",
                    ));
                }
                Vec::new()
            };
            let names: Vec<String> = param_def
                .groups
                .iter()
                .flat_map(|g| g.params.iter().cloned())
                .collect();
            Ok((param_def, facts, names))
        })();
        self.pop_parse_scope();
        let (param_def, facts, names) = result?;
        for name in names {
            self.occupy_name_as_parse(block, name)?;
        }
        Ok(Stmt::UnsafeStmt(UnsafeStmt::TrustHaveStmt(TrustHaveStmt {
            param_def,
            facts,
            line_file: LineFile::new(block.line, block.source_path.clone()),
        })))
    }
}
