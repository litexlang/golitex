//! Top-level `algo name(…) ret by cases:` / `algo name(…) ret by induc …:`.

use super::super::keywords::{BY, CASE, CASES, COLON, FROM, INDUC};
use super::super::object::{is_simple_name, parse_obj};
use crate::ast::fact::AndChainAtomicFact;
use crate::ast::line_file::SourceLine;
use crate::ast::names::BoundName;
use crate::ast::obj::Obj;
use crate::ast::stmt::{
    DefAlgoByCasesStmt, DefAlgoByInducStmt, DefinitionStmt, FnSetClause, Stmt,
};
use crate::runtime::{Runtime, RuntimeParseError, RuntimeResult};
use crate::tokenize::TokenBlock;

impl Runtime {
    // `algo f(x R) R by cases:` … | `algo f(n N) N by induc n from 0:` …
    pub(in crate::parse) fn parse_algo_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.advance()?; // `algo`

        let name = tb.advance().map_err(|_| {
            RuntimeParseError::new(
                "`algo` expects a function name",
                block.line,
                block.source_path.clone(),
            )
        })?;
        if !is_simple_name(&name) {
            return Err(RuntimeParseError::new(
                format!("invalid algo name `{name}`"),
                block.line,
                block.source_path.clone(),
            )
            .into());
        }

        let bound = self.define_plain_atom_as_parse(&tb, name.clone())?;

        self.push_parse_scope();
        let result = (|| {
            let (params, dom_facts) = self.parse_fn_set_header(&mut tb)?;
            let ret_set = parse_obj(self, &mut tb)?;
            let fn_set_clause = FnSetClause {
                set_bound_parameters: params,
                dom_facts,
                ret_set,
            };

            tb.expect(BY)?;
            if tb.peek() == Some(CASES) {
                return self.parse_algo_by_cases_tail(block, &mut tb, bound, fn_set_clause);
            }
            if tb.peek() == Some(INDUC) {
                return self.parse_algo_by_induc_tail(block, &mut tb, bound, fn_set_clause);
            }
            Err(tb.parse_error(
                "algo: expected `by cases` or `by induc` after signature",
            ))
        })();
        self.pop_parse_scope();
        result
    }

    fn parse_algo_by_cases_tail(
        &mut self,
        block: &TokenBlock,
        tb: &mut TokenBlock,
        name: BoundName,
        fn_set_clause: FnSetClause,
    ) -> RuntimeResult<Stmt> {
        tb.expect(CASES)?;
        tb.expect(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(tb.parse_error("unexpected token after `algo ... by cases:`"));
        }
        if block.body.is_empty() {
            return Err(RuntimeParseError::new(
                "algo by cases: expects at least one `case` arm",
                block.line,
                block.source_path.clone(),
            )
            .into());
        }

        let mut cases: Vec<AndChainAtomicFact> = Vec::new();
        let mut equal_tos: Vec<Obj> = Vec::new();
        for child in &block.body {
            let mut arm = child.clone();
            arm.expect(CASE)?;
            let case = self.parse_and_chain_atomic_fact_allow_not(&mut arm)?;
            arm.expect(COLON)?;
            let equal_to = parse_obj(self, &mut arm)?;
            if !arm.exceed_end_of_head() {
                return Err(arm.parse_error("case: trailing tokens after value"));
            }
            if !arm.body.is_empty() {
                return Err(arm.parse_error("case: value must be on the case header line"));
            }
            cases.push(case);
            equal_tos.push(equal_to);
        }

        Ok(Stmt::Definition(DefinitionStmt::DefAlgoByCasesStmt(
            DefAlgoByCasesStmt {
                name,
                fn_set_clause,
                cases,
                equal_tos,
                line_file: SourceLine::new(block.line, self.code_source.clone()),
            },
        )))
    }

    fn parse_algo_by_induc_tail(
        &mut self,
        block: &TokenBlock,
        tb: &mut TokenBlock,
        name: BoundName,
        fn_set_clause: FnSetClause,
    ) -> RuntimeResult<Stmt> {
        tb.expect(INDUC)?;
        let measure = parse_obj(self, tb)?;
        tb.expect(FROM)?;
        let lower_bound = parse_obj(self, tb)?;
        tb.expect(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(tb.parse_error(
                "unexpected token after `algo ... by induc <measure> from <lower>:`",
            ));
        }
        if block.body.is_empty() {
            return Err(RuntimeParseError::new(
                "algo by induc: expects at least one `case` arm",
                block.line,
                block.source_path.clone(),
            )
            .into());
        }
        let cases = self.parse_have_fn_by_induc_cases(&block.body)?;
        Ok(Stmt::Definition(DefinitionStmt::DefAlgoByInducStmt(
            DefAlgoByInducStmt {
                name,
                fn_set_clause,
                measure,
                lower_bound,
                cases,
                line_file: SourceLine::new(block.line, self.code_source.clone()),
            },
        )))
    }
}
