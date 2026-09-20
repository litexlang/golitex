//! `have fn name(...) ret by cases:` / `have fn name(...) ret = expr` /
//! `have fn name by exist!:`.

use super::super::keywords::{BY, CASE, CASES, COLON, EQUAL, EXIST, EXIST_BANG, FN, FROM, INDUC};
use super::super::object::{is_simple_name, parse_obj};
use crate::new_pipeline::ast::fact::AndChainAtomicFact;
use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::ast::obj::{AnonymousFn, FnSet, Obj};
use crate::new_pipeline::ast::stmt::{
    DefinitionStmt, FnSetClause, HaveFnByForallExistUniqueStmt, HaveFnEqualCaseByCaseStmt,
    HaveFnEqualStmt, Stmt,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeParseError, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

impl Runtime {
    // `have fn f(x R) R = x` | `have fn f(x R) Z by cases:` …
    pub(in crate::new_pipeline::parse) fn parse_have_fn_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
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

        // Occupy at enclosing scope before param binders.
        let _bound = self.define_plain_atom_as_parse(&tb, name.clone())?;

        // `have fn name by exist!:` has no signature paren list.
        if tb.peek() == Some(BY) {
            return self.parse_have_fn_by_exist_or_error(block, &mut tb, name);
        }

        self.push_parse_scope();
        let result = (|| {
            let (params, dom_facts) = self.parse_fn_set_header(&mut tb)?;
            let ret_set = parse_obj(self, &mut tb)?;
            let fn_set_clause = FnSetClause {
                set_bound_parameters: params,
                dom_facts,
                ret_set,
            };

            if tb.peek() == Some(BY) {
                tb.expect(BY)?;
                if tb.peek() == Some(CASES) {
                    return self.parse_have_fn_by_cases_tail(block, &mut tb, name, fn_set_clause);
                }
                if tb.peek() == Some(INDUC) {
                    return Err(RuntimeParseError::new(
                        "have fn by induc: not wired yet in new_pipeline",
                        block.line,
                        block.source_path.clone(),
                    )
                    .into());
                }
                return Err(tb.parse_error(
                    "have fn: expected `by cases` or `by induc` after signature",
                ));
            }

            if tb.peek() == Some(COLON) {
                return Err(RuntimeParseError::new(
                    "have fn colon case body: not wired yet in new_pipeline (use `by cases`)",
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
            if !block.body.is_empty() {
                return Err(RuntimeParseError::new(
                    "`have fn ... =` cannot have an indented body",
                    block.line,
                    block.source_path.clone(),
                )
                .into());
            }

            let equal_to_anonymous_fn = AnonymousFn {
                body: FnSet {
                    set_bound_parameters: fn_set_clause.set_bound_parameters,
                    dom_facts: fn_set_clause.dom_facts,
                    ret_set: Box::new(fn_set_clause.ret_set),
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

    fn parse_have_fn_by_cases_tail(
        &mut self,
        block: &TokenBlock,
        tb: &mut TokenBlock,
        name: String,
        fn_set_clause: FnSetClause,
    ) -> RuntimeResult<Stmt> {
        tb.expect(CASES)?;
        tb.expect(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(tb.parse_error("unexpected token after `have fn ... by cases:`"));
        }
        if block.body.is_empty() {
            return Err(RuntimeParseError::new(
                "have fn by cases: expects at least one `case` arm",
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

        Ok(Stmt::Definition(DefinitionStmt::HaveFnEqualCaseByCaseStmt(
            HaveFnEqualCaseByCaseStmt {
                name,
                fn_set_clause,
                cases,
                equal_tos,
                line_file: LineFile::new(block.line, block.source_path.clone()),
            },
        )))
    }

    // `have fn name by exist!:` then `? forall …` + optional fact-only proof.
    fn parse_have_fn_by_exist_or_error(
        &mut self,
        block: &TokenBlock,
        tb: &mut TokenBlock,
        name: String,
    ) -> RuntimeResult<Stmt> {
        tb.expect(BY)?;
        let is_exist_bang = match tb.peek() {
            Some(EXIST_BANG) => {
                tb.advance()?;
                true
            }
            Some(EXIST) => {
                tb.advance()?;
                if tb.peek() == Some(super::super::keywords::BANG) {
                    tb.advance()?;
                    true
                } else {
                    false
                }
            }
            _ => false,
        };
        if !is_exist_bang {
            let _ = FROM;
            return Err(RuntimeParseError::new(
                "have fn: expected signature `(…)` or `by exist!`",
                block.line,
                block.source_path.clone(),
            )
            .into());
        }
        tb.expect(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(tb.parse_error("unexpected token after `have fn … by exist!:`"));
        }
        if block.body.is_empty() {
            return Err(RuntimeParseError::new(
                "`have fn … by exist!:` expects a `? forall ...` goal block",
                block.line,
                block.source_path.clone(),
            )
            .into());
        }

        let mut goal = block.body[0].clone();
        let forall = self.parse_goal_forall_fact(&mut goal, "have fn by exist!")?;
        let proof_blocks = &block.body[1..];
        let prove_process = self.with_forall_params_occupied(
            &forall.typed_parameters,
            block,
            |this| this.parse_body_stmts(proof_blocks),
        )?;

        Ok(Stmt::Definition(
            DefinitionStmt::HaveFnByForallExistUniqueStmt(HaveFnByForallExistUniqueStmt {
                name,
                forall,
                prove_process,
                line_file: LineFile::new(block.line, block.source_path.clone()),
            }),
        ))
    }
}
