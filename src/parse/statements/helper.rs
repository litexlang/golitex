use super::super::keywords::{NOT, QUESTION_GOAL};
use crate::ast::fact::{AtomicFact, Fact, ForallFact};
use crate::ast::param::TypedParameterList;
use crate::ast::stmt::Stmt;
use crate::runtime::{Runtime, RuntimeResult};
use crate::tokenize::TokenBlock;

impl Runtime {
    pub(in super::super) fn parse_body_stmts(
        &mut self,
        body: &[TokenBlock],
    ) -> RuntimeResult<Vec<Stmt>> {
        let mut stmts = Vec::with_capacity(body.len());
        for block in body {
            stmts.push(self.parse_token_block(block)?);
        }
        Ok(stmts)
    }

    // `impossible <atomic>` / `impossible not <atomic>` — always one AtomicFact.
    pub(in super::super) fn parse_impossible_atomic_fact(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<AtomicFact> {
        if tb.peek() == Some(NOT) {
            tb.advance()?;
            self.parse_atomic_fact(tb, false)
        } else {
            self.parse_atomic_fact(tb, true)
        }
    }

    // `? <fact>` goal block used inside claim / thm / by / …
    pub(in super::super) fn parse_goal_fact(
        &mut self,
        block: &mut TokenBlock,
        syntax_name: &str,
    ) -> RuntimeResult<Fact> {
        if block.peek() != Some(QUESTION_GOAL) {
            return Err(
                block.parse_error(format!("{syntax_name}: expected a `? <fact>` goal block"))
            );
        }
        block.expect(QUESTION_GOAL)?;
        if block.exceed_end_of_head() {
            return Err(block.parse_error(format!("{syntax_name}: `?` expects a fact")));
        }
        let fact = self.parse_fact(block)?;
        if !block.exceed_end_of_head() {
            return Err(block.parse_error(format!("{syntax_name}: unfinished tokens in `?` goal")));
        }
        if !block.body.is_empty() && !matches!(&fact, Fact::ForallFact(_) | Fact::NotForall(_)) {
            return Err(block.parse_error(format!(
                "{syntax_name}: `?` body is only allowed for multiline `forall` facts"
            )));
        }
        Ok(fact)
    }

    pub(in super::super) fn parse_goal_forall_fact(
        &mut self,
        block: &mut TokenBlock,
        syntax_name: &str,
    ) -> RuntimeResult<ForallFact> {
        match self.parse_goal_fact(block, syntax_name)? {
            Fact::ForallFact(f) => Ok(f),
            _ => Err(block.parse_error(format!(
                "{syntax_name}: goal must be a single `forall` fact"
            ))),
        }
    }

    pub(in super::super) fn parse_facts_in_body(
        &mut self,
        body: &[TokenBlock],
    ) -> RuntimeResult<Vec<Fact>> {
        let mut facts = Vec::with_capacity(body.len());
        for block in body {
            let mut child = block.clone();
            facts.push(self.parse_complete_fact(&mut child)?);
        }
        Ok(facts)
    }

    // Re-open forall binders so proof statements may use the same names.
    pub(in super::super) fn with_forall_params_occupied<T>(
        &mut self,
        params: &TypedParameterList,
        tb: &TokenBlock,
        f: impl FnOnce(&mut Self) -> RuntimeResult<T>,
    ) -> RuntimeResult<T> {
        self.push_parse_scope();
        let result = (|| {
            for group in &params.groups {
                for identifier in &group.params {
                    self.occupy_bound_name_as_parse(tb, identifier)?;
                }
            }
            f(self)
        })();
        self.pop_parse_scope();
        result
    }

    pub(in super::super) fn forall_params_of_fact(fact: &Fact) -> Option<&TypedParameterList> {
        match fact {
            Fact::ForallFact(f) => Some(&f.typed_parameters),
            Fact::NotForall(n) => Some(&n.typed_parameters),
            _ => None,
        }
    }
}
