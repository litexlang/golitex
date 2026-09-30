use super::super::keywords::{EXIST, EXIST_BANG, FACT_PREFIX, FROM, OBTAIN};
use super::super::object::is_simple_name;
use crate::ast::fact::{AtomicFact, ExistShapedFact, NormalAtomicFact};
use crate::ast::line_file::SourceLine;
use crate::ast::stmt::{
    DefineObjStmt, DefinitionStmt, ObtainObjFromAtomicFact, ObtainObjFromExistFact, Stmt,
};
use crate::runtime::{Runtime, RuntimeResult};
use crate::tokenize::TokenBlock;

enum ObtainSource {
    Exist(ExistShapedFact),
    Atomic(NormalAtomicFact),
}

impl Runtime {
    // obtain x, y from exist … / exist! … / $P(…)
    pub(in super::super) fn parse_obtain_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(OBTAIN)?;

        let mut names = Vec::new();
        loop {
            if tb.peek() == Some(FROM) {
                break;
            }
            let name = tb
                .advance()
                .map_err(|_| tb.parse_error("`obtain` expects a name or `from`"))?;
            if !is_simple_name(&name) {
                return Err(tb.parse_error(format!("invalid obtain name `{name}`")));
            }
            names.push(name);
            if tb.peek() == Some(super::super::keywords::COMMA) {
                tb.advance()?;
            } else if tb.peek() != Some(FROM) {
                return Err(tb.parse_error("`obtain` expects `,` or `from` after each name"));
            }
        }
        if names.is_empty() {
            return Err(tb.parse_error("`obtain` expects at least one name before `from`"));
        }
        tb.expect(FROM)?;

        // Parse the source before introducing the witnesses. In
        // `obtain k from exist k Z st {...}`, the existential binder's scope
        // ends before the new witness k is allocated in the surrounding scope.
        let source = if tb.peek() == Some(EXIST) || tb.peek() == Some(EXIST_BANG) {
            ObtainSource::Exist(self.parse_exist_fact(&mut tb)?)
        } else if tb.peek() == Some(FACT_PREFIX) {
            let atomic = self.parse_atomic_fact(&mut tb, true)?;
            let AtomicFact::NormalAtomicFact(fact) = atomic else {
                return Err(
                    tb.parse_error("obtain from `$P` expects a positive normal atomic fact")
                );
            };
            ObtainSource::Atomic(fact)
        } else {
            return Err(
                tb.parse_error("obtain: expected `exist` / `exist!` / `$P(...)` after `from`")
            );
        };

        if !tb.exceed_end_of_head() {
            return Err(tb.parse_error("trailing tokens after obtain source"));
        }
        if !tb.body.is_empty() {
            return Err(tb.parse_error("obtain cannot have an indented body"));
        }

        let equal_tos = names
            .into_iter()
            .map(|name| self.define_plain_atom_as_parse(&tb, name))
            .collect::<RuntimeResult<Vec<_>>>()?;
        let line_file = SourceLine::new(block.line, self.code_source.clone());
        let definition = match source {
            ObtainSource::Exist(fact) => {
                DefineObjStmt::ObtainObjFromExistFact(ObtainObjFromExistFact {
                    equal_tos,
                    fact,
                    line_file,
                })
            }
            ObtainSource::Atomic(fact) => {
                DefineObjStmt::ObtainObjFromAtomicFact(ObtainObjFromAtomicFact {
                    equal_tos,
                    fact,
                    line_file,
                })
            }
        };
        Ok(Stmt::Definition(DefinitionStmt::DefineObj(definition)))
    }
}
