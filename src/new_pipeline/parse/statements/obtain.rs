use super::super::keywords::{EXIST, EXIST_BANG, FACT_PREFIX, FROM, OBTAIN};
use super::super::object::is_simple_name;
use crate::new_pipeline::ast::fact::AtomicFact;
use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::ast::stmt::{
    DefinitionStmt, ObtainObjFromAtomicFact, ObtainObjFromExistFact, Stmt,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

impl Runtime {
    // obtain x, y from exist … / exist! … / $P(…)
    pub(in super::super) fn parse_obtain_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(OBTAIN)?;

        let mut equal_tos = Vec::new();
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
            equal_tos.push(name);
            if tb.peek() == Some(super::super::keywords::COMMA) {
                tb.advance()?;
            } else if tb.peek() != Some(FROM) {
                return Err(tb.parse_error("`obtain` expects `,` or `from` after each name"));
            }
        }
        if equal_tos.is_empty() {
            return Err(tb.parse_error("`obtain` expects at least one name before `from`"));
        }
        tb.expect(FROM)?;

        let line_file = LineFile::new(block.line, block.source_path.clone());
        let stmt = if tb.peek() == Some(EXIST) || tb.peek() == Some(EXIST_BANG) {
            let fact = self.parse_exist_fact(&mut tb)?;
            Stmt::Definition(DefinitionStmt::ObtainObjFromExistFact(
                ObtainObjFromExistFact {
                    equal_tos: equal_tos.clone(),
                    fact,
                    line_file,
                },
            ))
        } else if tb.peek() == Some(FACT_PREFIX) {
            let atomic = self.parse_atomic_fact(&mut tb, true)?;
            let AtomicFact::NormalAtomicFact(fact) = atomic else {
                return Err(tb.parse_error(
                    "obtain from `$P` expects a positive normal atomic fact",
                ));
            };
            Stmt::Definition(DefinitionStmt::ObtainObjFromAtomicFact(
                ObtainObjFromAtomicFact {
                    equal_tos: equal_tos.clone(),
                    fact,
                    line_file,
                },
            ))
        } else {
            return Err(tb.parse_error(
                "obtain: expected `exist` / `exist!` / `$P(...)` after `from`",
            ));
        };

        if !tb.exceed_end_of_head() {
            return Err(tb.parse_error("trailing tokens after obtain source"));
        }
        if !tb.body.is_empty() {
            return Err(tb.parse_error("obtain cannot have an indented body"));
        }

        for name in &equal_tos {
            self.define_plain_atom_as_parse(&tb, name.clone())?;
        }
        Ok(stmt)
    }
}
