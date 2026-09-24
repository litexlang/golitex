use super::super::keywords::{REFLEXIVE, REGISTER, SYMMETRIC, TRANSITIVE};
use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::ast::stmt::{
    RegisterReflexivePropStmt, RegisterStmt, RegisterSymmetricPropStmt,
    RegisterTransitivePropStmt, Stmt,
};
use crate::new_pipeline::parse::prop_registration_shape::{
    reflexive_prop_name_from_forall, symmetric_prop_registration_from_forall,
    transitive_prop_name_from_forall,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

impl Runtime {
    pub(in super::super) fn parse_register_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(REGISTER)?;
        match tb.peek() {
            Some(REFLEXIVE) => self.parse_register_reflexive_prop_stmt(&mut tb, block),
            Some(SYMMETRIC) => self.parse_register_symmetric_prop_stmt(&mut tb, block),
            Some(TRANSITIVE) => self.parse_register_transitive_prop_stmt(&mut tb, block),
            other => Err(tb.parse_error(format!(
                "register: expected `transitive`, `symmetric`, or `reflexive`, got {other:?}"
            ))),
        }
    }

    fn parse_register_reflexive_prop_stmt(
        &mut self,
        tb: &mut TokenBlock,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        tb.expect(REFLEXIVE)?;
        tb.expect_colon_end_of_header()?;
        let forall_fact = self.parse_register_prop_forall_goal(tb, "register reflexive")?;
        if let Err(msg) = reflexive_prop_name_from_forall(&forall_fact) {
            return Err(tb.parse_error(msg));
        }
        Ok(Stmt::Register(RegisterStmt::RegisterReflexivePropStmt(
            RegisterReflexivePropStmt {
                forall_fact,
                line_file: LineFile::new(block.line, block.source_path.clone()),
            },
        )))
    }

    fn parse_register_symmetric_prop_stmt(
        &mut self,
        tb: &mut TokenBlock,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        tb.expect(SYMMETRIC)?;
        tb.expect_colon_end_of_header()?;
        let forall_fact = self.parse_register_prop_forall_goal(tb, "register symmetric")?;
        if let Err(msg) = symmetric_prop_registration_from_forall(&forall_fact) {
            return Err(tb.parse_error(msg));
        }
        Ok(Stmt::Register(RegisterStmt::RegisterSymmetricPropStmt(
            RegisterSymmetricPropStmt {
                forall_fact,
                line_file: LineFile::new(block.line, block.source_path.clone()),
            },
        )))
    }

    fn parse_register_transitive_prop_stmt(
        &mut self,
        tb: &mut TokenBlock,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        tb.expect(TRANSITIVE)?;
        tb.expect_colon_end_of_header()?;
        let forall_fact = self.parse_register_prop_forall_goal(tb, "register transitive")?;
        if let Err(msg) = transitive_prop_name_from_forall(&forall_fact) {
            return Err(tb.parse_error(msg));
        }
        Ok(Stmt::Register(RegisterStmt::RegisterTransitivePropStmt(
            RegisterTransitivePropStmt {
                forall_fact,
                line_file: LineFile::new(block.line, block.source_path.clone()),
            },
        )))
    }

    fn parse_register_prop_forall_goal(
        &mut self,
        tb: &mut TokenBlock,
        syntax: &str,
    ) -> RuntimeResult<crate::new_pipeline::ast::fact::ForallFact> {
        if tb.body.is_empty() {
            return Err(tb.parse_error(format!(
                "{syntax}: expects one shaped `? forall …` goal (no proof body)"
            )));
        }
        if tb.body.len() != 1 {
            return Err(tb.parse_error(format!(
                "{syntax}: indented proof body is not supported; prove the forall first, then register"
            )));
        }
        let mut goal = tb.body[0].clone();
        self.parse_goal_forall_fact(&mut goal, syntax)
    }
}
