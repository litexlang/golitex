use super::super::keywords::{AXIOM, THM};
use super::super::object::is_simple_name;
use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::ast::stmt::{AxiomStmt, DefThmStmt, DefinitionStmt, Stmt};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

impl Runtime {
    // thm Name:
    //   ? <fact>
    //   <proof…>
    pub(in super::super) fn parse_def_thm_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(THM)?;
        let name = tb
            .advance()
            .map_err(|_| tb.parse_error("`thm` expects a name"))?;
        if !is_simple_name(&name) {
            return Err(tb.parse_error(format!("invalid thm name `{name}`")));
        }
        tb.expect_colon_end_of_header()?;
        if tb.body.is_empty() {
            return Err(
                tb.parse_error("thm: expects a `? <fact>` goal block and optional proof body")
            );
        }
        let mut goal = tb.body[0].clone();
        let fact = self.parse_goal_fact(&mut goal, "thm")?;
        let proof_blocks = &tb.body[1..];
        let prove_process = if let Some(params) = Self::forall_params_of_fact(&fact) {
            self.with_forall_params_occupied(params, &tb, |this| {
                this.parse_body_stmts(proof_blocks)
            })?
        } else {
            self.parse_body_stmts(proof_blocks)?
        };
        self.define_plain_atom_as_parse(&tb, name.clone())?;
        Ok(Stmt::Definition(DefinitionStmt::DefThmStmt(DefThmStmt {
            name,
            fact,
            prove_process,
            line_file: LineFile::new(block.line, block.source_path.clone()),
        })))
    }

    // axiom Name:
    //   ? forall …
    pub(in super::super) fn parse_axiom_stmt(&mut self, block: &TokenBlock) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(AXIOM)?;
        let name = tb
            .advance()
            .map_err(|_| tb.parse_error("`axiom` expects a name"))?;
        if !is_simple_name(&name) {
            return Err(tb.parse_error(format!("invalid axiom name `{name}`")));
        }
        tb.expect_colon_end_of_header()?;
        if tb.body.len() != 1 {
            return Err(tb.parse_error("axiom: expects exactly one `? forall ...` goal block"));
        }
        let mut goal = tb.body[0].clone();
        let forall_fact = self.parse_goal_forall_fact(&mut goal, "axiom")?;
        self.define_plain_atom_as_parse(&tb, name.clone())?;
        Ok(Stmt::Definition(DefinitionStmt::AxiomStmt(AxiomStmt {
            name,
            forall_fact,
            line_file: LineFile::new(block.line, block.source_path.clone()),
        })))
    }
}
