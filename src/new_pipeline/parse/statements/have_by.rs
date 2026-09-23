//! `have by <keyword>: …` introduction forms.
//!
//! Kept separate from ordinary `have x T` so the second token `by` dispatches
//! cleanly (no clash with typed-parameter `name Type`).

use super::super::keywords::{
    BY, COLON, COMMA, FN_PREIMAGE, FROM, HAVE, PREIMAGE, PROP, REPLACEMENT_AXIOM, SET,
};
use super::super::object::{is_simple_name, parse_obj};
use crate::new_pipeline::ast::fact::AtomicFact;
use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::ast::stmt::{
    DefinitionStmt, HaveByPreimageStmt, HaveByReplacementAxiomStmt, Stmt,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

impl Runtime {
    // `have by replacement_axiom: Img from prop P, set A`
    // `have by fn_preimage: source from y $in fn_range(f)`
    pub(in super::super) fn parse_have_by_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(HAVE)?;
        tb.expect(BY)?;
        match tb.peek() {
            Some(REPLACEMENT_AXIOM) => self.parse_have_by_replacement_axiom_stmt(&mut tb, block),
            Some(FN_PREIMAGE) => self.parse_have_by_fn_preimage_stmt(&mut tb, block),
            Some(PREIMAGE) => Err(tb.parse_error(
                "`have by preimage` was renamed; use `have by fn_preimage: names from … $in fn_range(…)`",
            )),
            Some(other) => Err(tb.parse_error(format!(
                "have by: unknown `{other}` (supported: `replacement_axiom`, `fn_preimage`)"
            ))),
            None => Err(tb.parse_error(
                "have by: expected `replacement_axiom` or `fn_preimage`",
            )),
        }
    }

    // Axiom of Replacement: introduce named image set.
    // Example: `have by replacement_axiom: Img from prop image_rel, set {1, 2}`
    fn parse_have_by_replacement_axiom_stmt(
        &mut self,
        tb: &mut TokenBlock,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        tb.expect(REPLACEMENT_AXIOM)?;
        tb.expect(COLON)?;
        let name_tok = tb.advance().map_err(|_| {
            tb.parse_error("have by replacement_axiom: expected a name after `:`")
        })?;
        if !is_simple_name(&name_tok) {
            return Err(tb.parse_error(format!(
                "have by replacement_axiom: invalid name `{name_tok}`"
            )));
        }
        self.push_parse_scope();
        let bound = match self.define_plain_atom_as_parse(tb, name_tok) {
            Ok(b) => b,
            Err(e) => {
                self.pop_parse_scope();
                return Err(e);
            }
        };
        let parsed = (|| {
            tb.expect(FROM)?;
            tb.expect(PROP)?;
            let prop_name = self.parse_prop_name(tb)?;
            tb.expect(COMMA)?;
            tb.expect(SET)?;
            let source_set = parse_obj(self, tb)?;
            if !tb.exceed_end_of_head() {
                return Err(tb.parse_error(
                    "trailing tokens after `have by replacement_axiom: … from prop P, set A`",
                ));
            }
            if !tb.body.is_empty() {
                return Err(tb.parse_error(
                    "`have by replacement_axiom` cannot have an indented body",
                ));
            }
            Ok((prop_name, source_set))
        })();
        self.pop_parse_scope();
        let (prop_name, source_set) = parsed?;
        self.occupy_bound_name_as_parse(block, &bound)?;
        Ok(Stmt::Definition(
            DefinitionStmt::HaveByReplacementAxiomStmt(HaveByReplacementAxiomStmt {
                name: bound,
                prop_name,
                source_set,
                line_file: LineFile::new(block.line, block.source_path.clone()),
            }),
        ))
    }

    // Preimage names from known `… $in fn_range(…)`.
    // Example: `have by fn_preimage: source from shift(2) $in fn_range(shift)`
    fn parse_have_by_fn_preimage_stmt(
        &mut self,
        tb: &mut TokenBlock,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        tb.expect(FN_PREIMAGE)?;
        tb.expect(COLON)?;
        let mut preimage_names = Vec::new();
        loop {
            if tb.peek() == Some(FROM) {
                break;
            }
            let name = tb.advance().map_err(|_| {
                tb.parse_error("have by fn_preimage: expected a name or `from`")
            })?;
            if !is_simple_name(&name) {
                return Err(tb.parse_error(format!(
                    "have by fn_preimage: invalid name `{name}`"
                )));
            }
            preimage_names.push(name);
            if tb.peek() == Some(COMMA) {
                tb.advance()?;
            } else if tb.peek() != Some(FROM) {
                return Err(tb.parse_error(
                    "have by fn_preimage: expected `,` or `from` after each name",
                ));
            }
        }
        if preimage_names.is_empty() {
            return Err(tb.parse_error(
                "have by fn_preimage: expected at least one name before `from`",
            ));
        }
        tb.expect(FROM)?;
        let atomic = self.parse_atomic_fact(tb, true)?;
        let AtomicFact::InFact(range_membership) = atomic else {
            return Err(tb.parse_error(
                "have by fn_preimage: `from` expects a membership fact `… $in fn_range(…)`",
            ));
        };
        if !tb.exceed_end_of_head() {
            return Err(tb.parse_error(
                "trailing tokens after `have by fn_preimage: … from …`",
            ));
        }
        if !tb.body.is_empty() {
            return Err(tb.parse_error(
                "`have by fn_preimage` cannot have an indented body",
            ));
        }
        for name in &preimage_names {
            self.define_plain_atom_as_parse(tb, name.clone())?;
        }
        Ok(Stmt::Definition(DefinitionStmt::HaveByPreimageStmt(
            HaveByPreimageStmt {
                preimage_names,
                range_membership,
                line_file: LineFile::new(block.line, block.source_path.clone()),
            },
        )))
    }
}
