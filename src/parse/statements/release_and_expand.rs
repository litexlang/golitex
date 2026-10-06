use super::super::keywords::{
    AXIOM_OF_CHOICE, COLON, COMMA, DEF, EXPAND, FACT_PREFIX, IN, OBJ, PROP, REGULARITY_AXIOM,
    RELEASE, SET, STRUCT, THM, ZORN_LEMMA,
};
use super::super::object::{is_simple_name, parse_obj, parse_obj_list_paren};
use crate::ast::line_file::SourceLine;
use crate::ast::names::AtomicName;
use crate::ast::obj::{Obj, SetFormer};
use crate::ast::stmt::{
    ClosedRangeOrRange, ExpandRangeStmt, ReleaseAndExpandStmt, ReleaseAxiomOfChoiceStmt,
    ReleaseObjDefStmt, ReleaseRegularityAxiomStmt, ReleaseStructDefStmt, ReleaseThmStmt,
    ReleaseZornLemmaStmt, Stmt,
};
use crate::runtime::{Runtime, RuntimeResult};
use crate::tokenize::TokenBlock;

impl Runtime {
    pub(in super::super) fn parse_expand_range_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(EXPAND)?;
        tb.expect(COLON)?;
        let element = parse_obj(self, &mut tb)?;
        tb.expect(FACT_PREFIX)?;
        tb.expect(IN)?;
        let domain = parse_obj(self, &mut tb)?;
        if !tb.exceed_end_of_head() || !tb.body.is_empty() {
            return Err(tb.parse_error("expand: unexpected trailing tokens"));
        }
        let range = match domain {
            Obj::SetFormer(SetFormer::ClosedRange(closed)) => {
                ClosedRangeOrRange::ClosedRange(closed)
            }
            Obj::SetFormer(SetFormer::Range(range_obj)) => ClosedRangeOrRange::Range(range_obj),
            _ => {
                return Err(tb.parse_error(
                    "expand: expected `e $in range(…)`, `e $in closed_range(…)`, or `e $in a...b`",
                ));
            }
        };
        Ok(Stmt::ReleaseAndExpand(
            ReleaseAndExpandStmt::ExpandRangeStmt(ExpandRangeStmt {
                element,
                range,
                line_file: SourceLine::new(block.line, self.code_source.clone()),
            }),
        ))
    }

    pub(in super::super) fn parse_release_thm_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(RELEASE)?;
        tb.expect(THM)?;
        let call = self.parse_theorem_call(&mut tb)?;
        if !tb.exceed_end_of_head() || !tb.body.is_empty() {
            return Err(tb.parse_error("release thm accepts only a bare theorem call"));
        }
        Ok(Stmt::ReleaseAndExpand(
            ReleaseAndExpandStmt::ReleaseThmStmt(ReleaseThmStmt {
                call,
                line_file: SourceLine::new(block.line, self.code_source.clone()),
            }),
        ))
    }

    pub(in super::super) fn parse_release_struct_def_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(RELEASE)?;
        tb.expect(STRUCT)?;
        tb.expect(DEF)?;
        if tb.exceed_end_of_head() {
            return Err(tb.parse_error("release struct def expects exactly one object"));
        }
        if !tb.body.is_empty() {
            return Err(tb.parse_error("release struct def does not accept an indented body"));
        }
        let obj = parse_obj(self, &mut tb)?;
        if !tb.exceed_end_of_head() {
            return Err(tb.parse_error(
                "release struct def expects exactly one object and has no `as &Struct` form",
            ));
        }
        Ok(Stmt::ReleaseAndExpand(
            ReleaseAndExpandStmt::ReleaseStructDefStmt(ReleaseStructDefStmt {
                obj,
                line_file: SourceLine::new(block.line, self.code_source.clone()),
            }),
        ))
    }

    pub(in super::super) fn parse_release_obj_def_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(RELEASE)?;
        tb.expect(OBJ)?;
        tb.expect(DEF)?;
        if tb.exceed_end_of_head() {
            return Err(tb.parse_error("release obj def expects exactly one identifier"));
        }
        if !tb.body.is_empty() {
            return Err(tb.parse_error("release obj def does not accept an indented body"));
        }
        let obj = parse_obj(self, &mut tb)?;
        if !tb.exceed_end_of_head() {
            return Err(tb.parse_error("release obj def expects exactly one identifier"));
        }
        let Obj::Identifier(name) = obj else {
            return Err(tb.parse_error("release obj def expects an identifier"));
        };
        Ok(Stmt::ReleaseAndExpand(
            ReleaseAndExpandStmt::ReleaseObjDefStmt(ReleaseObjDefStmt {
                name,
                line_file: SourceLine::new(block.line, self.code_source.clone()),
            }),
        ))
    }

    pub(in super::super) fn parse_release_cart_def_stmt(&mut self, block: &TokenBlock) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(RELEASE)?;
        tb.expect(crate::parse::keywords::CART)?;
        tb.expect(DEF)?;
        let obj = parse_obj(self, &mut tb)?;
        if !tb.exceed_end_of_head() || !tb.body.is_empty() {
            return Err(tb.parse_error("release cart def expects one cart(...) and no body"));
        }
        let Obj::ProductShape(crate::ast::obj::ProductShape::Cart(cart)) = obj else {
            return Err(tb.parse_error("release cart def expects a cart(...) constructor"));
        };
        Ok(Stmt::ReleaseAndExpand(ReleaseAndExpandStmt::ReleaseCartDefStmt(
            crate::ast::stmt::ReleaseCartDefStmt { cart, line_file: SourceLine::new(block.line, self.code_source.clone()) },
        )))
    }

    pub(in super::super) fn parse_release_regularity_axiom_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(RELEASE)?;
        tb.expect(REGULARITY_AXIOM)?;
        let args = parse_obj_list_paren(self, &mut tb)?;
        if args.len() != 1 {
            return Err(tb.parse_error(format!(
                "release regularity_axiom: expected exactly one set argument, got {}",
                args.len()
            )));
        }
        if !tb.exceed_end_of_head() {
            return Err(tb.parse_error(
                "release regularity_axiom: unexpected token after argument",
            ));
        }
        if !tb.body.is_empty() {
            return Err(tb.parse_error(
                "release regularity_axiom: does not accept an indented body",
            ));
        }
        Ok(Stmt::ReleaseAndExpand(
            ReleaseAndExpandStmt::ReleaseRegularityAxiomStmt(ReleaseRegularityAxiomStmt {
                set: args[0].clone(),
                line_file: SourceLine::new(block.line, self.code_source.clone()),
            }),
        ))
    }

    pub(in super::super) fn parse_release_axiom_of_choice_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(RELEASE)?;
        tb.expect(AXIOM_OF_CHOICE)?;
        if tb.peek() != Some(COLON) {
            return Err(tb.parse_error(
                "release axiom_of_choice: expected `release axiom_of_choice: set S:` or `release axiom_of_choice: set S`",
            ));
        }
        tb.expect(COLON)?;
        tb.expect(SET)?;
        let family = parse_obj(self, &mut tb)?;
        let has_proof_body = parse_optional_trailing_proof_colon(&mut tb, "release axiom_of_choice")?;
        let proof = if has_proof_body {
            self.push_parse_scope();
            let proof = self.parse_body_stmts(&tb.body);
            self.pop_parse_scope();
            proof?
        } else {
            if !tb.body.is_empty() {
                return Err(tb.parse_error(
                    "release axiom_of_choice: indented body requires a trailing `:` after the family",
                ));
            }
            Vec::new()
        };
        Ok(Stmt::ReleaseAndExpand(
            ReleaseAndExpandStmt::ReleaseAxiomOfChoiceStmt(ReleaseAxiomOfChoiceStmt {
                family,
                proof,
                line_file: SourceLine::new(block.line, self.code_source.clone()),
            }),
        ))
    }

    pub(in super::super) fn parse_release_zorn_lemma_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(RELEASE)?;
        tb.expect(ZORN_LEMMA)?;
        if tb.peek() != Some(COLON) {
            return Err(tb.parse_error(
                "release zorn_lemma: expected `release zorn_lemma: set S, prop P, prop U, prop M:` or the same form without a proof body",
            ));
        }
        tb.expect(COLON)?;
        tb.expect(SET)?;
        let set = parse_obj(self, &mut tb)?;
        tb.expect(COMMA)?;
        tb.expect(PROP)?;
        let prop_name = self.parse_release_atomic_prop_name(&mut tb)?;
        tb.expect(COMMA)?;
        tb.expect(PROP)?;
        let upper_bound_prop_name = self.parse_release_atomic_prop_name(&mut tb)?;
        tb.expect(COMMA)?;
        tb.expect(PROP)?;
        let maximal_prop_name = self.parse_release_atomic_prop_name(&mut tb)?;
        let has_proof_body = parse_optional_trailing_proof_colon(&mut tb, "release zorn_lemma")?;
        let proof = if has_proof_body {
            self.push_parse_scope();
            let proof = self.parse_body_stmts(&tb.body);
            self.pop_parse_scope();
            proof?
        } else {
            if !tb.body.is_empty() {
                return Err(tb.parse_error(
                    "release zorn_lemma: indented body requires a trailing `:` after the header",
                ));
            }
            Vec::new()
        };
        Ok(Stmt::ReleaseAndExpand(
            ReleaseAndExpandStmt::ReleaseZornLemmaStmt(ReleaseZornLemmaStmt {
                set,
                prop_name,
                upper_bound_prop_name,
                maximal_prop_name,
                proof,
                line_file: SourceLine::new(block.line, self.code_source.clone()),
            }),
        ))
    }

    fn parse_release_atomic_prop_name(&mut self, tb: &mut TokenBlock) -> RuntimeResult<AtomicName> {
        let name = tb.advance()?;
        if !is_simple_name(&name) {
            return Err(tb.parse_error(format!(
                "expected a simple prop name, got `{name}`"
            )));
        }
        Ok(AtomicName::plain(name))
    }
}

fn parse_optional_trailing_proof_colon(
    tb: &mut TokenBlock,
    syntax_name: &str,
) -> RuntimeResult<bool> {
    if tb.peek() == Some(COLON) {
        tb.expect(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(tb.parse_error(format!(
                "{syntax_name}: unexpected token after trailing `:`"
            )));
        }
        return Ok(true);
    }
    if tb.exceed_end_of_head() {
        return Ok(false);
    }
    Err(tb.parse_error(format!(
        "{syntax_name}: expected end of head or trailing `:`"
    )))
}
