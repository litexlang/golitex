use super::super::keywords::{BY, COLON, COMMA, EQUAL, PROP, REPLACEMENT_AXIOM, SET};
use super::super::object::parse_obj;
use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::ast::param::{ParamType, TypedParameterList};
use crate::new_pipeline::ast::stmt::{
    DefinitionStmt, HaveByReplacementAxiomStmt, HaveObjByExistFactsStmt, HaveObjEqualStmt,
    HaveObjInNonemptySetOrParamTypeStmt, Stmt,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

impl Runtime {
    // have x T | have x, y T | have x = obj | have x T: facts
    // | have Img set by replacement_axiom: prop P, set A
    pub(in super::super) fn parse_have_obj_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.advance()?; // `have` already matched by dispatch

        self.push_parse_scope();
        let result = (|| {
            let param_def = self.parse_typed_param_list_until_eq_colon_or_end(&mut tb)?;
            let identifiers: Vec<crate::new_pipeline::ast::names::BoundName> = param_def
                .groups
                .iter()
                .flat_map(|g| g.params.iter().cloned())
                .collect();

            if tb.peek() == Some(BY) {
                return self.parse_have_by_replacement_axiom_tail(
                    &mut tb,
                    param_def,
                    identifiers,
                );
            }

            if tb.peek() == Some(COLON) {
                tb.expect(COLON)?;
                if !tb.exceed_end_of_head() {
                    return Err(
                        tb.parse_error("`have ...:` facts must be written in an indented body")
                    );
                }
                let mut facts = Vec::new();
                for child in &tb.body {
                    let mut c = child.clone();
                    facts.push(self.parse_quantifier_free_fact_top(&mut c)?);
                }
                return Ok(HaveObjKind::ByExist(param_def, facts, identifiers));
            }

            if tb.peek() == Some(EQUAL) {
                tb.expect(EQUAL)?;
                let mut objs_equal_to = vec![parse_obj(self, &mut tb)?];
                while tb.peek() == Some(COMMA) {
                    tb.advance()?;
                    objs_equal_to.push(parse_obj(self, &mut tb)?);
                }
                if !tb.exceed_end_of_head() {
                    return Err(tb.parse_error("trailing tokens after have equal value"));
                }
                if !tb.body.is_empty() {
                    return Err(tb.parse_error("`have ... =` cannot have an indented body"));
                }
                return Ok(HaveObjKind::Equal(param_def, objs_equal_to, identifiers));
            }

            if !tb.exceed_end_of_head() {
                return Err(tb.parse_error(
                    "have: expected `=`, `:`, `by replacement_axiom:`, or end of header after parameters",
                ));
            }
            if !tb.body.is_empty() {
                return Err(tb.parse_error("have without `=`/`:` cannot have an indented body"));
            }
            Ok(HaveObjKind::InSet(param_def, identifiers))
        })();
        self.pop_parse_scope();

        match result? {
            HaveObjKind::InSet(param_def, identifiers) => {
                for identifier in &identifiers {
                    self.occupy_bound_name_as_parse(block, identifier)?;
                }
                Ok(Stmt::Definition(DefinitionStmt::HaveObjInNonemptySetStmt(
                    HaveObjInNonemptySetOrParamTypeStmt {
                        param_def,
                        line_file: LineFile::new(block.line, block.source_path.clone()),
                    },
                )))
            }
            HaveObjKind::Equal(param_def, objs_equal_to, identifiers) => {
                for identifier in &identifiers {
                    self.occupy_bound_name_as_parse(block, identifier)?;
                }
                Ok(Stmt::Definition(DefinitionStmt::HaveObjEqualStmt(
                    HaveObjEqualStmt {
                        param_def,
                        objs_equal_to,
                        line_file: LineFile::new(block.line, block.source_path.clone()),
                    },
                )))
            }
            HaveObjKind::ByExist(param_def, facts, identifiers) => {
                for identifier in &identifiers {
                    self.occupy_bound_name_as_parse(block, identifier)?;
                }
                Ok(Stmt::Definition(DefinitionStmt::HaveObjByExistFactsStmt(
                    HaveObjByExistFactsStmt {
                        param_def,
                        facts,
                        line_file: LineFile::new(block.line, block.source_path.clone()),
                    },
                )))
            }
            HaveObjKind::ByReplacementAxiom(name, prop_name, source_set) => {
                self.occupy_bound_name_as_parse(block, &name)?;
                Ok(Stmt::Definition(
                    DefinitionStmt::HaveByReplacementAxiomStmt(HaveByReplacementAxiomStmt {
                        name,
                        prop_name,
                        source_set,
                        line_file: LineFile::new(block.line, block.source_path.clone()),
                    }),
                ))
            }
        }
    }

    // `by replacement_axiom: prop P, set A` after a single `name set` binding.
    // Same tagged-arg style as `by axiom_of_choice: set F` / `by zorn_lemma: …`.
    fn parse_have_by_replacement_axiom_tail(
        &mut self,
        tb: &mut TokenBlock,
        param_def: TypedParameterList,
        identifiers: Vec<crate::new_pipeline::ast::names::BoundName>,
    ) -> RuntimeResult<HaveObjKind> {
        tb.expect(BY)?;
        tb.expect(REPLACEMENT_AXIOM)?;
        if tb.peek() != Some(COLON) {
            return Err(tb.parse_error(
                "expected `by replacement_axiom: prop P, set A`",
            ));
        }
        tb.expect(COLON)?;
        tb.expect(PROP)?;
        let prop_name = self.parse_prop_name(tb)?;
        tb.expect(COMMA)?;
        tb.expect(SET)?;
        let source_set = parse_obj(self, tb)?;
        if !tb.exceed_end_of_head() {
            return Err(tb.parse_error(
                "trailing tokens after `have … by replacement_axiom: prop P, set A`",
            ));
        }
        if !tb.body.is_empty() {
            return Err(tb.parse_error(
                "`have … by replacement_axiom` cannot have an indented body",
            ));
        }
        if identifiers.len() != 1 {
            return Err(tb.parse_error(
                "`have … by replacement_axiom` expects exactly one name",
            ));
        }
        if param_def.groups.len() != 1
            || !matches!(param_def.groups[0].param_type, ParamType::Set(_))
        {
            return Err(tb.parse_error(
                "`have … by replacement_axiom` expects `name set`",
            ));
        }
        Ok(HaveObjKind::ByReplacementAxiom(
            identifiers.into_iter().next().unwrap(),
            prop_name,
            source_set,
        ))
    }
}

enum HaveObjKind {
    InSet(
        crate::new_pipeline::ast::param::TypedParameterList,
        Vec<crate::new_pipeline::ast::names::BoundName>,
    ),
    Equal(
        crate::new_pipeline::ast::param::TypedParameterList,
        Vec<crate::new_pipeline::ast::obj::Obj>,
        Vec<crate::new_pipeline::ast::names::BoundName>,
    ),
    ByExist(
        crate::new_pipeline::ast::param::TypedParameterList,
        Vec<crate::new_pipeline::ast::fact::QuantifierFreeFact>,
        Vec<crate::new_pipeline::ast::names::BoundName>,
    ),
    ByReplacementAxiom(
        crate::new_pipeline::ast::names::BoundName,
        crate::new_pipeline::ast::names::AtomicName,
        crate::new_pipeline::ast::obj::Obj,
    ),
}
