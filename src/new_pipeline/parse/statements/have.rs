use super::super::keywords::{COLON, EQUAL};
use super::super::object::parse_obj;
use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::ast::obj::Identifier;
use crate::new_pipeline::ast::stmt::{
    DefinitionStmt, HaveObjByExistFactsStmt, HaveObjEqualStmt, HaveObjInNonemptySetOrParamTypeStmt,
    Stmt,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

impl Runtime {
    // have x T | have x, y T | have x = obj | have x T: facts
    pub(in super::super) fn parse_have_obj_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.advance()?; // `have` already matched by dispatch

        self.push_parse_scope();
        let result = (|| {
            let param_def = self.parse_typed_param_list_until_eq_colon_or_end(&mut tb)?;
            let identifiers: Vec<Identifier> = param_def
                .groups
                .iter()
                .flat_map(|g| g.params.iter().cloned())
                .collect();

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
                while tb.peek() == Some(super::super::keywords::COMMA) {
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
                return Err(
                    tb.parse_error("have: expected `=`, `:`, or end of header after parameters")
                );
            }
            if !tb.body.is_empty() {
                return Err(tb.parse_error("have without `=`/`:` cannot have an indented body"));
            }
            Ok(HaveObjKind::InSet(param_def, identifiers))
        })();
        self.pop_parse_scope();

        match result? {
            HaveObjKind::InSet(param_def, identifiers) => {
                for identifier in identifiers {
                    self.occupy_plain_atom_as_parse(
                        block,
                        identifier.name,
                        identifier.identifier_id,
                    )?;
                }
                Ok(Stmt::Definition(DefinitionStmt::HaveObjInNonemptySetStmt(
                    HaveObjInNonemptySetOrParamTypeStmt {
                        param_def,
                        line_file: LineFile::new(block.line, block.source_path.clone()),
                    },
                )))
            }
            HaveObjKind::Equal(param_def, objs_equal_to, identifiers) => {
                for identifier in identifiers {
                    self.occupy_plain_atom_as_parse(
                        block,
                        identifier.name,
                        identifier.identifier_id,
                    )?;
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
                for identifier in identifiers {
                    self.occupy_plain_atom_as_parse(
                        block,
                        identifier.name,
                        identifier.identifier_id,
                    )?;
                }
                Ok(Stmt::Definition(DefinitionStmt::HaveObjByExistFactsStmt(
                    HaveObjByExistFactsStmt {
                        param_def,
                        facts,
                        line_file: LineFile::new(block.line, block.source_path.clone()),
                    },
                )))
            }
        }
    }
}

enum HaveObjKind {
    InSet(
        crate::new_pipeline::ast::param::TypedParameterList,
        Vec<Identifier>,
    ),
    Equal(
        crate::new_pipeline::ast::param::TypedParameterList,
        Vec<crate::new_pipeline::ast::obj::Obj>,
        Vec<Identifier>,
    ),
    ByExist(
        crate::new_pipeline::ast::param::TypedParameterList,
        Vec<crate::new_pipeline::ast::fact::QuantifierFreeFact>,
        Vec<Identifier>,
    ),
}
