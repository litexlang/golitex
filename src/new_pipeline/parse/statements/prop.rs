use super::super::keywords::{ABSTRACT_PROP, COLON, PROP};
use super::super::object::is_simple_name;
use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::ast::stmt::{DefAbstractPropStmt, DefPropStmt, DefinitionStmt, Stmt};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

impl Runtime {
    // prop Name(params): <body facts>
    pub(in super::super) fn parse_def_prop_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(PROP)?;
        let name = tb
            .advance()
            .map_err(|_| tb.parse_error("`prop` expects a name"))?;
        if !is_simple_name(&name) {
            return Err(tb.parse_error(format!("invalid prop name `{name}`")));
        }

        self.push_parse_scope();
        let result = (|| {
            let typed_parameters = self.parse_typed_param_list_in_parens(&mut tb)?;
            let iff_facts = if tb.peek() == Some(COLON) {
                tb.expect(COLON)?;
                if !tb.exceed_end_of_head() {
                    return Err(tb.parse_error("prop: unexpected tokens after `:` in header"));
                }
                self.parse_facts_in_body(&tb.body)?
            } else {
                if !tb.exceed_end_of_head() {
                    return Err(tb.parse_error("prop: expected `:` or end of header after `(...)`"));
                }
                if !tb.body.is_empty() {
                    return Err(tb.parse_error("prop without `:` cannot have an indented body"));
                }
                Vec::new()
            };
            Ok((typed_parameters, iff_facts))
        })();
        self.pop_parse_scope();
        let (typed_parameters, iff_facts) = result?;

        self.define_plain_atom_as_parse(&tb, name.clone())?;
        Ok(Stmt::Definition(DefinitionStmt::DefPropStmt(DefPropStmt {
            name,
            typed_parameters,
            iff_facts,
            line_file: LineFile::new(block.line, block.source_path.clone()),
        })))
    }

    // abstract_prop Name(params)
    pub(in super::super) fn parse_def_abstract_prop_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(ABSTRACT_PROP)?;
        let name = tb
            .advance()
            .map_err(|_| tb.parse_error("`abstract_prop` expects a name"))?;
        if !is_simple_name(&name) {
            return Err(tb.parse_error(format!("invalid abstract_prop name `{name}`")));
        }

        self.push_parse_scope();
        let params = self.parse_name_list_in_parens(&mut tb);
        self.pop_parse_scope();
        let params = params?;

        if !tb.exceed_end_of_head() {
            return Err(tb.parse_error("abstract_prop: unexpected tokens after `(...)`"));
        }
        if !tb.body.is_empty() {
            return Err(tb.parse_error("abstract_prop cannot have an indented body"));
        }

        self.define_plain_atom_as_parse(&tb, name.clone())?;
        Ok(Stmt::Definition(DefinitionStmt::DefAbstractPropStmt(
            DefAbstractPropStmt {
                name,
                params,
                line_file: LineFile::new(block.line, block.source_path.clone()),
            },
        )))
    }
}
