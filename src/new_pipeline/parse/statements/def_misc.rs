use super::super::keywords::{COLON, EQUIVALENT_SIGN, LEFT_PAREN, LESS, SETTING, STRATEGY, STRUCT};
use super::super::object::{is_simple_name, parse_obj};
use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::ast::stmt::{
    DefSettingStmt, DefStrategyStmt, DefStructStmt, DefinitionStmt, Stmt, StructFieldDef,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

impl Runtime {
    // setting Name(params) [: body facts]
    pub(in super::super) fn parse_def_setting_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(SETTING)?;
        let name = tb
            .advance()
            .map_err(|_| tb.parse_error("`setting` expects a name"))?;
        if !is_simple_name(&name) {
            return Err(tb.parse_error(format!("invalid setting name `{name}`")));
        }

        self.push_parse_scope();
        let result = (|| {
            let param_def = self.parse_typed_param_list_in_parens(&mut tb)?;
            let dom_facts = if tb.peek() == Some(COLON) {
                tb.expect(COLON)?;
                if !tb.exceed_end_of_head() {
                    return Err(tb.parse_error("setting: unexpected tokens after `:` in header"));
                }
                self.parse_facts_in_body(&tb.body)?
            } else {
                if !tb.exceed_end_of_head() {
                    return Err(
                        tb.parse_error("setting: expected `:` or end of header after `(...)`")
                    );
                }
                if !tb.body.is_empty() {
                    return Err(tb.parse_error("setting without `:` cannot have an indented body"));
                }
                Vec::new()
            };
            Ok((param_def, dom_facts))
        })();
        self.pop_parse_scope();
        let (param_def, dom_facts) = result?;

        self.define_plain_atom_as_parse(&tb, name.clone())?;
        Ok(Stmt::Definition(DefinitionStmt::DefSettingStmt(
            DefSettingStmt {
                name,
                param_def,
                dom_facts,
                line_file: LineFile::new(block.line, block.source_path.clone()),
            },
        )))
    }

    // struct Name: fields [<=>: facts]
    // struct Name<typed params>: …  (setting refs inside `<>` still deferred)
    pub(in super::super) fn parse_def_struct_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(STRUCT)?;
        let name = tb
            .advance()
            .map_err(|_| tb.parse_error("`struct` expects a name"))?;
        if !is_simple_name(&name) {
            return Err(tb.parse_error(format!("invalid struct name `{name}`")));
        }

        self.push_parse_scope();
        let result = (|| {
            let param_def_with_dom = if tb.peek() == Some(LESS) {
                let params = self.parse_typed_param_list_in_angles(&mut tb)?;
                Some((params, Vec::new()))
            } else if tb.peek() == Some(LEFT_PAREN) {
                return Err(tb.parse_error(
                    "struct parameters use `<...>` (e.g. `struct Pair<A set>:`), not `(...)`",
                ));
            } else {
                None
            };

            tb.expect(COLON)?;
            if !tb.exceed_end_of_head() {
                return Err(tb.parse_error("struct: unexpected tokens after `:`"));
            }
            if tb.body.is_empty() {
                return Err(tb.parse_error("struct definition expects at least one field"));
            }

            let mut fields: Vec<StructFieldDef> = Vec::new();
            let mut equivalent_facts = Vec::new();
            let mut seen_equivalent = false;

            for child in &tb.body {
                let mut field_tb = child.clone();
                if field_tb.peek() == Some(EQUIVALENT_SIGN) {
                    if seen_equivalent {
                        return Err(field_tb
                            .parse_error("struct definition can only have one `<=>:` block"));
                    }
                    seen_equivalent = true;
                    field_tb.expect(EQUIVALENT_SIGN)?;
                    field_tb.expect(COLON)?;
                    if !field_tb.exceed_end_of_head() {
                        return Err(
                            field_tb.parse_error("`<=>:` in struct must not have inline facts")
                        );
                    }
                    for f in &fields {
                        self.define_plain_atom_as_parse(&field_tb, f.binding.clone())?;
                    }
                    equivalent_facts.extend(self.parse_facts_in_body(&field_tb.body)?);
                } else {
                    if seen_equivalent {
                        return Err(field_tb.parse_error("struct fields must appear before `<=>:`"));
                    }
                    if !field_tb.body.is_empty() {
                        return Err(field_tb.parse_error("struct field must fit on one line"));
                    }
                    let binding = field_tb
                        .advance()
                        .map_err(|_| field_tb.parse_error("struct field expects a name"))?;
                    if !is_simple_name(&binding) {
                        return Err(
                            field_tb.parse_error(format!("invalid struct field `{binding}`"))
                        );
                    }
                    let field_type = parse_obj(self, &mut field_tb)?;
                    if !field_tb.exceed_end_of_head() {
                        return Err(
                            field_tb.parse_error("unexpected token after struct field type")
                        );
                    }
                    if fields.iter().any(|f| f.binding == binding) {
                        return Err(
                            field_tb.parse_error(format!("duplicate struct field `{binding}`"))
                        );
                    }
                    fields.push(StructFieldDef {
                        binding,
                        field_type,
                    });
                }
            }

            if fields.is_empty() {
                return Err(tb.parse_error("struct definition expects at least one field"));
            }
            Ok((param_def_with_dom, fields, equivalent_facts))
        })();
        self.pop_parse_scope();
        let (param_def_with_dom, fields, equivalent_facts) = result?;

        self.define_plain_atom_as_parse(&tb, name.clone())?;
        Ok(Stmt::Definition(DefinitionStmt::DefStructStmt(
            DefStructStmt {
                name,
                param_def_with_dom,
                fields,
                equivalent_facts,
                line_file: LineFile::new(block.line, block.source_path.clone()),
            },
        )))
    }

    pub(in super::super) fn parse_def_template_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        Err(block.parse_error("template: not wired yet in new_pipeline (parse → AST deferred)"))
    }

    // strategy Name:
    //   ? forall …
    //   <proof…>
    pub(in super::super) fn parse_def_strategy_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(STRATEGY)?;
        let name = tb
            .advance()
            .map_err(|_| tb.parse_error("`strategy` expects a name"))?;
        if !is_simple_name(&name) {
            return Err(tb.parse_error(format!("invalid strategy name `{name}`")));
        }
        tb.expect_colon_end_of_header()?;
        if tb.body.is_empty() {
            return Err(tb.parse_error(
                "strategy: expects a `? forall ...` goal block and optional proof body",
            ));
        }
        let mut goal = tb.body[0].clone();
        let forall_fact = self.parse_goal_forall_fact(&mut goal, "strategy")?;
        let proof_blocks = &tb.body[1..];
        let prove_process =
            self.with_forall_params_occupied(&forall_fact.typed_parameters, &tb, |this| {
                this.parse_body_stmts(proof_blocks)
            })?;
        self.define_plain_atom_as_parse(&tb, name.clone())?;
        Ok(Stmt::Definition(DefinitionStmt::DefStrategyStmt(
            DefStrategyStmt {
                name,
                forall_fact,
                prove_process,
                line_file: LineFile::new(block.line, block.source_path.clone()),
            },
        )))
    }
}
