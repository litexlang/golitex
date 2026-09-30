use super::super::keywords::{
    COLON, COMMA, EQUIVALENT_SIGN, GREATER, LEFT_PAREN, LESS, STRATEGY, STRUCT, TEMPLATE
};
use super::super::object::{is_simple_name, parse_obj};
use crate::ast::fact::QuantifierFreeFact;
use crate::ast::line_file::SourceLine;
use crate::ast::param::TypedParameterList;
use crate::ast::stmt::{
    DefStrategyStmt, DefStructStmt, DefTemplateStmt, DefineObjStmt, DefinitionStmt, Stmt, StructFieldDef,
    TemplateDefEnum, TrustBoundaryStmt
};
use crate::runtime::{Runtime, RuntimeResult};
use crate::tokenize::TokenBlock;

impl Runtime {
    // struct Name: fields [<=>: facts]
    // struct Name<typed params>: …
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
                return Err(tb.parse_error("struct definition expects at least two fields"));
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
                    // Field binders were occupied when each field line was
                    // parsed; free refs in `<=>:` resolve to those BoundNames.
                    equivalent_facts.extend(self.parse_facts_in_body(&field_tb.body)?);
                } else {
                    if seen_equivalent {
                        return Err(field_tb.parse_error("struct fields must appear before `<=>:`"));
                    }
                    if !field_tb.body.is_empty() {
                        return Err(field_tb.parse_error("struct field must fit on one line"));
                    }
                    let binding_name = field_tb
                        .advance()
                        .map_err(|_| field_tb.parse_error("struct field expects a name"))?;
                    if !is_simple_name(&binding_name) {
                        return Err(field_tb
                            .parse_error(format!("invalid struct field `{binding_name}`")));
                    }
                    if fields.iter().any(|f| f.binding.name == binding_name) {
                        return Err(field_tb
                            .parse_error(format!("duplicate struct field `{binding_name}`")));
                    }
                    let binding =
                        self.define_plain_atom_as_parse(&field_tb, binding_name)?;
                    let field_type = parse_obj(self, &mut field_tb)?;
                    if !field_tb.exceed_end_of_head() {
                        return Err(
                            field_tb.parse_error("unexpected token after struct field type")
                        );
                    }
                    fields.push(StructFieldDef {
                        binding,
                        field_type
                    });
                }
            }

            if fields.len() < 2 {
                return Err(tb.parse_error("struct definition expects at least two fields"));
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
                line_file: SourceLine::new(block.line, self.code_source.clone())
            },
        )))
    }

    // template<params [: dom…]>:
    //     <one have / trust have / obtain body>
    // Name comes from the body definition, not the header.
    pub(in super::super) fn parse_def_template_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(TEMPLATE)?;

        self.push_parse_scope();
        let parsed = (|| {
            let (template_arg_def, template_arg_dom) =
                self.parse_template_arg_header_in_angles(&mut tb)?;
            tb.expect(COLON)?;
            if !tb.exceed_end_of_head() {
                return Err(tb.parse_error("template: unexpected tokens after header `:`"));
            }
            if tb.body.len() != 1 {
                return Err(tb.parse_error(
                    "template definition expects exactly one body statement",
                ));
            }
            let body_stmt = self.parse_token_block(&tb.body[0])?;
            let template_def_stmt = template_def_enum_from_body_stmt(body_stmt, &tb)?;
            let template_name = template_def_enum_name(&template_def_stmt).ok_or_else(|| {
                tb.parse_error(
                    "template body must define exactly one object or function name",
                )
            })?;
            Ok((
                template_name,
                template_arg_def,
                template_arg_dom,
                template_def_stmt,
            ))
        })();
        self.pop_parse_scope();
        let (template_name, template_arg_def, template_arg_dom, template_def_stmt) = parsed?;

        self.define_plain_atom_as_parse(&tb, template_name.clone())?;
        Ok(Stmt::Definition(DefinitionStmt::DefTemplateStmt(
            DefTemplateStmt {
                template_name,
                template_arg_def,
                template_arg_dom,
                template_def_stmt,
                line_file: SourceLine::new(block.line, self.code_source.clone())
            },
        )))
    }

    // `<x R, y S [: dom, …]>` for template headers (dom facts optional before `>`).
    fn parse_template_arg_header_in_angles(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<(TypedParameterList, Vec<QuantifierFreeFact>)> {
        tb.expect(LESS)?;
        let mut groups = Vec::new();
        while !tb.exceed_end_of_head()
            && tb.peek() != Some(GREATER)
            && tb.peek() != Some(COLON)
        {
            groups.push(self.parse_one_typed_param_group(tb)?);
            if tb.peek() == Some(COMMA) {
                tb.advance()?;
            }
        }
        if groups.is_empty() {
            return Err(tb.parse_error(
                "template header expects at least one parameter inside `<...>`",
            ));
        }

        let mut template_arg_dom = Vec::new();
        if tb.peek() == Some(COLON) {
            tb.advance()?;
            while !tb.exceed_end_of_head() && tb.peek() != Some(GREATER) {
                template_arg_dom.push(self.parse_quantifier_free_fact_inline(tb)?);
                if tb.peek() == Some(COMMA) {
                    tb.advance()?;
                } else {
                    break;
                }
            }
        }
        tb.expect(GREATER)?;
        Ok((TypedParameterList { groups }, template_arg_dom))
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
                line_file: SourceLine::new(block.line, self.code_source.clone())
            },
        )))
    }
}

fn template_def_enum_from_body_stmt(
    body: Stmt,
    tb: &TokenBlock,
) -> RuntimeResult<TemplateDefEnum> {
    match body {
        Stmt::Definition(DefinitionStmt::DefineObj(DefineObjStmt::HaveObjInNonemptySetStmt(stmt))) => {
            Ok(TemplateDefEnum::HaveObjInNonemptySetStmt(stmt))
        }
        Stmt::Definition(DefinitionStmt::DefineObj(DefineObjStmt::HaveObjEqualStmt(stmt))) => {
            Ok(TemplateDefEnum::HaveObjEqualStmt(stmt))
        }
        Stmt::Definition(DefinitionStmt::DefineObj(DefineObjStmt::HaveObjByExistFactsStmt(stmt))) => {
            Ok(TemplateDefEnum::HaveObjByExistFactsStmt(stmt))
        }
        Stmt::Definition(DefinitionStmt::DefineObj(DefineObjStmt::HaveByReplacementAxiomStmt(stmt))) => {
            Ok(TemplateDefEnum::HaveByReplacementAxiomStmt(stmt))
        }
        Stmt::Trust(TrustBoundaryStmt::TrustHaveStmt(stmt)) => {
            Ok(TemplateDefEnum::TrustHaveStmt(stmt))
        }
        Stmt::Definition(DefinitionStmt::DefineObj(DefineObjStmt::ObtainObjFromExistFact(stmt))) => {
            Ok(TemplateDefEnum::ObtainObjFromExistFact(stmt))
        }
        Stmt::Definition(DefinitionStmt::DefineObj(DefineObjStmt::ObtainObjFromAtomicFact(stmt))) => {
            Ok(TemplateDefEnum::ObtainObjFromAtomicFact(stmt))
        }
        Stmt::Definition(DefinitionStmt::HaveFnEqualStmt(stmt)) => {
            Ok(TemplateDefEnum::HaveFnEqualStmt(stmt))
        }
        Stmt::Definition(DefinitionStmt::HaveFnEqualCaseByCaseStmt(stmt)) => {
            Ok(TemplateDefEnum::HaveFnEqualCaseByCaseStmt(stmt))
        }
        Stmt::Definition(DefinitionStmt::HaveFnByInducStmt(stmt)) => {
            Ok(TemplateDefEnum::HaveFnByInducStmt(stmt))
        }
        Stmt::Definition(DefinitionStmt::HaveFnByForallExistUniqueStmt(stmt)) => {
            Ok(TemplateDefEnum::HaveFnByForallExistUniqueStmt(stmt))
        }
        _ => Err(tb.parse_error(
            "template body only supports `have` / `trust have` / `obtain` definition statements",
        ))
    }
}

fn template_def_enum_name(body: &TemplateDefEnum) -> Option<String> {
    match body {
        TemplateDefEnum::HaveObjInNonemptySetStmt(stmt) => first_typed_param_name(&stmt.param_def),
        TemplateDefEnum::HaveObjEqualStmt(stmt) => first_typed_param_name(&stmt.param_def),
        TemplateDefEnum::HaveObjByExistFactsStmt(stmt) => first_typed_param_name(&stmt.param_def),
        TemplateDefEnum::HaveByReplacementAxiomStmt(stmt) => Some(stmt.name.name.clone()),
        TemplateDefEnum::TrustHaveStmt(stmt) => first_typed_param_name(&stmt.param_def),
        TemplateDefEnum::ObtainObjFromExistFact(stmt) => stmt.equal_tos.first().map(|bound| bound.name.clone()),
        TemplateDefEnum::ObtainObjFromAtomicFact(stmt) => stmt.equal_tos.first().map(|bound| bound.name.clone()),
        TemplateDefEnum::HaveFnEqualStmt(stmt) => Some(stmt.name.clone()),
        TemplateDefEnum::HaveFnEqualCaseByCaseStmt(stmt) => Some(stmt.name.clone()),
        TemplateDefEnum::HaveFnByInducStmt(stmt) => Some(stmt.name.clone()),
        TemplateDefEnum::HaveFnByForallExistUniqueStmt(stmt) => Some(stmt.name.clone())
    }
}

fn first_typed_param_name(param_def: &TypedParameterList) -> Option<String> {
    param_def
        .groups
        .first()
        .and_then(|g| g.params.first())
        .map(|p| p.name.clone())
}
