//! Object, tuple, Cartesian, sequence, and matrix `have` definitions.

use crate::prelude::*;

impl Runtime {
    pub fn parse_have_obj_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(HAVE)?;
        let has_fact_body = self.have_obj_stmt_has_fact_body(tb)?;
        let binding_kind = if has_fact_body {
            BindingScope::LocalBinder
        } else {
            BindingScope::DeclaredObject
        };
        let param_defs = self.parse_have_obj_param_defs_until_header_delimiter(tb, binding_kind)?;
        if param_defs.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "have expects at least one param type pair".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        let param_defs = ParamDefWithType::new(param_defs);
        let have_param_names = param_defs.collect_param_names();

        if has_fact_body {
            let facts_result = (|| -> Result<Vec<QuantifierFreeFact>, RuntimeError> {
                tb.skip_token(COLON)?;
                if !tb.exceed_end_of_head() {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "`have ...:` facts must be written in an indented body".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                self.parse_quantifier_free_facts_in_body(tb)
            })();
            if !have_param_names.is_empty() {
                self.end_parsing_scope(&have_param_names);
            }
            let facts = facts_result?;
            self.register_collected_param_names_for_def_parse(
                &have_param_names,
                tb.line_file.clone(),
            )?;
            self.register_local_existing_identifier_bindings_for_parse(
                &param_defs.collect_param_bindings(),
                tb.line_file.clone(),
            )?;
            return Ok(
                HaveObjByExistFactsStmt::new(param_defs, facts, tb.line_file.clone()).into(),
            );
        }

        let register_result = self
            .register_collected_param_names_for_def_parse(&have_param_names, tb.line_file.clone());
        if register_result.is_err() && !have_param_names.is_empty() {
            self.end_parsing_scope(&have_param_names);
        }
        register_result?;

        if tb.current().map(|t| t != EQUAL).unwrap_or(true) {
            if !have_param_names.is_empty() {
                self.end_parsing_scope(&have_param_names);
            }
            self.register_local_existing_identifier_bindings_for_parse(
                &param_defs.collect_param_bindings(),
                tb.line_file.clone(),
            )?;
            Ok(HaveObjInNonemptySetOrParamTypeStmt::new(param_defs, tb.line_file.clone()).into())
        } else {
            tb.skip_token(EQUAL)?;
            let objs_result = (|| -> Result<Vec<Obj>, RuntimeError> {
                let mut objs_equal_to = vec![self.parse_obj(tb)?];
                while matches!(tb.current(), Ok(t) if t == COMMA) {
                    tb.skip_token(COMMA)?;
                    objs_equal_to.push(self.parse_obj(tb)?);
                }
                Ok(objs_equal_to)
            })();
            self.end_parsing_scope(&have_param_names);
            let objs_equal_to = objs_result?;
            self.register_local_existing_identifier_bindings_for_parse(
                &param_defs.collect_param_bindings(),
                tb.line_file.clone(),
            )?;
            Ok(HaveObjEqualStmt::new(param_defs, objs_equal_to, tb.line_file.clone()).into())
        }
    }

    fn have_obj_stmt_has_fact_body(&mut self, tb: &TokenBlock) -> Result<bool, RuntimeError> {
        let mut dry_tb = tb.clone();
        self.run_in_local_parsing_time_name_scope(|this| {
            let param_defs = this.parse_have_obj_param_defs_until_header_delimiter(
                &mut dry_tb,
                BindingScope::DeclaredObject,
            )?;
            if param_defs.is_empty() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "have expects at least one param type pair".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            Ok(dry_tb.current_token_is_equal_to(COLON))
        })
    }

    fn parse_have_obj_param_defs_until_header_delimiter(
        &mut self,
        tb: &mut TokenBlock,
        binding_scope: BindingScope,
    ) -> Result<Vec<ParamGroupWithParamType>, RuntimeError> {
        let mut param_defs: Vec<ParamGroupWithParamType> = vec![];
        loop {
            match tb.current() {
                Ok(t) if t == EQUAL || t == COLON => break,
                Err(_) => break,
                Ok(_) => {}
            }
            param_defs
                .push(self.parse_param_def_with_param_type_and_skip_comma(tb, binding_scope)?);
        }
        Ok(param_defs)
    }

    pub fn parse_have_tuple_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(HAVE)?;
        tb.skip_token(TUPLE)?;
        let name = parse_have_tuple_or_cart_name(tb)?;
        let symbol_binding = self.allocate_declared_symbol_binding(name.clone())?;
        skip_have_indexed_definition_keyword(tb, "have tuple")?;
        let index_name = parse_have_tuple_or_cart_name(tb)?;
        tb.skip_token(LESS_EQUAL)?;
        let dimension = self.parse_obj(tb)?;
        tb.skip_token(COMMA)?;

        let index_names = vec![index_name.clone()];
        let ((lhs, value), index_bindings) = self.parse_in_local_free_param_scope_with_bindings(
            BindingScope::LocalBinder,
            &index_names,
            tb.line_file.clone(),
            |this| {
                let lhs = this.parse_obj(tb)?;
                tb.skip_token(EQUAL)?;
                let value = this.parse_obj(tb)?;
                if !tb.exceed_end_of_head() {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "unexpected token after have tuple value expression".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                Ok((lhs, value))
            },
        )?;
        validate_have_tuple_lhs(&lhs, &name, &index_name, tb.line_file.clone())?;

        self.register_local_existing_identifier_bindings_for_parse(
            std::slice::from_ref(&symbol_binding),
            tb.line_file.clone(),
        )?;
        Ok(HaveTupleStmt::new(
            symbol_binding,
            index_bindings[0].clone(),
            dimension,
            value,
            tb.line_file.clone(),
        )
        .into())
    }

    pub fn parse_have_cart_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(HAVE)?;
        tb.skip_token(CART)?;
        let name = parse_have_tuple_or_cart_name(tb)?;
        let symbol_binding = self.allocate_declared_symbol_binding(name.clone())?;
        skip_have_indexed_definition_keyword(tb, "have cart")?;
        let index_name = parse_have_tuple_or_cart_name(tb)?;
        tb.skip_token(LESS_EQUAL)?;
        let dimension = self.parse_obj(tb)?;
        tb.skip_token(COMMA)?;

        let index_names = vec![index_name.clone()];
        let ((lhs, value), index_bindings) = self.parse_in_local_free_param_scope_with_bindings(
            BindingScope::LocalBinder,
            &index_names,
            tb.line_file.clone(),
            |this| {
                let lhs = this.parse_obj(tb)?;
                tb.skip_token(EQUAL)?;
                let value = this.parse_obj(tb)?;
                if !tb.exceed_end_of_head() {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "unexpected token after have cart value expression".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                Ok((lhs, value))
            },
        )?;
        validate_have_cart_lhs(&lhs, &name, &index_name, tb.line_file.clone())?;

        self.register_local_existing_identifier_bindings_for_parse(
            std::slice::from_ref(&symbol_binding),
            tb.line_file.clone(),
        )?;
        Ok(HaveCartStmt::new(
            symbol_binding,
            index_bindings[0].clone(),
            dimension,
            value,
            tb.line_file.clone(),
        )
        .into())
    }

    pub fn parse_have_seq_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(HAVE)?;
        tb.skip_token(SEQ)?;
        let name = parse_have_tuple_or_cart_name(tb)?;
        let symbol_binding = self.allocate_declared_symbol_binding(name.clone())?;
        let seq_set = match self.parse_obj(tb)? {
            Obj::SeqSet(seq_set) => seq_set,
            _ => {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "have seq expects typed header `seq(S)`".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
        };
        skip_have_indexed_definition_keyword(tb, "have seq")?;
        let index_name = parse_have_tuple_or_cart_name(tb)?;
        tb.skip_token(COMMA)?;

        let index_names = vec![index_name.clone()];
        let ((lhs, value), index_bindings) = self.parse_in_local_free_param_scope_with_bindings(
            BindingScope::LocalBinder,
            &index_names,
            tb.line_file.clone(),
            |this| {
                let lhs = this.parse_obj(tb)?;
                tb.skip_token(EQUAL)?;
                let value = this.parse_obj(tb)?;
                if !tb.exceed_end_of_head() {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "unexpected token after have seq value expression".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                Ok((lhs, value))
            },
        )?;
        validate_have_seq_lhs(&lhs, &name, &index_name, tb.line_file.clone())?;

        self.register_local_existing_identifier_bindings_for_parse(
            std::slice::from_ref(&symbol_binding),
            tb.line_file.clone(),
        )?;
        Ok(HaveSeqStmt::new(
            symbol_binding,
            seq_set,
            index_bindings[0].clone(),
            value,
            tb.line_file.clone(),
        )
        .into())
    }

    pub fn parse_have_finite_seq_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        tb.skip_token(HAVE)?;
        tb.skip_token(FINITE_SEQ)?;
        let name = parse_have_tuple_or_cart_name(tb)?;
        let symbol_binding = self.allocate_declared_symbol_binding(name.clone())?;
        let finite_seq_set = match self.parse_obj(tb)? {
            Obj::FiniteSeqSet(finite_seq_set) => finite_seq_set,
            _ => {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "have finite_seq expects typed header `finite_seq(S, n)`".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
        };
        skip_have_indexed_definition_keyword(tb, "have finite_seq")?;
        let index_name = parse_have_tuple_or_cart_name(tb)?;
        tb.skip_token(LESS_EQUAL)?;
        let bound = self.parse_obj(tb)?;
        tb.skip_token(COMMA)?;

        let index_names = vec![index_name.clone()];
        let ((lhs, value), index_bindings) = self.parse_in_local_free_param_scope_with_bindings(
            BindingScope::LocalBinder,
            &index_names,
            tb.line_file.clone(),
            |this| {
                let lhs = this.parse_obj(tb)?;
                tb.skip_token(EQUAL)?;
                let value = this.parse_obj(tb)?;
                if !tb.exceed_end_of_head() {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "unexpected token after have finite_seq value expression".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                Ok((lhs, value))
            },
        )?;
        validate_have_seq_lhs(&lhs, &name, &index_name, tb.line_file.clone())?;

        self.register_local_existing_identifier_bindings_for_parse(
            std::slice::from_ref(&symbol_binding),
            tb.line_file.clone(),
        )?;
        Ok(HaveFiniteSeqStmt::new(
            symbol_binding,
            finite_seq_set,
            index_bindings[0].clone(),
            bound,
            value,
            tb.line_file.clone(),
        )
        .into())
    }

    pub fn parse_have_matrix_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(HAVE)?;
        tb.skip_token(MATRIX)?;
        let name = parse_have_tuple_or_cart_name(tb)?;
        let symbol_binding = self.allocate_declared_symbol_binding(name.clone())?;
        let matrix_set = match self.parse_obj(tb)? {
            Obj::MatrixSet(matrix_set) => matrix_set,
            _ => {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "have matrix expects typed header `matrix(S, rows, cols)`".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
        };
        skip_have_indexed_definition_keyword(tb, "have matrix")?;
        let row_index_name = parse_have_tuple_or_cart_name(tb)?;
        tb.skip_token(LESS_EQUAL)?;
        let row_bound = self.parse_obj(tb)?;
        tb.skip_token(COMMA)?;
        let col_index_name = parse_have_tuple_or_cart_name(tb)?;
        tb.skip_token(LESS_EQUAL)?;
        let col_bound = self.parse_obj(tb)?;
        tb.skip_token(COMMA)?;

        let index_names = vec![row_index_name.clone(), col_index_name.clone()];
        let ((lhs, value), index_bindings) = self.parse_in_local_free_param_scope_with_bindings(
            BindingScope::LocalBinder,
            &index_names,
            tb.line_file.clone(),
            |this| {
                let lhs = this.parse_obj(tb)?;
                tb.skip_token(EQUAL)?;
                let value = this.parse_obj(tb)?;
                if !tb.exceed_end_of_head() {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "unexpected token after have matrix value expression".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                Ok((lhs, value))
            },
        )?;
        validate_have_matrix_lhs(
            &lhs,
            &name,
            &row_index_name,
            &col_index_name,
            tb.line_file.clone(),
        )?;

        self.register_local_existing_identifier_bindings_for_parse(
            std::slice::from_ref(&symbol_binding),
            tb.line_file.clone(),
        )?;
        Ok(HaveMatrixStmt::new(
            symbol_binding,
            matrix_set,
            index_bindings[0].clone(),
            row_bound,
            index_bindings[1].clone(),
            col_bound,
            value,
            tb.line_file.clone(),
        )
        .into())
    }
}

fn parse_have_tuple_or_cart_name(tb: &mut TokenBlock) -> Result<String, RuntimeError> {
    let name = tb.advance()?;
    is_valid_litex_name(&name).map_err(|msg| {
        RuntimeError::from(ParseRuntimeError(
            RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone()),
        ))
    })?;
    Ok(name)
}

fn skip_have_indexed_definition_keyword(
    tb: &mut TokenBlock,
    stmt_name: &str,
) -> Result<(), RuntimeError> {
    if tb.current_token_is_equal_to(FOR) {
        return tb.skip_token(FOR);
    }
    Err(RuntimeError::from(ParseRuntimeError(
        RuntimeErrorStruct::new_with_msg_and_line_file(
            format!("{} expects `for` before the index binder", stmt_name),
            tb.line_file.clone(),
        ),
    )))
}

fn validate_have_tuple_lhs(
    lhs: &Obj,
    name: &str,
    index_name: &str,
    line_file: LineFile,
) -> Result<(), RuntimeError> {
    let Obj::ObjAtIndex(indexed) = lhs else {
        return Err(have_tuple_or_cart_parse_error(
            "have tuple expects left side `name[index]`",
            line_file,
        ));
    };
    if !is_identifier_named(indexed.obj.as_ref(), name) {
        return Err(have_tuple_or_cart_parse_error(
            "have tuple left side must index the tuple being defined",
            line_file,
        ));
    }
    if !is_tuple_index_named(indexed.index.as_ref(), index_name) {
        return Err(have_tuple_or_cart_parse_error(
            "have tuple left side must use the bound index",
            line_file,
        ));
    }
    Ok(())
}

fn validate_have_cart_lhs(
    lhs: &Obj,
    name: &str,
    index_name: &str,
    line_file: LineFile,
) -> Result<(), RuntimeError> {
    let Obj::Proj(proj) = lhs else {
        return Err(have_tuple_or_cart_parse_error(
            "have cart expects left side `proj(name, index)`",
            line_file,
        ));
    };
    if !is_identifier_named(proj.set.as_ref(), name) {
        return Err(have_tuple_or_cart_parse_error(
            "have cart left side must project the cart being defined",
            line_file,
        ));
    }
    if !is_cart_index_named(proj.dim.as_ref(), index_name) {
        return Err(have_tuple_or_cart_parse_error(
            "have cart left side must use the bound index",
            line_file,
        ));
    }
    Ok(())
}

fn validate_have_seq_lhs(
    lhs: &Obj,
    name: &str,
    index_name: &str,
    line_file: LineFile,
) -> Result<(), RuntimeError> {
    let Obj::FnObj(fn_obj) = lhs else {
        return Err(have_tuple_or_cart_parse_error(
            "have seq expects left side `name(index)`",
            line_file,
        ));
    };
    if !is_fn_head_identifier_named(fn_obj.head.as_ref(), name) {
        return Err(have_tuple_or_cart_parse_error(
            "have seq left side must apply the sequence being defined",
            line_file,
        ));
    }
    if fn_obj.body.len() != 1 || fn_obj.body[0].len() != 1 {
        return Err(have_tuple_or_cart_parse_error(
            "have seq left side must use exactly one index",
            line_file,
        ));
    }
    if !is_fn_set_index_named(fn_obj.body[0][0].as_ref(), index_name) {
        return Err(have_tuple_or_cart_parse_error(
            "have seq left side must use the bound index",
            line_file,
        ));
    }
    Ok(())
}

fn validate_have_matrix_lhs(
    lhs: &Obj,
    name: &str,
    row_index_name: &str,
    col_index_name: &str,
    line_file: LineFile,
) -> Result<(), RuntimeError> {
    let Obj::FnObj(fn_obj) = lhs else {
        return Err(have_tuple_or_cart_parse_error(
            "have matrix expects left side `name(row, col)`",
            line_file,
        ));
    };
    if !is_fn_head_identifier_named(fn_obj.head.as_ref(), name) {
        return Err(have_tuple_or_cart_parse_error(
            "have matrix left side must apply the matrix being defined",
            line_file,
        ));
    }
    if fn_obj.body.len() != 1 || fn_obj.body[0].len() != 2 {
        return Err(have_tuple_or_cart_parse_error(
            "have matrix left side must use exactly two indices",
            line_file,
        ));
    }
    if !is_fn_set_index_named(fn_obj.body[0][0].as_ref(), row_index_name)
        || !is_fn_set_index_named(fn_obj.body[0][1].as_ref(), col_index_name)
    {
        return Err(have_tuple_or_cart_parse_error(
            "have matrix left side must use the bound row and column indices",
            line_file,
        ));
    }
    Ok(())
}

fn is_fn_head_identifier_named(head: &FnObjHead, name: &str) -> bool {
    matches!(head, FnObjHead::Identifier(identifier) if identifier.name == name)
        || matches!(head, FnObjHead::IdentifierWithMod(identifier) if identifier.name == name)
}

fn is_identifier_named(obj: &Obj, name: &str) -> bool {
    matches!(obj, Obj::Atom(AtomObj::Identifier(identifier)) if identifier.name == name)
        || matches!(obj, Obj::Atom(AtomObj::IdentifierWithMod(identifier)) if identifier.name == name)
}

fn is_tuple_index_named(obj: &Obj, name: &str) -> bool {
    matches!(obj, Obj::Atom(AtomObj::Bound(index)) if index.name() == name)
}

fn is_cart_index_named(obj: &Obj, name: &str) -> bool {
    matches!(obj, Obj::Atom(AtomObj::Bound(index)) if index.name() == name)
}

fn is_fn_set_index_named(obj: &Obj, name: &str) -> bool {
    matches!(obj, Obj::Atom(AtomObj::Bound(index)) if index.name() == name)
}

fn have_tuple_or_cart_parse_error(msg: &str, line_file: LineFile) -> RuntimeError {
    RuntimeError::from(ParseRuntimeError(
        RuntimeErrorStruct::new_with_msg_and_line_file(msg.to_string(), line_file),
    ))
}
