use crate::prelude::*;

use super::parse_obj::{
    parse_synthetically_correct_identifier_string, validate_litex_name_for_parse,
    validate_module_path_segment_for_parse,
};

impl Runtime {
    pub fn parse_identifier(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let left = parse_synthetically_correct_identifier_string(tb)?;
        Ok(Identifier::new(left).into())
    }

    fn parse_mod_qualified_atom(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let mut parts = vec![parse_synthetically_correct_identifier_string(tb)?];
        while !tb.exceed_end_of_head() && tb.current()? == MOD_SIGN {
            tb.skip_token(MOD_SIGN)?;
            parts.push(parse_synthetically_correct_identifier_string(tb)?);
        }
        let right = parts
            .pop()
            .expect("qualified name should have a local name");
        let left = self.canonical_module_name_for_parse(&parts.join(MOD_SIGN));
        let identifier = match self.resolved_qualified_identifier_symbol(&left, &right) {
            Some(symbol) => IdentifierWithMod::new_bound(left, right, symbol),
            None => IdentifierWithMod::new(left, right),
        };
        Ok(identifier.into())
    }

    /// Unqualified or `::`-qualified name / field name; returns a name-shaped [`Obj`].
    pub fn parse_identifier_or_identifier_with_mod(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Obj, RuntimeError> {
        let next_is_mod = tb.token_at_add_index(1) == MOD_SIGN;
        if next_is_mod {
            self.parse_mod_qualified_atom(tb)
        } else {
            self.parse_identifier(tb)
        }
    }

    pub fn parse_predicate(&mut self, tb: &mut TokenBlock) -> Result<AtomicName, RuntimeError> {
        self.parse_atomic_name(tb)
    }

    pub fn parse_struct_view_obj(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        tb.skip_token(STRUCT_VIEW_PREFIX)?;
        let struct_obj = self.parse_struct_obj_after_prefix(tb)?;

        if !tb.exceed_end_of_head() && tb.current()? == LEFT_CURLY_BRACE {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "explicit struct selection `&Struct{object}.field` has been removed; declare the object or function return directly with `&Struct` and write `object.field`"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(struct_obj.into())
    }

    pub fn struct_view_for_field_access_receiver(
        &mut self,
        obj: &Obj,
        line_file: LineFile,
    ) -> Result<StructObj, RuntimeError> {
        if let Obj::InstantiatedTemplateObj(template_obj) = obj {
            if let Some(struct_obj) =
                self.direct_struct_carrier_for_instantiated_template(template_obj)?
            {
                self.current_parse_context_mut()
                    .default_struct_views
                    .entry(template_obj.symbol.id())
                    .or_insert_with(|| struct_obj.clone());
                return Ok(struct_obj);
            }
        }

        let symbol = match obj {
            Obj::Atom(atom) => atom.symbol_ref(),
            Obj::InstantiatedTemplateObj(template_obj) => Some(&template_obj.symbol),
            _ => None,
        };
        if let Some(symbol) = symbol {
            return self.default_struct_view_for_symbol(symbol).ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!(
                            "no declaration-time struct carrier is recorded for `{}`; declare it directly with a type such as `{} &Struct`",
                            symbol.display_name(),
                            symbol.display_name()
                        ),
                        line_file,
                    ),
                ))
            });
        }

        if let Obj::FnObj(fn_obj) = obj {
            let return_set = self.direct_fn_obj_return_set_after_application(fn_obj)?;
            if let Some(Obj::StructObj(struct_obj)) = return_set {
                return Ok(struct_obj);
            }

            // Local proof blocks are parsed before their `have fn` statements
            // execute. For a non-dependent direct struct return, the signature
            // parser records the carrier by the function symbol so field access
            // remains declaration-owned even in that pre-execution window.
            let head_obj: Obj = (*fn_obj.head).clone().into();
            if let Obj::Atom(atom) = head_obj {
                if let Some(struct_obj) = atom
                    .symbol_ref()
                    .and_then(|symbol| self.default_struct_view_for_symbol(symbol))
                {
                    return Ok(struct_obj);
                }
            }

            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "function result `{}` has no direct struct return carrier",
                        obj
                    ),
                    line_file,
                ),
            )));
        }

        let Obj::ObjAsStructInstanceWithFieldAccess(field_access) = obj else {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "field access requires a symbol, field, or function result whose declaration has a direct `&Struct` carrier"
                        .to_string(),
                    line_file,
                ),
            )));
        };

        let instantiated_field_type =
            self.declared_struct_field_type(field_access, line_file.clone())?;
        let Obj::StructObj(struct_obj) = instantiated_field_type else {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "cannot continue field access after `{}` because its declared field carrier is not a struct",
                        field_access
                    ),
                    line_file,
                ),
            )));
        };
        Ok(struct_obj)
    }

    /// A template application owns the carrier written on its body declaration
    /// after the template arguments have been substituted. This is deliberately
    /// declaration-only: an equality or a later membership fact cannot supply a
    /// named-field carrier.
    fn direct_struct_carrier_for_instantiated_template(
        &mut self,
        template_obj: &InstantiatedTemplateObj,
    ) -> Result<Option<StructObj>, RuntimeError> {
        let template_name = template_obj.template_name.to_string();
        let Some(def) = self.get_template_definition_by_name(&template_name) else {
            return Ok(None);
        };
        if template_obj.args.len() != def.template_arg_def.number_of_params() {
            return Ok(None);
        }

        let param_def = match &def.template_def_stmt {
            TemplateDefEnum::HaveObjInNonemptySetStmt(stmt) => Some(&stmt.param_def),
            TemplateDefEnum::HaveObjEqualStmt(stmt) => Some(&stmt.param_def),
            TemplateDefEnum::HaveObjByExistFactsStmt(stmt) => Some(&stmt.param_def),
            TemplateDefEnum::TrustHaveStmt(stmt) => Some(&stmt.param_def),
            _ => None,
        };
        let Some(param_def) = param_def else {
            return Ok(None);
        };
        let Some(ParamType::Obj(Obj::StructObj(struct_obj))) = param_def
            .groups
            .iter()
            .find(|group| {
                group
                    .params
                    .iter()
                    .any(|binding| binding.name() == def.template_name)
            })
            .map(|group| &group.param_type)
        else {
            return Ok(None);
        };

        let param_to_arg_map = def
            .template_arg_def
            .param_defs_and_args_to_param_to_arg_map(&template_obj.args);
        let instantiated = self.inst_obj(
            &Obj::StructObj(struct_obj.clone()),
            &param_to_arg_map,
            ParamObjType::DefHeader,
        )?;
        let Obj::StructObj(instantiated) = instantiated else {
            unreachable!("instantiating a struct carrier must preserve its object kind");
        };
        Ok(Some(instantiated))
    }

    fn direct_fn_obj_return_set_after_application(
        &mut self,
        fn_obj: &FnObj,
    ) -> Result<Option<Obj>, RuntimeError> {
        if fn_obj.body.is_empty() {
            return Ok(None);
        }

        let mut fn_body = match fn_obj.head.as_ref() {
            FnObjHead::AnonymousFnLiteral(anonymous_fn) => anonymous_fn.body.clone(),
            FnObjHead::ObjAsStructInstanceWithFieldAccess(field_access) => {
                let field_type =
                    self.declared_struct_field_type(field_access, default_line_file())?;
                match field_type {
                    Obj::FnSet(fn_set) => fn_set.body,
                    Obj::AnonymousFn(anonymous_fn) => anonymous_fn.body,
                    _ => return Ok(None),
                }
            }
            FnObjHead::FiniteSeqListObj(_) | FnObjHead::MatrixOperator(_) => return Ok(None),
            FnObjHead::InstantiatedTemplateObj(template_obj) => {
                let Some(body) = self.direct_fn_body_for_instantiated_template(template_obj)?
                else {
                    return Ok(None);
                };
                body
            }
            _ => {
                let head_obj: Obj = (*fn_obj.head).clone().into();
                let Some(body) = self.get_direct_object_in_fn_set(&head_obj) else {
                    return Ok(None);
                };
                body
            }
        };

        for (index, args) in fn_obj.body.iter().enumerate() {
            let args_as_obj: Vec<Obj> = args.iter().map(|arg| (**arg).clone()).collect();
            let param_to_arg_map = fn_body
                .params_def_with_set
                .param_defs_and_args_to_param_to_arg_map(&args_as_obj);
            let return_set =
                self.inst_obj(&fn_body.ret_set, &param_to_arg_map, ParamObjType::FnSet)?;
            if index == fn_obj.body.len() - 1 {
                return Ok(Some(return_set));
            }
            fn_body = match return_set {
                Obj::FnSet(fn_set) => fn_set.body,
                Obj::AnonymousFn(anonymous_fn) => anonymous_fn.body,
                _ => return Ok(None),
            };
        }

        Ok(None)
    }

    fn direct_fn_body_for_instantiated_template(
        &self,
        template_obj: &InstantiatedTemplateObj,
    ) -> Result<Option<FnSetBody>, RuntimeError> {
        let template_name = template_obj.template_name.to_string();
        let Some(def) = self.get_template_definition_by_name(&template_name) else {
            return Ok(None);
        };
        if template_obj.args.len() != def.template_arg_def.number_of_params() {
            return Ok(None);
        }

        let raw_body = match &def.template_def_stmt {
            TemplateDefEnum::HaveFnEqualStmt(stmt) => stmt.equal_to_anonymous_fn.body.clone(),
            TemplateDefEnum::HaveFnEqualCaseByCaseStmt(stmt) => FnSetBody::new(
                stmt.fn_set_clause.params_def_with_set.clone(),
                stmt.fn_set_clause.dom_facts.clone(),
                stmt.fn_set_clause.ret_set.clone(),
            ),
            TemplateDefEnum::HaveFnByInducStmt(stmt) => FnSetBody::new(
                stmt.fn_set_clause.params_def_with_set.clone(),
                stmt.fn_set_clause.dom_facts.clone(),
                stmt.fn_set_clause.ret_set.clone(),
            ),
            TemplateDefEnum::HaveFnByForallExistUniqueStmt(stmt) => {
                self.direct_fn_set_body_for_have_fn_by_forall_exist_unique(stmt)?
            }
            _ => return Ok(None),
        };

        let template_param_to_arg = def
            .template_arg_def
            .param_defs_and_args_to_param_to_arg_map(&template_obj.args);
        let instantiated_return = self.inst_obj(
            &raw_body.ret_set,
            &template_param_to_arg,
            ParamObjType::DefHeader,
        )?;
        Ok(Some(FnSetBody::new(
            raw_body.params_def_with_set,
            raw_body.dom_facts,
            instantiated_return,
        )))
    }

    fn declared_struct_field_type(
        &mut self,
        field_access: &ObjAsStructInstanceWithFieldAccess,
        line_file: LineFile,
    ) -> Result<Obj, RuntimeError> {
        let struct_name = field_access.struct_obj.name.to_string();
        let Some(def) = self
            .get_struct_definition_by_name(&struct_name)
            .or_else(|| self.parsed_struct_definition_by_name(&struct_name))
        else {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "cannot continue field access after `{}` because struct `{}` is not defined",
                        field_access, struct_name
                    ),
                    line_file,
                ),
            )));
        };

        let expected_count = def
            .param_def_with_dom
            .as_ref()
            .map(|(param_def, _)| param_def.number_of_params())
            .unwrap_or(0);
        if field_access.struct_obj.params.len() != expected_count {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "cannot continue field access after `{}` because struct `{}` expects {} parameter(s), got {}",
                        field_access,
                        struct_name,
                        expected_count,
                        field_access.struct_obj.params.len()
                    ),
                    line_file,
                ),
            )));
        }

        let Some(field) = def
            .fields
            .iter()
            .find(|field| field.name() == field_access.field_name)
        else {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "cannot continue field access: struct `{}` has no field `{}`",
                        struct_name, field_access.field_name
                    ),
                    line_file,
                ),
            )));
        };
        let instantiated_field_type = if let Some((param_def, _)) = &def.param_def_with_dom {
            let param_to_arg_map =
                param_def.param_defs_and_args_to_param_to_arg_map(&field_access.struct_obj.params);
            self.inst_obj(
                &field.field_type,
                &param_to_arg_map,
                ParamObjType::DefHeader,
            )?
        } else {
            field.field_type.clone()
        };
        Ok(instantiated_field_type)
    }

    fn parse_struct_obj_after_prefix(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<StructObj, RuntimeError> {
        let name = self.parse_module_qualified_reference_name(tb)?;
        let params = if !tb.exceed_end_of_head() && tb.current()? == LESS {
            self.parse_angle_bracketed_objs(tb)?
        } else if !tb.exceed_end_of_head() && tb.current()? == LEFT_BRACE {
            self.parse_braced_objs(tb)?
        } else {
            vec![]
        };
        Ok(StructObj::new(name, params))
    }

    /// `ident` or `mod::ident` as a predicate/atomic name in parse position.
    pub fn parse_atomic_name(&mut self, tb: &mut TokenBlock) -> Result<AtomicName, RuntimeError> {
        let left = parse_synthetically_correct_identifier_string(tb)?;
        if !tb.exceed_end_of_head() && tb.current()? == MOD_SIGN {
            let mut parts = vec![left];
            while !tb.exceed_end_of_head() && tb.current()? == MOD_SIGN {
                tb.skip()?;
                parts.push(parse_synthetically_correct_identifier_string(tb)?);
            }
            let right = parts
                .pop()
                .expect("qualified name should have a local name");
            let module_name = self.canonical_module_name_for_parse(&parts.join(MOD_SIGN));
            Ok(AtomicName::WithMod(module_name, right))
        } else {
            Ok(self.qualify_bare_atomic_name_if_needed(left))
        }
    }

    pub fn parse_module_qualified_reference_name(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<AtomicName, RuntimeError> {
        let left = tb.advance()?;
        if !tb.exceed_end_of_head() && tb.current()? == MOD_SIGN {
            let mut parts = vec![left];
            while !tb.exceed_end_of_head() && tb.current()? == MOD_SIGN {
                tb.skip_token(MOD_SIGN)?;
                let part = tb.advance()?;
                parts.push(part);
            }
            let right = parts
                .pop()
                .expect("qualified name should have a local name");
            for (index, part) in parts.iter().enumerate() {
                validate_module_path_segment_for_parse(part, index == 0, tb.line_file.clone())?;
            }
            validate_litex_name_for_parse(&right, tb.line_file.clone())?;
            let module_name = self.canonical_module_name_for_parse(&parts.join(MOD_SIGN));
            Ok(AtomicName::WithMod(module_name, right))
        } else {
            validate_litex_name_for_parse(&left, tb.line_file.clone())?;
            if let Some(symbol) = self.bare_symbol(&left) {
                return Ok(AtomicName::WithMod(symbol.canonical_owner.clone(), left));
            }
            match self.current_parse_module_name() {
                Some(module_name) => Ok(AtomicName::WithMod(module_name, left)),
                None => Ok(AtomicName::WithoutMod(left)),
            }
        }
    }

    fn current_parse_module_name(&self) -> Option<String> {
        self.current_parse_namespace().map(str::to_string)
    }

    pub(super) fn qualify_bare_identifier_if_needed(&self, id: Identifier) -> Obj {
        if is_builtin_identifier_name(&id.name) {
            let symbol =
                builtin_symbol_ref(&id.name).expect("builtin identifiers have stable symbol IDs");
            return Identifier::new_bound(id.name, symbol).into();
        }
        let symbol = self.resolved_identifier_symbol(&id.name);
        if symbol.is_none() {
            if let Some(bare) = self.bare_symbol(&id.name) {
                return IdentifierWithMod::new_bound(
                    bare.canonical_owner.clone(),
                    id.name,
                    bare.symbol.clone(),
                )
                .into();
            }
        }
        let Some(module_name) = self.current_parse_module_name() else {
            return match symbol {
                Some(symbol) => Identifier::new_bound(id.name, symbol).into(),
                None => id.into(),
            };
        };
        match symbol {
            Some(symbol) => IdentifierWithMod::new_bound(module_name, id.name, symbol).into(),
            None => IdentifierWithMod::new(module_name, id.name).into(),
        }
    }

    pub(super) fn qualify_bare_atomic_name_if_needed(&self, name: String) -> AtomicName {
        if is_builtin_predicate(&name) {
            return AtomicName::WithoutMod(name);
        }
        if let Some(symbol) = self.bare_symbol(&name) {
            return AtomicName::WithMod(symbol.canonical_owner.clone(), name);
        }
        let Some(module_name) = self.current_parse_module_name() else {
            return AtomicName::WithoutMod(name);
        };
        AtomicName::WithMod(module_name, name)
    }
}
