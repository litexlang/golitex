//! Definition-owned struct carriers used to resolve named-field access.

use crate::prelude::*;

impl Runtime {
    pub(crate) fn direct_struct_carrier_for_obj(
        &self,
        obj: &Obj,
        line_file: LineFile,
    ) -> Result<StructObj, RuntimeError> {
        if let Obj::InstantiatedTemplateObj(template_obj) = obj {
            if let Some(struct_obj) =
                self.direct_struct_carrier_for_instantiated_template(template_obj)?
            {
                return Ok(struct_obj);
            }
        }

        let symbol = match obj {
            Obj::Atom(atom) => atom.symbol_ref(),
            _ => None,
        };
        if let Some(symbol) = symbol {
            return self.direct_struct_carrier_for_symbol(symbol).ok_or_else(|| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!(
                            "no definition-time struct carrier is recorded for `{}`; define it directly with a type such as `{} &Struct`",
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

            return Err(RuntimeError::from(WellDefinedRuntimeError(
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
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "field access requires a symbol, field, or function result whose definition has a direct `&Struct` carrier"
                        .to_string(),
                    line_file,
                ),
            )));
        };

        let instantiated_field_type =
            self.direct_struct_field_type_for_access(field_access, line_file.clone())?;
        let Obj::StructObj(struct_obj) = instantiated_field_type else {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "cannot continue field access after `{}` because its defined field carrier is not a struct",
                        field_access
                    ),
                    line_file,
                ),
            )));
        };
        Ok(struct_obj)
    }

    /// A template application owns the carrier written on its body definition
    /// after the template arguments have been substituted. This is deliberately
    /// definition-only: an equality or a later membership fact cannot supply a
    /// named-field carrier.
    fn direct_struct_carrier_for_instantiated_template(
        &self,
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
            SubstitutionMode::Exact,
        )?;
        let Obj::StructObj(instantiated) = instantiated else {
            unreachable!("instantiating a struct carrier must preserve its object kind");
        };
        Ok(Some(instantiated))
    }

    fn direct_fn_obj_return_set_after_application(
        &self,
        fn_obj: &FnObj,
    ) -> Result<Option<Obj>, RuntimeError> {
        if fn_obj.body.is_empty() {
            return Ok(None);
        }

        let mut fn_body = match fn_obj.head.as_ref() {
            FnObjHead::AnonymousFnLiteral(anonymous_fn) => anonymous_fn.body.clone(),
            FnObjHead::ObjAsStructInstanceWithFieldAccess(field_access) => {
                let field_type =
                    self.direct_struct_field_type_for_access(field_access, default_line_file())?;
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
                .set_bound_parameters
                .param_defs_and_args_to_param_to_arg_map(&args_as_obj);
            let return_set =
                self.inst_obj(&fn_body.ret_set, &param_to_arg_map, SubstitutionMode::Exact)?;
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
                stmt.fn_set_clause.set_bound_parameters.clone(),
                stmt.fn_set_clause.dom_facts.clone(),
                stmt.fn_set_clause.ret_set.clone(),
            ),
            TemplateDefEnum::HaveFnByInducStmt(stmt) => FnSetBody::new(
                stmt.fn_set_clause.set_bound_parameters.clone(),
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
            SubstitutionMode::Exact,
        )?;
        Ok(Some(FnSetBody::new(
            raw_body.set_bound_parameters,
            raw_body.dom_facts,
            instantiated_return,
        )))
    }

    pub(crate) fn direct_struct_field_type_for_access(
        &self,
        field_access: &ObjAsStructInstanceWithFieldAccess,
        line_file: LineFile,
    ) -> Result<Obj, RuntimeError> {
        let struct_obj =
            self.direct_struct_owner_carrier_for_field_access(field_access, line_file.clone())?;
        let struct_name = struct_obj.name.to_string();
        let Some(def) = self.get_struct_definition_by_name(&struct_name) else {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
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
        if struct_obj.params.len() != expected_count {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "cannot continue field access after `{}` because struct `{}` expects {} parameter(s), got {}",
                        field_access,
                        struct_name,
                        expected_count,
                        struct_obj.params.len()
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
            return Err(RuntimeError::from(WellDefinedRuntimeError(
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
                param_def.param_defs_and_args_to_param_to_arg_map(&struct_obj.params);
            self.inst_obj(
                &field.field_type,
                &param_to_arg_map,
                SubstitutionMode::Exact,
            )?
        } else {
            field.field_type.clone()
        };
        Ok(instantiated_field_type)
    }

    pub(crate) fn direct_struct_owner_carrier_for_field_access(
        &self,
        field_access: &ObjAsStructInstanceWithFieldAccess,
        line_file: LineFile,
    ) -> Result<StructObj, RuntimeError> {
        match field_access.resolved_struct_carrier.as_deref() {
            Some(struct_obj) => Ok(struct_obj.clone()),
            None => self.direct_struct_carrier_for_obj(&field_access.obj, line_file),
        }
    }
}
