use crate::prelude::*;

impl Runtime {
    pub(crate) fn allocate_symbol_id(&self) -> Result<SymbolId, RuntimeError> {
        self.symbol_id_allocator.allocate()
    }

    pub(crate) fn allocate_local_symbol_binding(
        &self,
        name: String,
    ) -> Result<SymbolBinding, RuntimeError> {
        if let Some(binding) = SymbolBinding::from_allocated_internal_name(name.clone()) {
            return Ok(binding);
        }
        Ok(SymbolBinding::new(
            self.allocate_symbol_id()?,
            name.clone(),
            name,
        ))
    }

    pub(crate) fn allocate_local_symbol_bindings(
        &self,
        names: &[String],
    ) -> Result<Vec<SymbolBinding>, RuntimeError> {
        names
            .iter()
            .map(|name| self.allocate_local_symbol_binding(name.clone()))
            .collect()
    }

    pub(crate) fn allocate_internal_symbol_binding(&self) -> Result<SymbolBinding, RuntimeError> {
        let id = self.allocate_symbol_id()?;
        let name = format!("#binder_{}", id.value());
        Ok(SymbolBinding::new(id, name.clone(), name))
    }

    pub(crate) fn allocate_declared_symbol_binding(
        &self,
        name: String,
    ) -> Result<SymbolBinding, RuntimeError> {
        Ok(SymbolBinding::new(
            self.allocate_symbol_id()?,
            name.clone(),
            self.canonical_display_name_for_declaration(name.as_str()),
        ))
    }

    fn canonical_display_name_for_declaration(&self, name: &str) -> String {
        let canonical_owner = self
            .execution_stack
            .last()
            .and_then(|frame| match frame.layer {
                ExecutionLayer::Main => self
                    .module_manager
                    .canonical_name_for_target(ImportTarget::Module(frame.module_id)),
                ExecutionLayer::File(file_id) => {
                    self.module_manager
                        .canonical_name_for_target(ImportTarget::File {
                            module_id: frame.module_id,
                            file_id,
                        })
                }
            })
            .unwrap_or("");
        if canonical_owner.is_empty() {
            name.to_string()
        } else {
            format!("{}{}{}", canonical_owner, MOD_SIGN, name)
        }
    }

    pub(crate) fn visible_symbol_definition(&self, name: &str) -> Option<&SymbolDefinition> {
        self.iter_environments_from_top()
            .find_map(|environment| environment.symbols.get(name))
    }

    pub(crate) fn resolved_identifier_symbol(&self, name: &str) -> Option<SymbolRef> {
        self.visible_symbol_definition(name)
            .map(|definition| definition.binding().as_ref())
    }

    pub(crate) fn resolved_qualified_identifier_symbol(
        &self,
        module_name: &str,
        name: &str,
    ) -> Option<SymbolRef> {
        if self.is_current_parse_module(module_name) {
            return self.resolved_identifier_symbol(name);
        }
        self.imported_module_environments(module_name)
            .into_iter()
            .find_map(|environment| environment.symbols.get(name))
            .map(|definition| definition.binding().as_ref())
    }

    pub(crate) fn active_parse_symbol_binding(&self, name: &str) -> Option<SymbolBinding> {
        self.current_parse_context().active_binding(name).cloned()
    }

    pub(crate) fn register_default_struct_view(
        &mut self,
        bindings: &[SymbolBinding],
        struct_obj: &StructObj,
    ) {
        for binding in bindings {
            self.default_struct_views
                .entry(binding.id())
                .or_insert_with(|| struct_obj.clone());
        }
    }

    pub(crate) fn default_struct_view_for_symbol(&self, symbol: &SymbolRef) -> Option<StructObj> {
        self.default_struct_views.get(&symbol.id()).cloned()
    }

    pub(crate) fn register_parsed_struct_definition(&mut self, def: &DefStructStmt) {
        let name = self
            .current_parse_namespace()
            .map(|owner| format!("{}{}{}", owner, MOD_SIGN, def.name))
            .unwrap_or_else(|| def.name.clone());
        self.parsed_struct_definitions
            .entry(name)
            .or_insert_with(|| def.clone());
    }

    pub(crate) fn parsed_struct_definition_by_name(&self, name: &str) -> Option<DefStructStmt> {
        self.parsed_struct_definitions.get(name).cloned()
    }

    pub(crate) fn template_instance_symbol_binding(
        &mut self,
        surface_name: &str,
    ) -> Result<SymbolBinding, RuntimeError> {
        let binding = self.intern_template_instance_symbol_binding(surface_name)?;
        self.current_parse_context_mut()
            .template_instance_bindings
            .insert(surface_name.to_string(), binding.clone());
        Ok(binding)
    }

    pub(crate) fn intern_template_instance_symbol_binding(
        &self,
        surface_name: &str,
    ) -> Result<SymbolBinding, RuntimeError> {
        if let Some(definition) = self.visible_symbol_definition(surface_name) {
            return Ok(definition.binding().clone());
        }
        if let Some(binding) = self.template_instance_interner.borrow().get(surface_name) {
            return Ok(binding.clone());
        }
        let binding = SymbolBinding::new(
            self.allocate_symbol_id()?,
            surface_name.to_string(),
            surface_name.to_string(),
        );
        self.template_instance_interner
            .borrow_mut()
            .insert(surface_name.to_string(), binding.clone());
        Ok(binding)
    }

    pub(crate) fn fresh_bound_param(
        &self,
        name: String,
        kind: ParamObjType,
    ) -> Result<(SymbolBinding, Obj), RuntimeError> {
        let binding = self.allocate_local_symbol_binding(name)?;
        let obj = obj_for_bound_param_in_scope(&binding, kind);
        Ok((binding, obj))
    }

    pub(crate) fn register_declared_symbol(
        &mut self,
        name: &str,
        role: SymbolRole,
    ) -> Result<SymbolBinding, RuntimeError> {
        if let Some(existing) = self.visible_symbol_definition(name) {
            return Err(symbol_name_already_used_error(
                name,
                existing.role().description(),
            ));
        }
        if is_builtin_identifier_name(name) || is_builtin_predicate(name) {
            return Err(symbol_name_already_used_error(name, "builtin"));
        }

        let binding = self.allocate_declared_symbol_binding(name.to_string())?;
        self.top_level_env()
            .symbols
            .insert(SymbolDefinition::new(binding.clone(), role))
            .expect("symbol was checked absent before registration");
        Ok(binding)
    }

    pub(crate) fn register_existing_symbol_binding(
        &mut self,
        binding: SymbolBinding,
        role: SymbolRole,
    ) -> Result<(), RuntimeError> {
        let binding = if role == SymbolRole::Object
            && !binding.name().starts_with(TEMPLATE_INSTANCE_PREFIX)
        {
            let canonical_display_name =
                self.canonical_display_name_for_declaration(binding.name());
            binding.with_canonical_display_name(canonical_display_name)
        } else {
            binding
        };
        let name = binding.name();
        if let Some(existing) = self.visible_symbol_definition(name) {
            if existing.binding().id() == binding.id() {
                return Ok(());
            }
            return Err(symbol_name_already_used_error(
                name,
                existing.role().description(),
            ));
        }
        if is_builtin_identifier_name(name) || is_builtin_predicate(name) {
            return Err(symbol_name_already_used_error(name, "builtin"));
        }
        self.top_level_env()
            .symbols
            .insert(SymbolDefinition::new(binding, role))
            .expect("symbol was checked absent before registration");
        Ok(())
    }

    pub(crate) fn begin_parsing_scope(
        &mut self,
        kind: ParamObjType,
        names: &[String],
        line_file: LineFile,
    ) -> Result<Vec<SymbolBinding>, RuntimeError> {
        if kind == ParamObjType::Induc
            && names
                .iter()
                .all(|name| self.current_parse_context().active_binding(name).is_some())
        {
            let bindings = names
                .iter()
                .map(|name| {
                    self.current_parse_context()
                        .active_binding(name)
                        .expect("induction binding was checked active")
                        .clone()
                })
                .collect::<Vec<_>>();
            self.current_parse_context_mut()
                .free_params
                .begin_scope(kind, &bindings, line_file)?;
            self.current_parse_context_mut()
                .push_reused_scope_frame(names.to_vec());
            return Ok(bindings);
        }

        let mut bindings = Vec::with_capacity(names.len());
        for (index, name) in names.iter().enumerate() {
            if names.iter().take(index).any(|existing| existing == name) {
                return Err(active_parse_name_error(name, &line_file));
            }
            if self.current_parse_context().active_binding(name).is_some()
                || self.visible_symbol_definition(name).is_some()
                || is_builtin_identifier_name(name)
                || is_builtin_predicate(name)
            {
                return Err(active_parse_name_error(name, &line_file));
            }
            let binding = if kind == ParamObjType::Identifier {
                self.allocate_declared_symbol_binding(name.clone())?
            } else {
                self.allocate_local_symbol_binding(name.clone())?
            };
            bindings.push(binding);
        }
        self.current_parse_context_mut()
            .free_params
            .begin_scope(kind, &bindings, line_file)?;
        self.current_parse_context_mut()
            .push_scope_frame(bindings.clone());
        Ok(bindings)
    }

    pub(crate) fn end_parsing_scope(&mut self, kind: ParamObjType, names: &[String]) {
        self.current_parse_context_mut()
            .free_params
            .end_scope(kind, names);
        self.current_parse_context_mut().remove_bindings(names);
    }

    pub(crate) fn fresh_param_group_with_type(
        &self,
        names: Vec<String>,
        param_type: ParamType,
    ) -> Result<ParamGroupWithParamType, RuntimeError> {
        Ok(ParamGroupWithParamType::new(
            self.allocate_local_symbol_bindings(&names)?,
            param_type,
        ))
    }

    pub(crate) fn fresh_param_group_with_set(
        &self,
        names: Vec<String>,
        set: Obj,
    ) -> Result<ParamGroupWithSet, RuntimeError> {
        Ok(ParamGroupWithSet::new(
            self.allocate_local_symbol_bindings(&names)?,
            set,
        ))
    }
}

fn symbol_name_already_used_error(name: &str, existing_role: &str) -> RuntimeError {
    NameAlreadyUsedRuntimeError(RuntimeErrorStruct::new_with_just_msg(format!(
        "name `{}` is already used in this scope as {}",
        name, existing_role
    )))
    .into()
}

pub(crate) fn active_parse_name_error(name: &str, line_file: &LineFile) -> RuntimeError {
    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
        format!(
            "name `{}` is already active in this scope and cannot be rebound",
            name
        ),
        line_file.clone(),
    ))
    .into()
}
