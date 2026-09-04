//! Symbol allocation, lookup policy, and binder-name validation.

use crate::prelude::*;

impl Runtime {
    pub fn allocate_symbol_id(&self) -> Result<SymbolId, RuntimeError> {
        self.symbol_id_allocator.allocate()
    }

    pub fn allocate_local_symbol_binding(
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

    pub fn allocate_local_symbol_bindings(
        &self,
        names: &[String],
    ) -> Result<Vec<SymbolBinding>, RuntimeError> {
        names
            .iter()
            .map(|name| self.allocate_local_symbol_binding(name.clone()))
            .collect()
    }

    pub fn allocate_internal_symbol_binding(&self) -> Result<SymbolBinding, RuntimeError> {
        let id = self.allocate_symbol_id()?;
        let name = format!("{}{}", INTERNAL_BINDER_PREFIX, id.value());
        Ok(SymbolBinding::new(id, name.clone(), name))
    }

    pub fn allocate_definition_symbol_binding(
        &self,
        name: String,
    ) -> Result<SymbolBinding, RuntimeError> {
        Ok(SymbolBinding::new(
            self.allocate_symbol_id()?,
            name.clone(),
            self.canonical_display_name_for_definition(name.as_str()),
        ))
    }

    fn canonical_display_name_for_definition(&self, name: &str) -> String {
        let canonical_owner = self
            .current_module_id
            .zip(self.current_source_id)
            .and_then(|(module_id, source_id)| {
                self.module_manager
                    .canonical_name_for_target(ImportTarget::File {
                        module_id,
                        source_id,
                    })
            })
            .unwrap_or("");
        if canonical_owner.is_empty() {
            name.to_string()
        } else {
            format!("{}{}{}", canonical_owner, MOD_SIGN, name)
        }
    }

    pub fn visible_symbol_definition(&self, name: &str) -> Option<&SymbolDefinition> {
        self.iter_environments_from_top()
            .find_map(|environment| environment.definitions.symbols.get(name))
    }

    pub fn resolved_identifier_symbol(&self, name: &str) -> Option<SymbolRef> {
        self.visible_symbol_definition(name)
            .map(|definition| definition.binding().as_ref())
    }

    pub fn resolved_qualified_identifier_symbol(
        &self,
        module_name: &str,
        name: &str,
    ) -> Option<SymbolRef> {
        if self.is_current_parse_module(module_name) {
            return self.resolved_identifier_symbol(name);
        }
        self.imported_module_environments(module_name)
            .into_iter()
            .find_map(|environment| environment.definitions.symbols.get(name))
            .map(|definition| definition.binding().as_ref())
    }

    pub fn active_parse_symbol_binding(&self, name: &str) -> Option<SymbolBinding> {
        self.current_parse_context().active_binding(name).cloned()
    }

    pub fn direct_struct_carrier_for_symbol(&self, symbol: &SymbolRef) -> Option<StructObj> {
        self.iter_environments_from_top()
            .find_map(|environment| {
                environment
                    .definitions
                    .symbols
                    .get_by_id(symbol.id())
                    .and_then(SymbolDefinition::direct_struct_carrier)
                    .cloned()
            })
            .or_else(|| {
                self.executed_direct_struct_carriers
                    .get(&symbol.id())
                    .cloned()
            })
            .or_else(|| {
                self.module_manager.modules.values().find_map(|module| {
                    module
                        .main_environment
                        .definitions
                        .symbols
                        .get_by_id(symbol.id())
                        .and_then(SymbolDefinition::direct_struct_carrier)
                        .cloned()
                        .or_else(|| {
                            module.sources.iter().find_map(|source| {
                                if source.real_file_path().is_none()
                                    && !(self.current_module_id == Some(module.id)
                                        && self.current_source_id == Some(source.id))
                                {
                                    return None;
                                }
                                source
                                    .environment
                                    .definitions
                                    .symbols
                                    .get_by_id(symbol.id())
                                    .and_then(SymbolDefinition::direct_struct_carrier)
                                    .cloned()
                            })
                        })
                })
            })
    }

    pub fn remember_direct_struct_carrier_for_binding(
        &mut self,
        binding: &SymbolBinding,
        struct_obj: &StructObj,
    ) {
        self.executed_direct_struct_carriers
            .entry(binding.id())
            .or_insert_with(|| struct_obj.clone());
        if let Some(definition) = self
            .top_level_env()
            .definitions
            .symbols
            .get_by_id_mut(binding.id())
        {
            definition.remember_direct_struct_carrier_if_absent(struct_obj.clone());
        }
    }

    /// A concrete predicate application semantically projects its declared
    /// parameter type onto the supplied argument. For a symbol argument and a
    /// struct parameter, retain that definition-owned consequence so later
    /// field syntax can resolve without treating arbitrary membership facts as
    /// field-owner declarations.
    pub fn remember_inferred_direct_struct_carrier_for_symbol(
        &mut self,
        symbol: &SymbolRef,
        struct_obj: &StructObj,
    ) -> Result<(), RuntimeError> {
        if let Some(existing) = self.direct_struct_carrier_for_symbol(symbol) {
            let existing_obj: Obj = existing.clone().into();
            let inferred_obj: Obj = struct_obj.clone().into();
            if obj_equality_key(&existing_obj) != obj_equality_key(&inferred_obj) {
                return Err(RuntimeError::from(InferRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "predicate parameter inference gives `{}` conflicting direct struct carriers `{existing}` and `{struct_obj}`",
                        symbol.display_name()
                    )),
                )));
            }
            return Ok(());
        }

        self.executed_direct_struct_carriers
            .insert(symbol.id(), struct_obj.clone());
        if let Some(definition) = self
            .top_level_env()
            .definitions
            .symbols
            .get_by_id_mut(symbol.id())
        {
            definition.remember_direct_struct_carrier_if_absent(struct_obj.clone());
        }
        Ok(())
    }

    pub fn fresh_bound_param(&self, name: String) -> Result<(SymbolBinding, Obj), RuntimeError> {
        let binding = self.allocate_local_symbol_binding(name)?;
        let obj = obj_for_bound_param_in_scope(&binding);
        Ok((binding, obj))
    }

    pub fn register_definition_symbol(
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
        if is_keyword(name) || is_builtin_identifier_name(name) || is_builtin_predicate(name) {
            return Err(symbol_name_already_used_error(name, "builtin"));
        }

        let binding = self.allocate_definition_symbol_binding(name.to_string())?;
        self.top_level_env()
            .definitions
            .symbols
            .insert(SymbolDefinition::new(binding.clone(), role))
            .expect("symbol was checked absent before registration");
        Ok(binding)
    }

    pub fn register_existing_symbol_binding(
        &mut self,
        binding: SymbolBinding,
        role: SymbolRole,
    ) -> Result<(), RuntimeError> {
        let binding = if role == SymbolRole::Object
            && !binding.name().starts_with(TEMPLATE_INSTANCE_PREFIX)
        {
            let canonical_display_name = self.canonical_display_name_for_definition(binding.name());
            binding.with_canonical_display_name(canonical_display_name)
        } else {
            binding
        };
        let name = binding.name();
        if let Some(existing) = self.visible_symbol_definition(name) {
            if existing.binding().id() == binding.id() {
                if existing.role() == role {
                    return Ok(());
                }
                return Err(symbol_name_already_used_error(
                    name,
                    existing.role().description(),
                ));
            }
            return Err(symbol_name_already_used_error(
                name,
                existing.role().description(),
            ));
        }
        if is_keyword(name) || is_builtin_identifier_name(name) || is_builtin_predicate(name) {
            return Err(symbol_name_already_used_error(name, "builtin"));
        }
        self.top_level_env()
            .definitions
            .symbols
            .insert(SymbolDefinition::new(binding, role))
            .expect("symbol was checked absent before registration");
        Ok(())
    }

    pub fn begin_parsing_scope(
        &mut self,
        scope: BindingScope,
        names: &[String],
        line_file: LineFile,
    ) -> Result<Vec<SymbolBinding>, RuntimeError> {
        if scope.reuses_active_binding()
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
                .begin_scope(scope, &bindings, line_file)?;
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
                || is_keyword(name)
                || is_builtin_identifier_name(name)
                || is_builtin_predicate(name)
            {
                return Err(active_parse_name_error(name, &line_file));
            }
            let binding = if scope.is_definition_binding() {
                self.allocate_definition_symbol_binding(name.clone())?
            } else {
                self.allocate_local_symbol_binding(name.clone())?
            };
            bindings.push(binding);
        }
        self.current_parse_context_mut()
            .free_params
            .begin_scope(scope, &bindings, line_file)?;
        self.current_parse_context_mut()
            .push_scope_frame(bindings.clone());
        Ok(bindings)
    }

    pub fn end_parsing_scope(&mut self, names: &[String]) {
        self.current_parse_context_mut()
            .free_params
            .end_scope(names);
        self.current_parse_context_mut().remove_bindings(names);
    }

    pub fn fresh_param_group_with_type(
        &self,
        names: Vec<String>,
        param_type: ParamType,
    ) -> Result<TypedParameterGroup, RuntimeError> {
        Ok(TypedParameterGroup::new(
            self.allocate_local_symbol_bindings(&names)?,
            param_type,
        ))
    }

    pub fn fresh_param_group_with_set(
        &self,
        names: Vec<String>,
        set: Obj,
    ) -> Result<SetBoundParameterGroup, RuntimeError> {
        Ok(SetBoundParameterGroup::new(
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

pub fn active_parse_name_error(name: &str, line_file: &LineFile) -> RuntimeError {
    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
        format!(
            "name `{}` is already active in this scope and cannot be rebound",
            name
        ),
        line_file.clone(),
    ))
    .into()
}
