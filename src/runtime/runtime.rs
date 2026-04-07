use crate::prelude::*;
use std::collections::HashMap;
use std::rc::Rc;

pub struct Runtime {
    pub module_manager: ModuleManager,
    pub environment_stack: Vec<Box<Environment>>,
    pub parsing_time_name_scope_stack: Vec<HashMap<String, LineFile>>,
}

impl Runtime {
    pub fn new() -> Self {
        let module_manager = ModuleManager::new_empty_module_manager(BUILTIN_CODE_PATH);
        let new_environment = Box::new(Environment::new_empty_env());

        Runtime {
            module_manager,
            environment_stack: vec![new_environment],
            parsing_time_name_scope_stack: vec![HashMap::new()],
        }
    }
}

impl Runtime {
    pub fn push_parsing_time_name_scope(&mut self) {
        self.parsing_time_name_scope_stack.push(HashMap::new());
    }

    pub fn validate_name(
        &mut self,
        name: &str,
        current_line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        if let Err(invalid_name_message) = is_valid_litex_name(name) {
            return Err(
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    invalid_name_message,
                    default_line_file(),
                    None,
                ),
            );
        }

        for names_in_scope in self.parsing_time_name_scope_stack.iter().rev() {
            if let Some(name_already_defined_on_line_file) = names_in_scope.get(name) {
                return Err(RuntimeError::new_parse_error_with_msg_position_previous_error(
                    format!(
                        "name `{}` is already used: previous definition at line {} in {}; current at line {} in {}",
                        name,
                        name_already_defined_on_line_file.0,
                        name_already_defined_on_line_file.1.as_ref(),
                        current_line_file.0,
                        current_line_file.1.as_ref(),
                    ),
                    current_line_file,
                    None,
                ));
            }
        }

        if self.is_name_used(name) {
            return Err(RuntimeError::new_parse_error_with_msg_position_previous_error(
                format!(
                    "name `{}` is already used: previous definition at line {} in {}; current at line {} in {}",
                    name,
                    default_line_file().0,
                    default_line_file().1.as_ref(),
                    current_line_file.0,
                    current_line_file.1.as_ref(),
                ),
                current_line_file,
                None,
            ));
        }

        Ok(())
    }

    pub(crate) fn validate_name_for_mangled_fn_param(
        &mut self,
        name: &str,
        current_line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        if let Err(invalid_name_message) = is_valid_mangled_fn_param_name(name) {
            return Err(
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    invalid_name_message,
                    default_line_file(),
                    None,
                ),
            );
        }

        for names_in_scope in self.parsing_time_name_scope_stack.iter().rev() {
            if let Some(name_already_defined_on_line_file) = names_in_scope.get(name) {
                return Err(RuntimeError::new_parse_error_with_msg_position_previous_error(
                    format!(
                        "name `{}` is already used: previous definition at line {} in {}; current at line {} in {}",
                        name,
                        name_already_defined_on_line_file.0,
                        name_already_defined_on_line_file.1.as_ref(),
                        current_line_file.0,
                        current_line_file.1.as_ref(),
                    ),
                    current_line_file,
                    None,
                ));
            }
        }

        if self.is_name_used(name) {
            return Err(RuntimeError::new_parse_error_with_msg_position_previous_error(
                format!(
                    "name `{}` is already used: previous definition at line {} in {}; current at line {} in {}",
                    name,
                    default_line_file().0,
                    default_line_file().1.as_ref(),
                    current_line_file.0,
                    current_line_file.1.as_ref(),
                ),
                current_line_file,
                None,
            ));
        }

        Ok(())
    }

    pub(crate) fn validate_name_and_insert_mangled_fn_param(
        &mut self,
        name: &str,
        (line, path): LineFile,
    ) -> Result<(), RuntimeError> {
        self.validate_name_for_mangled_fn_param(name, (line, path.clone()))?;
        if let Some(names_in_top_scope) = self.parsing_time_name_scope_stack.last_mut() {
            names_in_top_scope.insert(name.to_string(), (line, path.clone()));
        }
        Ok(())
    }

    pub(crate) fn register_collected_mangled_fn_param_names_for_def_parse(
        &mut self,
        names: &Vec<String>,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        for name in names {
            self.validate_name_and_insert_mangled_fn_param(name, line_file.clone())
                .map_err(|e| {
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        String::new(),
                        line_file.clone(),
                        Some(e),
                    )
                })?;
        }
        Ok(())
    }

    pub(crate) fn register_mangled_fn_param_binding(
        &mut self,
        user_written_names: &[String],
        line_file: LineFile,
    ) -> Result<(Vec<String>, HashMap<String, Obj>), RuntimeError> {
        // 虽然本质上存的是 __param，但param本身也要符合litex命名规则，比如你不能让 param 是 1
        for name in user_written_names {
            if let Err(e) = is_valid_litex_name(name) {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        e,
                        line_file.clone(),
                        None,
                    ),
                );
            }
        }

        let (mangled, map) = crate::common::mangled_fn_param::mangled_fn_param_binding(
            user_written_names,
            crate::common::defaults::DEFAULT_MANGLED_FN_PARAM_PREFIX,
        );
        self.register_collected_mangled_fn_param_names_for_def_parse(&mangled, line_file)?;
        Ok((mangled, map))
    }

    pub fn pop_parsing_time_name_scope(&mut self) {
        self.parsing_time_name_scope_stack.pop();
    }

    pub fn validate_names_and_insert_into_top_parsing_time_name_scope(
        &mut self,
        names: &Vec<String>,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        for name in names {
            self.validate_name_and_insert_into_top_parsing_time_name_scope(
                name,
                line_file.clone(),
            )?;
        }
        Ok(())
    }

    pub fn validate_name_and_insert_into_top_parsing_time_name_scope(
        &mut self,
        name: &str,
        (line, path): LineFile,
    ) -> Result<(), RuntimeError> {
        self.validate_name(name, (line, path.clone()))?;
        if let Some(names_in_top_scope) = self.parsing_time_name_scope_stack.last_mut() {
            names_in_top_scope.insert(name.to_string(), (line, path.clone()));
        }
        Ok(())
    }
}

impl Runtime {
    pub fn new_file_path_new_env_new_name_scope(&mut self, path: &str) {
        self.module_manager.run_file_paths.push(Rc::from(path));
        self.module_manager.current_file_index += 1;
        self.push_parsing_time_name_scope();
        self.push_env();
    }

    pub fn is_name_used(&self, name: &str) -> bool {
        self.parsing_time_name_scope_stack
            .iter()
            .any(|scope| scope.contains_key(name))
    }
}

impl Runtime {
    pub fn top_level_env(&mut self) -> &mut Environment {
        let result = self.environment_stack.last_mut();
        match result {
            Some(environment) => environment,
            None => unreachable!("no top level environment"),
        }
    }
}

impl Runtime {
    pub fn push_env(&mut self) {
        let new_env = Box::new(Environment::new_empty_env());
        self.environment_stack.push(new_env);
    }

    pub fn pop_env(&mut self) {
        let last_env = self.environment_stack.last();

        match last_env {
            None => {
                unreachable!("no top level environment")
            }
            Some(_) => {
                self.environment_stack.pop();
            }
        }
    }
}

impl Runtime {
    pub fn is_name_used_for_identifier_and_field_access(&self, name: &str) -> bool {
        if is_builtin_identifier_name(name) {
            return true;
        }

        for env in self.iter_environments_from_top() {
            if env.defined_identifiers.contains_key(name) {
                return true;
            }
        }

        false
    }

    pub fn is_name_used_for_prop(&self, name: &str) -> bool {
        return self.get_prop_definition_by_name(name).is_some();
    }

    pub fn is_name_used_for_abstract_prop(&self, name: &str) -> bool {
        if is_builtin_predicate(name) {
            return true;
        }

        return self.get_abstract_prop_definition_by_name(name).is_some();
    }

    pub fn is_name_used_for_struct(&self, name: &str) -> bool {
        return self.get_definition_of_struct_by_name(name).is_some();
    }

    pub fn is_name_used_for_family(&self, name: &str) -> bool {
        return self.get_family_definition_by_name(name).is_some();
    }

    pub fn is_name_used_for_algo(&self, name: &str) -> bool {
        return self.get_algo_definition_by_name(name).is_some();
    }
}

impl Runtime {
    pub fn new_file_and_update_runtime_with_file_content(&mut self, path: &str) {
        self.module_manager.run_file_paths.push(Rc::from(path));
        self.module_manager.current_file_index = self.module_manager.run_file_paths.len() - 1;
    }

    pub fn change_file_index_to(&mut self, file_index: usize) {
        self.module_manager.current_file_index = file_index;
    }
}

impl Runtime {
    pub fn store_tuple_obj_and_cart(
        &mut self,
        name: &str,
        tuple: Option<Tuple>,
        cart: Option<Cart>,
        line_file: LineFile,
    ) {
        let known_tuple_objs = &mut self.top_level_env().known_objs_equal_to_tuple;
        let old_tuple_and_cart = known_tuple_objs.get(name).cloned();

        let merged_tuple = match (tuple, old_tuple_and_cart.as_ref()) {
            (Some(new_tuple), _) => Some(new_tuple),
            (None, Some((old_tuple, _, _))) => old_tuple.clone(),
            (None, None) => None,
        };
        let merged_cart = match (cart, old_tuple_and_cart.as_ref()) {
            (Some(new_cart), _) => Some(new_cart),
            (None, Some((_, old_cart, _))) => old_cart.clone(),
            (None, None) => None,
        };
        let merged_line_file = line_file;

        known_tuple_objs.insert(
            name.to_string(),
            (merged_tuple, merged_cart, merged_line_file),
        );
    }

    pub fn store_known_cart_obj(&mut self, name: &str, cart: Cart, line_file: LineFile) {
        self.top_level_env()
            .known_objs_equal_to_cart
            .insert(name.to_string(), (cart, line_file));
    }
}
