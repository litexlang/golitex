//! Parser-owned free-parameter bindings and source locations.

use crate::prelude::*;
use std::collections::HashMap;

#[derive(Clone)]
pub struct FreeParamCollection {
    pub params: HashMap<String, Vec<FreeParamTypeAndLineFile>>,
}

#[derive(Clone, Debug)]
pub struct FreeParamTypeAndLineFile {
    pub scope: BindingScope,
    pub binding: SymbolBinding,
}

impl FreeParamCollection {
    pub fn new() -> Self {
        FreeParamCollection {
            params: HashMap::new(),
        }
    }

    pub fn clear(&mut self) {
        self.params.clear();
    }

    pub fn begin_scope(
        &mut self,
        scope: BindingScope,
        bindings: &[SymbolBinding],
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        let mut names_in_new_scope: Vec<&str> = Vec::with_capacity(bindings.len());
        for binding in bindings {
            let n = binding.name();
            let duplicates_new_name = names_in_new_scope.contains(&n);
            let duplicates_active_binding = self.params.get(n).is_some_and(|stack| {
                stack
                    .last()
                    .is_some_and(|active| active.binding.id() != binding.id())
            });
            if duplicates_new_name || duplicates_active_binding {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!(
                            "free parameter `{}` is already bound to a different symbol in an active scope",
                            n
                        ),
                        line_file,
                    ),
                )));
            }
            names_in_new_scope.push(n);
        }
        for binding in bindings {
            let n = binding.name();
            self.params
                .entry(n.to_string())
                .or_default()
                .push(FreeParamTypeAndLineFile {
                    scope,
                    binding: binding.clone(),
                });
        }
        Ok(())
    }

    pub fn end_scope(&mut self, names: &[String]) {
        for n in names {
            let Some(stack) = self.params.get_mut(n) else {
                panic!("free param stack missing for `{}` on end_scope", n);
            };
            let Some(_top) = stack.pop() else {
                panic!("free param stack for `{}` empty on end_scope", n);
            };
            if stack.is_empty() {
                self.params.remove(n);
            }
        }
    }

    pub fn name_is_in_any_free_param_map(&self, name: &str) -> bool {
        self.params
            .get(name)
            .map_or(false, |stack| !stack.is_empty())
    }

    pub fn resolve_identifier_to_free_param_obj(&self, name: &str) -> Obj {
        if !self.name_is_in_any_free_param_map(name) {
            return Identifier::new(name.to_string()).into();
        }
        let Some(stack) = self.params.get(name) else {
            return Identifier::new(name.to_string()).into();
        };
        let Some(top) = stack.last() else {
            return Identifier::new(name.to_string()).into();
        };
        if top.scope.is_definition_binding() {
            Identifier::new_bound(name.to_string(), top.binding.as_ref()).into()
        } else {
            BoundParamObj::new(top.binding.as_ref()).into()
        }
    }
}
