use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::ast::stmt::{
    AxiomStmt, DefAbstractPropStmt, DefPropStmt, DefStructStmt, DefTemplateStmt, DefThmStmt,
};
use crate::new_pipeline::exec_env::ExecEnv;
use crate::new_pipeline::runtime::runtime_ids::WellDefinednessId;
use crate::new_pipeline::runtime::Runtime;

impl Runtime {
    // Walk the exec-env stack (inner first) for name conflicts under a temp shell.
    pub(in crate::new_pipeline::execute) fn identifier_defined_in_stack(&self, name: &str) -> bool {
        self.execution_environments_stack
            .iter()
            .rev()
            .any(|env| env.definitions.identifiers.contains_key(name))
    }

    pub(crate) fn def_prop_visible_in_stack(&self, name: &str) -> Option<&DefPropStmt> {
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(def) = env.lookup_def_prop(name) {
                return Some(def);
            }
        }
        None
    }

    pub(crate) fn def_abstract_prop_visible_in_stack(
        &self,
        name: &str,
    ) -> Option<&DefAbstractPropStmt> {
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(def) = env.lookup_def_abstract_prop(name) {
                return Some(def);
            }
        }
        None
    }

    pub(crate) fn def_thm_visible_in_stack(&self, name: &str) -> Option<&DefThmStmt> {
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(def) = env.lookup_def_thm(name) {
                return Some(def);
            }
        }
        None
    }

    // Plain → live stack. Qualified → finished export Env (current-file fallback).
    pub(crate) fn def_thm_visible(&self, name: &AtomicName) -> Option<&DefThmStmt> {
        self.lookup_named_definition(name, |env, plain| env.lookup_def_thm(plain))
    }

    pub(crate) fn def_prop_visible(&self, name: &AtomicName) -> Option<&DefPropStmt> {
        self.lookup_named_definition(name, |env, plain| env.lookup_def_prop(plain))
    }

    pub(crate) fn def_abstract_prop_visible(
        &self,
        name: &AtomicName,
    ) -> Option<&DefAbstractPropStmt> {
        self.lookup_named_definition(name, |env, plain| env.lookup_def_abstract_prop(plain))
    }

    pub(crate) fn def_struct_visible_in_stack(&self, name: &str) -> Option<&DefStructStmt> {
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(def) = env.lookup_def_struct(name) {
                return Some(def);
            }
        }
        None
    }

    pub(crate) fn def_template_visible_in_stack(&self, name: &str) -> Option<&DefTemplateStmt> {
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(def) = env.lookup_def_template(name) {
                return Some(def);
            }
        }
        None
    }

    pub(crate) fn axiom_visible_in_stack(&self, name: &str) -> Option<&AxiomStmt> {
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(def) = env.lookup_axiom(name) {
                return Some(def);
            }
        }
        None
    }

    pub(crate) fn stored_identifier_definition_visible_in_stack(
        &self,
        name: &str,
    ) -> Option<&crate::new_pipeline::exec_env::StoredIdentifierDefinition> {
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(def) = env.definitions.identifiers.get(name) {
                return Some(def);
            }
        }
        None
    }

    // Finished export file Env after that file recorded; None while still loading.
    pub(crate) fn finished_export_exec_env(
        &self,
        global_mod_id: Option<usize>,
        export_file_id: usize,
    ) -> Option<&ExecEnv> {
        let exports = match global_mod_id {
            None => self.global_module_manager.root_exports(),
            Some(mod_id) => self
                .global_module_manager
                .imports()
                .get(mod_id)?
                .export_files_and_their_env
                .as_slice(),
        };
        Some(exports.get(export_file_id)?.exec_env.as_ref())
    }

    // WD memory: inner scopes first, then parents (same walk as definitions).
    pub(in crate::new_pipeline::execute) fn well_defined_visible_in_stack(
        &self,
        obj: &Obj,
    ) -> Option<WellDefinednessId> {
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(wd_id) = env.well_defined_objects.lookup(obj) {
                return Some(wd_id);
            }
        }
        None
    }

    fn lookup_named_definition<'a, T: 'a>(
        &'a self,
        name: &AtomicName,
        lookup: impl Fn(&'a ExecEnv, &str) -> Option<&'a T>,
    ) -> Option<&'a T> {
        let plain = name.local_name();
        match name {
            AtomicName::Plain { .. } => {
                for env in self.execution_environments_stack.iter().rev() {
                    if let Some(def) = lookup(env, plain) {
                        return Some(def);
                    }
                }
                None
            }
            AtomicName::WithExportFileId { export_file_id, .. } => self
                .finished_export_exec_env(None, *export_file_id)
                .and_then(|env| lookup(env, plain))
                .or_else(|| {
                    if *export_file_id == self.current_export_file_id {
                        for env in self.execution_environments_stack.iter().rev() {
                            if let Some(def) = lookup(env, plain) {
                                return Some(def);
                            }
                        }
                    }
                    None
                }),
            AtomicName::WithModAndExportFileId {
                global_mod_id,
                export_file_id,
                ..
            } => self
                .finished_export_exec_env(Some(*global_mod_id), *export_file_id)
                .and_then(|env| lookup(env, plain))
                .or_else(|| {
                    if self.global_module_manager.current_mod_id() == Some(*global_mod_id)
                        && *export_file_id == self.current_export_file_id
                    {
                        for env in self.execution_environments_stack.iter().rev() {
                            if let Some(def) = lookup(env, plain) {
                                return Some(def);
                            }
                        }
                    }
                    None
                }),
        }
    }
}
