use crate::ast::names::AtomicName;
use crate::ast::obj::Obj;
use crate::ast::stmt::{
    AxiomStmt, DefAbstractPropStmt, DefPropStmt, DefStrategyStmt, DefStructStmt, DefTemplateStmt,
    DefThmStmt,
};
use crate::exec_env::ExecEnv;
use crate::runtime::runtime_ids::WellDefinednessId;
use crate::runtime::Runtime;

impl Runtime {
    // Walk the exec-env stack (inner first) for name conflicts under a temp shell.
    pub(in crate::execute) fn identifier_defined_in_stack(&self, name: &str) -> bool {
        self.execution_environments_stack
            .iter()
            .rev()
            .any(|env| env.definitions.identifiers.contains_key(name))
    }

    // Drop a surface-name identifier definition from the first env (inner-first)
    // that owns it. Used when `obtain` rebinds a name already introduced earlier
    // in the same proof.
    pub(in crate::execute) fn remove_identifier_definition_from_stack(&mut self, name: &str) {
        for env in self.execution_environments_stack.iter_mut().rev() {
            if env.definitions.identifiers.remove(name).is_some() {
                return;
            }
        }
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

    pub(crate) fn def_algo_visible_in_stack(
        &self,
        name: &str,
    ) -> Option<&crate::exec_env::StoredDefAlgo> {
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(def) = env.lookup_def_algo(name) {
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

    // Plain → live stack. Qualified → finished export Env (same path as def_thm).
    pub(crate) fn axiom_visible(&self, name: &AtomicName) -> Option<&AxiomStmt> {
        self.lookup_named_definition(name, |env, plain| env.lookup_axiom(plain))
    }

    pub(crate) fn def_strategy_visible_in_stack(&self, name: &str) -> Option<&DefStrategyStmt> {
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(def) = env.lookup_def_strategy(name) {
                return Some(def);
            }
        }
        None
    }

    pub(crate) fn stored_identifier_definition_visible_in_stack(
        &self,
        name: &str,
    ) -> Option<&crate::exec_env::StoredIdentifierDefinition> {
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
    pub(in crate::execute) fn well_defined_visible_in_stack(
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
                    if self.code_source.is_live_root_export(*export_file_id) {
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
                    if self
                        .code_source
                        .is_live_imported_export(*global_mod_id, *export_file_id)
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
