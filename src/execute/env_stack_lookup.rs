use crate::ast::names::AtomicName;
use crate::ast::obj::{IdentifierObj, Obj};
use crate::ast::stmt::{
    AxiomStmt, DefAbstractPropStmt, DefPropStmt, DefStrategyStmt, DefStructStmt, DefTemplateStmt,
    DefThmStmt,
};
use crate::exec_env::ExecEnv;
use crate::exec_env::StoredIdentifierDefinition;
use crate::runtime::runtime_ids::{IdentifierId, WellDefinednessId};
use crate::runtime::Runtime;

impl Runtime {
    // Walk the exec-env stack (inner first) for name conflicts under a temp shell.
    pub(in crate::execute) fn identifier_defined_in_stack(&self, name: &str) -> bool {
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

    pub(crate) fn def_struct_visible(&self, name: &AtomicName) -> Option<&DefStructStmt> {
        self.lookup_named_definition(name, |env, plain| env.lookup_def_struct(plain))
    }

    pub(crate) fn def_template_visible(&self, name: &AtomicName) -> Option<&DefTemplateStmt> {
        self.lookup_named_definition(name, |env, plain| env.lookup_def_template(plain))
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

    pub(crate) fn stored_identifier_definition_visible(
        &self,
        identifier: &IdentifierObj,
    ) -> Option<&crate::exec_env::StoredIdentifierDefinition> {
        let name = match identifier {
            IdentifierObj::Plain { name, .. } => AtomicName::Plain { name: name.clone() },
            IdentifierObj::WithExportFileId { export_file_id, name } => {
                AtomicName::WithExportFileId {
                    export_file_id: *export_file_id,
                    name: name.clone(),
                }
            }
            IdentifierObj::WithModAndExportFileId { global_mod_id, export_file_id, name } => {
                AtomicName::WithModAndExportFileId {
                    global_mod_id: *global_mod_id,
                    export_file_id: *export_file_id,
                    name: name.clone(),
                }
            }
        };
        let definition = self.lookup_named_definition(&name, |env, plain| env.definitions.identifiers.get(plain))?;
        if let Some(stored_id) = stored_identifier_binding_id(definition, name.local_name()) {
            match identifier {
                IdentifierObj::Plain { id, .. } if *id != stored_id => return None,
                IdentifierObj::WithExportFileId { export_file_id, .. }
                    if self.code_source.is_live_root_export(*export_file_id) => {
                    if self.parse_scope_stack.first()?.plain.get(name.local_name()) != Some(&stored_id) {
                        return None;
                    }
                }
                IdentifierObj::WithModAndExportFileId { global_mod_id, export_file_id, .. }
                    if self.code_source.is_live_imported_export(*global_mod_id, *export_file_id) => {
                    if self.parse_scope_stack.first()?.plain.get(name.local_name()) != Some(&stored_id) {
                        return None;
                    }
                }
                _ => {}
            }
        }
        Some(definition)
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

fn stored_identifier_binding_id(definition: &StoredIdentifierDefinition, name: &str) -> Option<IdentifierId> {
    let params = match definition {
        StoredIdentifierDefinition::ParamType((bound, _)) => return Some(bound.id),
        StoredIdentifierDefinition::LetObj((_, stmt)) => return Some(stmt.name.id),
        StoredIdentifierDefinition::HaveFnEqual((_, stmt)) => return Some(stmt.name.id),
        StoredIdentifierDefinition::HaveByReplacementAxiom((_, stmt)) => return Some(stmt.name.id),
        StoredIdentifierDefinition::HaveObjEqual((_, stmt)) => &stmt.param_def,
        StoredIdentifierDefinition::HaveObjInNonemptySetOrParamType((_, stmt)) => &stmt.param_def,
        StoredIdentifierDefinition::HaveObjByExistFacts((_, stmt)) => &stmt.param_def,
        StoredIdentifierDefinition::TrustHave((_, stmt)) => &stmt.param_def,
        StoredIdentifierDefinition::HaveFnEqualCaseByCase((_, stmt)) => return Some(stmt.name.id),
        StoredIdentifierDefinition::HaveFnByForallExistUnique((_, stmt)) => return Some(stmt.name.id),
        StoredIdentifierDefinition::HaveFnByInduc((_, stmt)) => return Some(stmt.name.id),
    };
    params.groups.iter().flat_map(|group| &group.params)
        .find(|bound| bound.name == name).map(|bound| bound.id)
}
