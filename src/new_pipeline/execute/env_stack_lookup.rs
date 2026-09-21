use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::ast::stmt::{
    AxiomStmt, DefAbstractPropStmt, DefPropStmt, DefStructStmt, DefTemplateStmt, DefThmStmt,
};
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

    pub(crate) fn def_prop_visible_in_stack(
        &self,
        name: &str,
    ) -> Option<&DefPropStmt> {
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
}
