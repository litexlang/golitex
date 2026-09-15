use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::ast::stmt::{DefAbstractPropStmt, DefPropStmt};
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

    pub(in crate::new_pipeline::execute) fn def_prop_visible_in_stack(
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

    pub(in crate::new_pipeline::execute) fn def_abstract_prop_visible_in_stack(
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
