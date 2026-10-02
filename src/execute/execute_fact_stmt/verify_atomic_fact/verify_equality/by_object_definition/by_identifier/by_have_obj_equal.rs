//! Equality by object definition: unfold an identifier introduced by `have … = …`.
//!
//! Mathematical property:
//!   If `have a T = rhs` stores definition `a`, then `a = rhs`.
//!
//! Example:
//!   have a R = 1 + 1
//!   a = 2
//! reduces to proving `1 + 1 = 2` after unfolding `a`.

use crate::ast::fact::EqualFact;
use crate::ast::obj::{IdentifierObj, Obj};
use crate::ast::stmt::HaveObjEqualStmt;
use crate::exec_env::StoredIdentifierDefinition;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

pub struct ByHaveObjEqualObjectDefinitionProof {
    pub expanded_rhs: Obj,
    pub residual_equal: VerifyFactResult,
}

impl Runtime {
    pub fn search_equal_fact_object_definition_have_obj_equal(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ByHaveObjEqualObjectDefinitionProof>> {
        if let Some(proof) = self.try_have_obj_equal_object_definition(
            &fact.left,
            &fact.right,
            fact,
            verify_state.clone(),
        )? {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.try_have_obj_equal_object_definition(
            &fact.right,
            &fact.left,
            fact,
            verify_state,
        )? {
            return Ok(Some(proof));
        }
        Ok(None)
    }

    pub(crate) fn try_have_obj_equal_object_definition(
        &mut self,
        def_side: &Obj,
        other_side: &Obj,
        parent_fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ByHaveObjEqualObjectDefinitionProof>> {
        let Obj::Identifier(identifier) = def_side else {
            return Ok(None);
        };
        let Some(StoredIdentifierDefinition::HaveObjEqual((_, stmt))) =
            self.stored_identifier_definition_visible(identifier)
        else {
            return Ok(None);
        };
        let stmt = stmt.clone();
        let name = match identifier {
            IdentifierObj::Plain { name, .. }
            | IdentifierObj::WithExportFileId { name, .. }
            | IdentifierObj::WithModAndExportFileId { name, .. } => name.as_str(),
        };
        let Some(expanded_rhs) = rhs_of_have_obj_equal_for_name(name, &stmt) else {
            return Ok(None);
        };

        let residual = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: expanded_rhs.clone(),
            right: other_side.clone(),
            line_file: parent_fact.line_file.clone(),
        };
        let child_state = VerifyState {
            can_use_builtin_rule: verify_state.can_use_builtin_rule,
            remaining_deep_search_depth: verify_state.remaining_deep_search_depth,
            can_use_def_and_known_forall_and_known_strategy: verify_state.can_use_def_and_known_forall_and_known_strategy,
            can_use_rewrite: false,
            store_well_defined_fact: false,
            equality_class_search: verify_state.equality_class_search,
        };
        let residual_equal = self.verify_equal_fact(&residual, child_state)?;
        if residual_equal.is_failed() {
            return Ok(None);
        }
        Ok(Some(ByHaveObjEqualObjectDefinitionProof {
            expanded_rhs,
            residual_equal,
        }))
    }
}


fn rhs_of_have_obj_equal_for_name(name: &str, stmt: &HaveObjEqualStmt) -> Option<Obj> {
    let mut index = 0;
    for group in &stmt.param_def.groups {
        for param in &group.params {
            if param.name.as_str() == name {
                return stmt.objs_equal_to.get(index).cloned();
            }
            index += 1;
        }
    }
    None
}
