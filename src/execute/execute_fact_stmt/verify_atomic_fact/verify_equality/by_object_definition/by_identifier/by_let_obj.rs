//! Equality by object definition: unfold an identifier introduced by `let … = …`.
//!
//! Mathematical property:
//!   If `let a = rhs`, then `a = rhs`.
//!
//! Example:
//!   let a = 1 + 1
//!   a = 2
//! reduces to proving `1 + 1 = 2` after unfolding `a`.

use crate::ast::fact::EqualFact;
use crate::ast::obj::Obj;
use crate::exec_env::StoredIdentifierDefinition;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};
use super::super::helper::identifier_plain_name;

pub struct ByLetObjObjectDefinitionProof {
    pub expanded_rhs: Obj,
    pub residual_equal: VerifyFactResult,
}

impl Runtime {
    pub fn search_equal_fact_object_definition_let_obj(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ByLetObjObjectDefinitionProof>> {
        if let Some(proof) =
            self.try_let_obj_object_definition(&fact.left, &fact.right, fact, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            self.try_let_obj_object_definition(&fact.right, &fact.left, fact, verify_state)?
        {
            return Ok(Some(proof));
        }
        Ok(None)
    }

    pub(crate) fn try_let_obj_object_definition(
        &mut self,
        def_side: &Obj,
        other_side: &Obj,
        parent_fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ByLetObjObjectDefinitionProof>> {
        let Some(name) = identifier_plain_name(def_side) else {
            return Ok(None);
        };
        let Some(StoredIdentifierDefinition::LetObj((_, stmt))) =
            self.stored_identifier_definition_visible_in_stack(name)
        else {
            return Ok(None);
        };
        let expanded_rhs = stmt.value.clone();

        let residual = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: expanded_rhs.clone(),
            right: other_side.clone(),
            line_file: parent_fact.line_file.clone(),
        };
        let child_state = VerifyState {
            can_use_forall_fact: verify_state.can_use_forall_fact,
            can_use_rewrite: false,
            store_well_defined_fact: false,
        };
        let residual_equal = self.verify_equal_fact(&residual, child_state)?;
        if residual_equal.is_failed() {
            return Ok(None);
        }
        Ok(Some(ByLetObjObjectDefinitionProof {
            expanded_rhs,
            residual_equal,
        }))
    }
}

