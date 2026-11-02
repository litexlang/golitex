//! Equality by object definition: unfold `\Name<args>` when the template body is `have … = …`.
//!
//! Mathematical property (definitional unfold):
//!   If `template<params>:` defines `have name T = rhs`, then for concrete args
//!   satisfying the header, `\name<args> = subst(rhs)`.
//!
//! Example:
//!   template<S set>:
//!       have carrier_copy set = S
//!   \carrier_copy<R> = R
//! reduces to proving `R = R` after substituting `S := R`.

use crate::ast::fact::EqualFact;
use crate::ast::obj::{InstantiatedTemplateObj, Obj};
use crate::ast::stmt::TemplateDefEnum;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

// Success evidence for one orientation of the unfold.
// Field order: expanded RHS, then residual equality proof.
pub struct ByUnfoldInstantiatedTemplateHaveObjEqualObjectDefinitionProof {
    pub expanded_rhs: Obj,
    pub residual_equal: VerifyFactResult,
}

impl Runtime {
    // If `template_side` is `\Name<args>` with HaveObjEqual body, prove
    // `subst(rhs) = other_side`.
    pub(crate) fn try_unfold_instantiated_template_have_obj_equal(
        &mut self,
        template_side: &Obj,
        other_side: &Obj,
        parent_fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ByUnfoldInstantiatedTemplateHaveObjEqualObjectDefinitionProof>> {
        let Obj::InstantiatedTemplateObj(inst) = template_side else {
            return Ok(None);
        };
        let Some(expanded_rhs) = self.expanded_have_obj_equal_rhs_of_instantiated_template(inst)?
        else {
            return Ok(None);
        };

        let residual = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: expanded_rhs.clone(),
            right: other_side.clone(),
            line_file: parent_fact.line_file.clone(),
        };
        // Residual search keeps rewrite off so unfold does not loop through
        // rewrite→builtin. Forall stays available for ordinary residual goals.
        let child_state = verify_state.without_rewrite();
        let residual_equal = self.verify_equal_fact(&residual, child_state)?;
        if residual_equal.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            ByUnfoldInstantiatedTemplateHaveObjEqualObjectDefinitionProof {
                expanded_rhs,
                residual_equal,
            },
        ))
    }

    // Select this output's RHS from the original shared template body.
    pub(crate) fn expanded_have_obj_equal_rhs_of_instantiated_template(
        &mut self,
        inst: &InstantiatedTemplateObj,
    ) -> RuntimeResult<Option<Obj>> {
        let Some(def) = self.def_template_visible(&inst.template_name) else {
            return Ok(None);
        };
        let TemplateDefEnum::HaveObjEqualStmt(have) = &def.template_def_stmt else {
            return Ok(None);
        };
        let Some(index) = have
            .param_def
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .position(|p| p.name == inst.template_name.local_name())
        else {
            return Ok(None);
        };
        let Some(rhs) = have.objs_equal_to.get(index).cloned() else {
            return Ok(None);
        };
        let Some(subst) = self.template_instance_substitution(def, inst) else {
            return Ok(None);
        };
        match self.inst_obj(&rhs, &subst) {
            Ok(expanded) => Ok(Some(expanded)),
            Err(_) => Ok(None),
        }
    }
}
