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

use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::ast::obj::{InstantiatedTemplateObj, Obj};
use crate::new_pipeline::ast::stmt::TemplateDefEnum;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use std::collections::HashMap;

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
            fact_id: self.ids.allocate_fact_id(),
            left: expanded_rhs.clone(),
            right: other_side.clone(),
            line_file: parent_fact.line_file.clone(),
        };
        // Residual search keeps rewrite off so unfold does not loop through
        // rewrite→builtin. Forall stays available for ordinary residual goals.
        let child_state = VerifyState {
            can_use_forall_fact: verify_state.can_use_forall_fact,
            can_use_rewrite: false,
            store_well_defined_fact: false,
        };
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

    // Look up template body; only HaveObjEqual with a single RHS is supported here.
    pub(crate) fn expanded_have_obj_equal_rhs_of_instantiated_template(
        &mut self,
        inst: &InstantiatedTemplateObj,
    ) -> RuntimeResult<Option<Obj>> {
        let plain = inst.template_name.local_name();
        let Some(def) = self.def_template_visible_in_stack(plain) else {
            return Ok(None);
        };
        let TemplateDefEnum::HaveObjEqualStmt(have) = &def.template_def_stmt else {
            return Ok(None);
        };
        if have.objs_equal_to.len() != 1 {
            return Ok(None);
        }
        let expected = def.template_arg_def.ordered_param_ids().len();
        if inst.args.len() != expected {
            return Ok(None);
        }
        let rhs = have.objs_equal_to[0].clone();
        let param_ids = def.template_arg_def.ordered_param_ids();
        let mut subst: HashMap<IdentifierId, Obj> = HashMap::new();
        for (id, arg) in param_ids.into_iter().zip(inst.args.iter()) {
            subst.insert(id, arg.clone());
        }
        match self.inst_obj(&rhs, &subst) {
            Ok(expanded) => Ok(Some(expanded)),
            Err(_) => Ok(None),
        }
    }
}
