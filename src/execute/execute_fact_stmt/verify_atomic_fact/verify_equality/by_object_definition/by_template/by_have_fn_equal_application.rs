//! Equality by object definition: unfold `\Name<args>(…)` when the template body is `have fn … = …`.
//!
//! Mathematical property:
//!   If `template<params>:` defines `have fn name(…) T = body`, then
//!   `\name<args>(fn_args) = subst(body)` under the combined substitution.
//!
//! Example:
//!   template<S set, z S>:
//!       have fn const_on_S(x S) S = z
//!   \const_on_S<R, 0>(2) = 0

use crate::ast::fact::EqualFact;
use crate::ast::obj::{FnObjHead, Obj};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

pub struct ByUnfoldInstantiatedTemplateHaveFnEqualApplicationObjectDefinitionProof {
    pub normalization:
        super::super::by_fn_application::normalize_function_body::FunctionBodyNormalizationProof,
    pub residual_equal: VerifyFactResult,
}

impl Runtime {
    pub(crate) fn try_unfold_instantiated_template_have_fn_equal_application(
        &mut self,
        app_side: &Obj,
        other_side: &Obj,
        parent_fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<
        Option<ByUnfoldInstantiatedTemplateHaveFnEqualApplicationObjectDefinitionProof>,
    > {
        let Obj::FnObj(fn_obj) = app_side else {
            return Ok(None);
        };
        let FnObjHead::InstantiatedTemplateObj(_) = fn_obj.head.as_ref() else {
            return Ok(None);
        };
        let Some(normalization) =
            self.normalize_function_body(app_side, other_side, verify_state)?
        else {
            return Ok(None);
        };

        let residual = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: normalization.expanded_body.clone(),
            right: other_side.clone(),
            line_file: parent_fact.line_file.clone(),
        };
        let child_state = verify_state.without_rewrite();
        let residual_equal = self.verify_equal_fact(&residual, child_state)?;
        if residual_equal.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            ByUnfoldInstantiatedTemplateHaveFnEqualApplicationObjectDefinitionProof {
                normalization,
                residual_equal,
            },
        ))
    }
}
