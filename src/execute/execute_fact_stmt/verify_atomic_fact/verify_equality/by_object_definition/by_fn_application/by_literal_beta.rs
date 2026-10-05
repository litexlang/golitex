//! Beta reduction of the actual literal whose application the parent checked.

use crate::ast::fact::EqualFact;
use crate::ast::obj::{FnObjHead, Obj};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::well_defined_result::EqualFactWellDefinedProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::EqualFactSearchedProof;
use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
use crate::runtime::{Runtime, RuntimeResult};

use super::super::helper::{set_bound_parameter_count, set_bound_params_to_arg_map};

pub struct ByLiteralBetaObjectDefinitionProof {
    pub parent_well_defined_side: ParentEqualitySide,
    pub expanded_body: Obj,
    pub residual_equal: EqualFact,
    pub residual_proof: Box<EqualFactSearchedProof>,
}

pub enum ParentEqualitySide {
    Left,
    Right,
}

impl Runtime {
    pub(in crate::execute) fn try_literal_beta_with_parent_well_definedness(
        &mut self,
        fact: &EqualFact,
        parent_wd: &EqualFactWellDefinedProof,
        state: VerifyState,
    ) -> RuntimeResult<Option<ByLiteralBetaObjectDefinitionProof>> {
        let Some(child) = state.for_premises(VerifyStateLevel::DefinitionAndForall) else {
            return Ok(None);
        };
        if parent_wd.left.obj() != &fact.left || parent_wd.right.obj() != &fact.right {
            return Ok(None);
        }
        for (app_side, other_side, side) in [
            (&fact.left, &fact.right, ParentEqualitySide::Left),
            (&fact.right, &fact.left, ParentEqualitySide::Right),
        ] {
            let Obj::FnObj(app) = app_side else { continue };
            let FnObjHead::AnonymousFnLiteral(literal) = app.head.as_ref() else {
                continue;
            };
            if app.body.len() != 1 {
                continue;
            }
            let args: Vec<Obj> = app.body[0].iter().map(|v| v.as_ref().clone()).collect();
            if args.len() != set_bound_parameter_count(&literal.body.set_bound_parameters) {
                continue;
            }
            let subst = set_bound_params_to_arg_map(&literal.body.set_bound_parameters, &args);
            let Ok(expanded_body) = self.inst_obj(literal.equal_to.as_ref(), &subst) else {
                continue;
            };
            let residual_equal = EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: expanded_body.clone(),
                right: other_side.clone(),
                line_file: fact.line_file.clone(),
            };
            // Parent WD checked this exact literal, its arguments and guards.
            // Substitution preserves its body WD; search only residual truth
            // at the ordinary definition-premise ceiling. A named alias may
            // select a different body, so it cannot use this certificate.
            let Some(residual_proof) = self.search_equal_fact_proof(&residual_equal, child)? else {
                continue;
            };
            return Ok(Some(ByLiteralBetaObjectDefinitionProof {
                parent_well_defined_side: side,
                expanded_body,
                residual_equal,
                residual_proof: Box::new(residual_proof),
            }));
        }
        Ok(None)
    }
}
