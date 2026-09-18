//! Function / atom / standard-set object WD.

use super::entry::ObjWellDefinedProofByDef;
use super::helper::{
    anonymous_fn_body_is_bound_param, set_bound_parameters_to_typed_parameter_list,
};
use crate::new_pipeline::ast::fact::{AtomicFact, InFact};
use crate::new_pipeline::ast::obj::{AnonymousFn, FnObj, FnObjHead, FnSet, Obj};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn verify_atom_obj_well_definedness_by_def(
        &mut self,
        _verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        Ok(ObjWellDefinedProofByDef::leaf())
    }

    pub(super) fn verify_standard_set_obj_well_definedness_by_def(
        &mut self,
        _verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        Ok(ObjWellDefinedProofByDef::leaf())
    }

    pub(super) fn verify_fn_obj_well_definedness_by_def(
        &mut self,
        value: &FnObj,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        // Bare anonymous literal as FnObj head: same binder WD as Obj::AnonymousFn.
        if let FnObjHead::AnonymousFnLiteral(anon) = value.head.as_ref() {
            let mut proof =
                self.verify_anonymous_fn_obj_well_definedness_by_def(anon, verify_state.clone())?;
            for layer in &value.body {
                for arg in layer {
                    proof.child_obj_well_defined.push((
                        arg.as_ref().clone(),
                        self.verify_obj_well_definedness(arg.as_ref(), verify_state.clone())?,
                    ));
                }
            }
            return Ok(proof);
        }

        let mut children = Vec::new();
        self.collect_fn_obj_head_child_objs(&value.head, &mut children);
        for layer in &value.body {
            for arg in layer {
                children.push(arg.as_ref());
            }
        }
        self.verify_objs_as_children(&children, verify_state)
    }

    fn collect_fn_obj_head_child_objs<'a>(&self, head: &'a FnObjHead, children: &mut Vec<&'a Obj>) {
        match head {
            FnObjHead::Identifier(_) => {}
            FnObjHead::AnonymousFnLiteral(_) => {
                // Handled in verify_fn_obj_well_definedness_by_def via binder WD.
            }
            FnObjHead::FiniteSeqListObj(list) => {
                for obj in &list.objs {
                    children.push(obj.as_ref());
                }
            }
            FnObjHead::ObjAtIndex(at) => {
                children.push(at.obj.as_ref());
                children.push(at.index.as_ref());
            }
            FnObjHead::ObjAsStructInstanceWithFieldAccess(access) => {
                children.push(access.obj.as_ref());
                if let Some(carrier) = &access.resolved_struct_carrier {
                    for param in &carrier.params {
                        children.push(param);
                    }
                }
            }
            FnObjHead::InstantiatedTemplateObj(inst) => {
                for arg in &inst.args {
                    children.push(arg);
                }
            }
        }
    }

    pub(super) fn verify_fn_set_obj_well_definedness_by_def(
        &mut self,
        value: &FnSet,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let mut children = Vec::new();
        for group in &value.set_bound_parameters.groups {
            children.push(group.param_type.as_ref());
        }
        children.push(value.ret_set.as_ref());
        self.verify_objs_as_children(&children, verify_state)
    }

    // Anonymous fn WD: ambient carriers, then local binders for the body.
    // Example: `fn(x Z) Z {x + 0}` needs `x Z` in scope before Add WD of `x + 0`.
    // Body ∈ ret_set is required except when the body is exactly a bound parameter
    // (legacy uses param_set ⊆ ret_set there; list-subset search is not ready yet).
    pub(super) fn verify_anonymous_fn_obj_well_definedness_by_def(
        &mut self,
        value: &AnonymousFn,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let mut ambient_children = Vec::new();
        for group in &value.body.set_bound_parameters.groups {
            ambient_children.push(group.param_type.as_ref());
        }
        ambient_children.push(value.body.ret_set.as_ref());
        let mut proof = self.verify_objs_as_children(&ambient_children, verify_state.clone())?;
        if !proof.is_fully_known() {
            return Ok(proof);
        }

        let typed = set_bound_parameters_to_typed_parameter_list(&value.body.set_bound_parameters);
        let identity_body = anonymous_fn_body_is_bound_param(value);
        let ((body_wd, membership), _local_env) = self.run_in_local_env_and_take_env(|rt| {
            rt.define_typed_parameters_in_current_env(&typed)?;
            let body_wd =
                rt.verify_obj_well_definedness(value.equal_to.as_ref(), verify_state.clone())?;
            let membership = if identity_body {
                None
            } else {
                let membership_fact = AtomicFact::InFact(InFact {
                    fact_id: rt.ids.allocate_fact_id(),
                    element: value.equal_to.as_ref().clone(),
                    set: value.body.ret_set.as_ref().clone(),
                    line_file: None,
                });
                Some(rt.verify_required_atomic_fact(
                    membership_fact,
                    verify_state.clone(),
                    "anonymous function body must belong to the return set".to_string(),
                )?)
            };
            Ok((body_wd, membership))
        })?;

        proof
            .child_obj_well_defined
            .push((value.equal_to.as_ref().clone(), body_wd));
        if let Some(membership) = membership {
            proof.requirement_fact_verified.push(membership);
        }
        Ok(proof)
    }
}
