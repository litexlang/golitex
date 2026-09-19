//! Function / atom / standard-set object WD.

use super::fail_to_verify_obj_well_defined::{
    FailToVerifyFnObjObjWellDefined, FailToVerifyObjWellDefinedResult,
};
use super::helper::{
    anonymous_fn_body_is_bound_param, set_bound_parameter_count, set_bound_parameters_to_typed_parameter_list,
    set_bound_params_to_arg_map,
};
use super::obj_well_defined_by_def_common::ObjWellDefinedByDefCommonStages;
use super::obj_well_defined_proof_by_def::{FnObjObjWellDefinedProof, ObjWellDefinedProofByDef};
use super::entry::{ObjWellDefinedProof, VerifyObjWellDefinedResult};
use crate::new_pipeline::ast::fact::{AtomicFact, InFact};
use crate::new_pipeline::ast::obj::{AnonymousFn, FnObj, FnObjHead, FnSet, Obj};
use crate::new_pipeline::exec_env::exec_env::SpecialObjProperty;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::runtime_ids::FactId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn verify_atom_obj_well_definedness_by_def(
        &mut self,
        _verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        Ok(ObjWellDefinedByDefCommonStages::leaf())
    }

    pub(super) fn verify_standard_set_obj_well_definedness_by_def(
        &mut self,
        _verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        Ok(ObjWellDefinedByDefCommonStages::leaf())
    }

    // Identifier-headed application: look up InFunctionSet, check arity, param $in,
    // and instantiated dom_facts. Example: after `let f = fn(x R) R {x}`, WD of `f(a)`
    // needs `a $in R` (and any `dom_facts` under that signature).
    pub(super) fn verify_identifier_headed_fn_obj_well_definedness(
        &mut self,
        value: &FnObj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let FnObjHead::Identifier(head_id) = value.head.as_ref() else {
            return Err(crate::new_pipeline::runtime::RuntimeError::InternalBug(
                "verify_identifier_headed_fn_obj expects Identifier head".to_string(),
            ));
        };
        let head_obj = Obj::Identifier(head_id.clone());
        let candidates = self.collect_in_function_set_candidates(&head_obj);
        if candidates.is_empty() {
            return Ok(VerifyObjWellDefinedResult::Failed(
                FailToVerifyObjWellDefinedResult::FnObj(
                    FailToVerifyFnObjObjWellDefined::NotInFunctionSet,
                ),
            ));
        }
        if value.body.is_empty() {
            return Ok(VerifyObjWellDefinedResult::Failed(
                FailToVerifyObjWellDefinedResult::FnObj(FailToVerifyFnObjObjWellDefined::Domain(
                    ObjWellDefinedByDefCommonStages::leaf().into_common_fail(&Obj::FnObj(value.clone())),
                )),
            ));
        }

        let mut last_domain_fail: Option<ObjWellDefinedByDefCommonStages> = None;
        for (fn_set, fact_id) in candidates {
            match self.try_verify_fn_obj_against_fn_set(value, &fn_set, verify_state.clone())? {
                Ok(stages) => {
                    let proof = FnObjObjWellDefinedProof {
                        applied_fn_set: Some((fn_set, fact_id)),
                        child_obj_well_defined: stages.child_obj_well_defined,
                        requirement_fact_verified: stages.requirement_fact_verified,
                    };
                    if verify_state.store_well_defined_fact {
                        let wd_id = self.ids.allocate_well_definedness_id();
                        self.top_exec_env_mut()
                            .well_defined_objects
                            .record(Obj::FnObj(value.clone()), wd_id);
                    }
                    return Ok(VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef(
                        ObjWellDefinedProofByDef::FnObj(proof),
                    )));
                }
                Err(stages) => {
                    last_domain_fail = Some(stages);
                }
            }
        }

        let fail_stages = last_domain_fail.unwrap_or_else(ObjWellDefinedByDefCommonStages::leaf);
        Ok(VerifyObjWellDefinedResult::Failed(
            FailToVerifyObjWellDefinedResult::FnObj(FailToVerifyFnObjObjWellDefined::Domain(
                fail_stages.into_common_fail(&Obj::FnObj(value.clone())),
            )),
        ))
    }

    pub(super) fn verify_fn_obj_well_definedness_by_def(
        &mut self,
        value: &FnObj,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
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

        // Identifier head is handled in verify_identifier_headed_fn_obj_well_definedness.
        if matches!(value.head.as_ref(), FnObjHead::Identifier(_)) {
            return Ok(ObjWellDefinedByDefCommonStages::leaf());
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
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
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
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
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

    // Visible InFunctionSet rows for `obj` and its equality-class neighbors.
    fn collect_in_function_set_candidates(&self, obj: &Obj) -> Vec<(FnSet, FactId)> {
        let mut keys = self.known_equality_class_keys(obj);
        let self_ir = obj.ir();
        if !keys.iter().any(|k| k == &self_ir) {
            keys.push(self_ir);
        }
        let mut out = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            for key in &keys {
                let Some(props) = env.special_object_properties.get(key) else {
                    continue;
                };
                for prop in props {
                    if let SpecialObjProperty::InFunctionSet((fn_set, fact_id)) = prop {
                        out.push((fn_set.clone(), *fact_id));
                    }
                }
            }
        }
        out
    }

    // Ok(stages) = candidate matched; Err(stages) = soft miss for this candidate.
    fn try_verify_fn_obj_against_fn_set(
        &mut self,
        value: &FnObj,
        fn_set: &FnSet,
        verify_state: VerifyState,
    ) -> RuntimeResult<Result<ObjWellDefinedByDefCommonStages, ObjWellDefinedByDefCommonStages>> {
        let (proof, _local_env) = self.run_in_local_env_and_take_env(|rt| {
            rt.verify_fn_obj_against_fn_set_in_local(value, fn_set, verify_state)
        })?;
        Ok(proof)
    }

    fn verify_fn_obj_against_fn_set_in_local(
        &mut self,
        value: &FnObj,
        fn_set: &FnSet,
        verify_state: VerifyState,
    ) -> RuntimeResult<Result<ObjWellDefinedByDefCommonStages, ObjWellDefinedByDefCommonStages>> {
        let mut proof = ObjWellDefinedByDefCommonStages::leaf();
        let mut space = fn_set.clone();
        let last = value.body.len() - 1;
        for (layer_index, layer) in value.body.iter().enumerate() {
            let args: Vec<Obj> = layer.iter().map(|a| a.as_ref().clone()).collect();
            let expected = set_bound_parameter_count(&space.set_bound_parameters);
            if args.len() != expected {
                return Ok(Err(proof));
            }
            for arg in &args {
                let child = self.verify_obj_well_definedness(arg, verify_state.clone())?;
                let failed = child.is_failed();
                proof.child_obj_well_defined.push((arg.clone(), child));
                if failed {
                    return Ok(Err(proof));
                }
            }
            let mut arg_index = 0;
            for group in &space.set_bound_parameters.groups {
                let param_type = group.param_type.as_ref();
                for _param in &group.params {
                    let arg = &args[arg_index];
                    let membership = AtomicFact::InFact(InFact {
                        fact_id: self.ids.allocate_fact_id(),
                        element: arg.clone(),
                        set: param_type.clone(),
                        line_file: None,
                    });
                    let req = self.verify_required_atomic_fact(
                        membership,
                        verify_state.clone(),
                        format!("argument does not belong to parameter type"),
                    )?;
                    let failed = req.is_failed();
                    proof.requirement_fact_verified.push(req);
                    if failed {
                        return Ok(Err(proof));
                    }
                    arg_index += 1;
                }
            }
            let subst = set_bound_params_to_arg_map(&space.set_bound_parameters, &args);
            for dom in &space.dom_facts {
                let instantiated = match self.inst_quantifier_free_fact(dom, &subst) {
                    Ok(f) => f,
                    Err(_) => return Ok(Err(proof)),
                };
                let req =
                    self.verify_required_quantifier_free_fact(instantiated, verify_state.clone())?;
                let failed = req.is_failed();
                proof.requirement_fact_verified.push(req);
                if failed {
                    return Ok(Err(proof));
                }
            }
            if layer_index < last {
                let next_ret = match self.inst_obj(space.ret_set.as_ref(), &subst) {
                    Ok(o) => o,
                    Err(_) => return Ok(Err(proof)),
                };
                // Curried return may be FnSet or an anonymous fn value.
                space = match next_ret {
                    Obj::FnSet(next) => next,
                    Obj::AnonymousFn(anon) => anon.body,
                    _ => return Ok(Err(proof)),
                };
            }
        }
        Ok(Ok(proof))
    }
}
