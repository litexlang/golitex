//! Function / atom / standard-set object WD.

use super::fail_to_verify_obj_well_defined::{
    FailToVerifyFnObjObjWellDefined, FailToVerifyFnRangeObjWellDefined,
    FailToVerifyIdentifierObjWellDefined, FailToVerifyObjWellDefinedResult,
};
use super::helper::{set_bound_parameter_count, set_bound_params_to_arg_map};
use super::obj_well_defined_by_def_common::ObjWellDefinedByDefCommonStages;
use super::obj_well_defined_proof_by_def::{
    FnObjObjWellDefinedProof, FnRangeObjWellDefinedProof, IdentifierObjWellDefinedProof,
    NumberObjWellDefinedProof, ObjWellDefinedProofByDef, StandardSetObjWellDefinedProof,
};
use super::entry::{ObjWellDefinedProof, VerifyObjWellDefinedResult};
use crate::new_pipeline::ast::fact::{AtomicFact, InFact};
use crate::new_pipeline::ast::obj::{FnObj, FnObjHead, FnRange, FnSet, IdentifierObj, Obj};
use crate::new_pipeline::exec_env::exec_env::SpecialObjProperty;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::runtime_ids::FactId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Identifier: must be defined in the exec-env stack (let/have/binder/…).
    // Example: after `have a R = 1`, WD of `a` succeeds; bare `ghost` fails Undefined.
    pub(super) fn verify_identifier_obj_well_definedness(
        &mut self,
        value: &IdentifierObj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let name = match value {
            IdentifierObj::Plain { name, .. } => name.clone(),
            // Qualified names are treated as already resolved references.
            IdentifierObj::WithExportFileId { .. }
            | IdentifierObj::WithModAndExportFileId { .. } => {
                return self.finish_leaf_obj_success(Obj::Identifier(value.clone()), verify_state);
            }
        };
        if !self.identifier_defined_in_stack(&name) {
            return Ok(VerifyObjWellDefinedResult::Failed(
                FailToVerifyObjWellDefinedResult::Identifier(
                    FailToVerifyIdentifierObjWellDefined::Undefined {
                        obj: Obj::Identifier(value.clone()),
                    },
                ),
            ));
        }
        self.finish_leaf_obj_success(Obj::Identifier(value.clone()), verify_state)
    }

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

    fn finish_leaf_obj_success(
        &mut self,
        obj: Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        if verify_state.store_well_defined_fact {
            let wd_id = self.ids.allocate_well_definedness_id();
            self.top_exec_env_mut()
                .well_defined_objects
                .record(obj.clone(), wd_id);
        }
        let by_def = match &obj {
            Obj::Identifier(_) => ObjWellDefinedProofByDef::Identifier(IdentifierObjWellDefinedProof::new()),
            Obj::Number(_) => ObjWellDefinedProofByDef::Number(NumberObjWellDefinedProof::new()),
            Obj::StandardSet(_) => {
                ObjWellDefinedProofByDef::StandardSet(StandardSetObjWellDefinedProof::new())
            }
            _ => ObjWellDefinedProofByDef::Identifier(IdentifierObjWellDefinedProof::new()),
        };
        Ok(VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef(
            by_def,
        )))
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
        // Bare anonymous literal as FnObj head: reuse Obj::AnonymousFn binder WD.
        if let FnObjHead::AnonymousFnLiteral(anon) = value.head.as_ref() {
            let anon_obj = Obj::AnonymousFn(anon.as_ref().clone());
            let mut children = vec![(
                anon_obj.clone(),
                self.verify_obj_well_definedness(&anon_obj, verify_state.clone())?,
            )];
            for layer in &value.body {
                for arg in layer {
                    children.push((
                        arg.as_ref().clone(),
                        self.verify_obj_well_definedness(arg.as_ref(), verify_state.clone())?,
                    ));
                }
            }
            return Ok(ObjWellDefinedByDefCommonStages {
                child_obj_well_defined: children,
                requirement_fact_verified: Vec::new(),
            });
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
                // Handled in verify_fn_obj_well_definedness_by_def via AnonymousFn WD.
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

    // Visible InFunctionSet rows for `obj` and its equality-class neighbors.
    pub(super) fn collect_in_function_set_candidates(&self, obj: &Obj) -> Vec<(FnSet, FactId)> {
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

    // fn_range(f): children, then f must have a visible InFunctionSet registration.
    // Example: after `let f = fn(x R) R {x}`, `fn_range(f)` is WD.
    pub(super) fn verify_fn_range_obj_well_definedness(
        &mut self,
        value: &FnRange,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let stages = self.verify_unary_obj_well_definedness_by_def(
            value.function.as_ref(),
            verify_state.clone(),
        )?;
        if !stages.is_fully_known() {
            return Ok(VerifyObjWellDefinedResult::Failed(
                FailToVerifyObjWellDefinedResult::FnRange(FailToVerifyFnRangeObjWellDefined::Domain(
                    stages.into_common_fail(&Obj::FnRange(value.clone())),
                )),
            ));
        }
        if self
            .collect_in_function_set_candidates(value.function.as_ref())
            .is_empty()
        {
            return Ok(VerifyObjWellDefinedResult::Failed(
                FailToVerifyObjWellDefinedResult::FnRange(
                    FailToVerifyFnRangeObjWellDefined::NotInFunctionSet,
                ),
            ));
        }
        if verify_state.store_well_defined_fact {
            let wd_id = self.ids.allocate_well_definedness_id();
            self.top_exec_env_mut()
                .well_defined_objects
                .record(Obj::FnRange(value.clone()), wd_id);
        }
        Ok(VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef(
            ObjWellDefinedProofByDef::FnRange(FnRangeObjWellDefinedProof::from_stages(stages)),
        )))
    }

    pub(super) fn obj_has_in_function_set(&self, obj: &Obj) -> bool {
        !self.collect_in_function_set_candidates(obj).is_empty()
    }
}
