//! Binder-object WD: FnSet / AnonymousFn / SetBuilder.
//!
//! Definition-side: open a proof-scope local env, WD param carriers, WD
//! dom/facts under binders, WD ret_set / body. Success carries `local_env`.
//! Example: `fn(x R: x > 0) R` needs `R` WD, binder `x`, WD of `x > 0`, WD of ret `R`.

use super::entry::{ObjWellDefinedProof, VerifyObjWellDefinedResult};
use super::fail_to_verify_obj_well_defined::*;
use super::helper::set_bound_parameters_to_typed_parameter_list;
use super::obj_well_defined_proof_by_def::*;
use crate::ast::fact::{AtomicFact, InFact, QuantifierFreeFact};
use crate::ast::obj::{AnonymousFn, FnSet, FunctionSpace, Obj, SetBuilder, SetFormer};
use crate::ast::param::{ParamType, TypedParameterGroup, TypedParameterList};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::well_defined_results::well_defined_result::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult, VerifyFactWellDefinedResult,
};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::instantiate::quantifier_free_fact_to_fact;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // `fn(x R: x > 0) R` — param types → binders → dom WD → ret_set WD; keep local_env.
    pub(super) fn verify_fn_set_obj_well_definedness(
        &mut self,
        value: &FnSet,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let (inner, local_env) = self.run_in_local_env_and_take_env(|rt| {
            rt.verify_fn_set_obj_well_definedness_in_local(value, verify_state.clone())
        })?;
        match inner {
            Ok((param_type_well_defined, dom_fact_well_defined, ret_set_well_defined)) => {
                let proof = FnSetObjWellDefinedProof {
                    param_type_well_defined,
                    dom_fact_well_defined,
                    ret_set_well_defined,
                    local_env,
                };
                self.finish_binder_obj_success(Obj::FunctionSpace(FunctionSpace::FnSet(value.clone())), verify_state, |p| {
                    ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::FnSet(p))
                }, proof)
            }
            Err(reason) => Ok(VerifyObjWellDefinedResult::Failed {
                obj: Obj::FunctionSpace(FunctionSpace::FnSet(value.clone())),
                reason: FailToVerifyObjWellDefinedResult::FunctionSpace(FailToVerifyFunctionSpaceObjWellDefinedResult::FnSet(reason)),
            }),
        }
    }

    // `fn(x R) R {x + 0}` — same binder scope as FnSet, then body WD + body ∈ ret_set.
    pub(super) fn verify_anonymous_fn_obj_well_definedness(
        &mut self,
        value: &AnonymousFn,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let (inner, local_env) = self.run_in_local_env_and_take_env(|rt| {
            rt.verify_anonymous_fn_obj_well_definedness_in_local(value, verify_state.clone())
        })?;
        match inner {
            Ok((
                param_type_well_defined,
                dom_fact_well_defined,
                ret_set_well_defined,
                body_well_defined,
                body_in_ret_set,
            )) => {
                let proof = AnonymousFnObjWellDefinedProof {
                    param_type_well_defined,
                    dom_fact_well_defined,
                    ret_set_well_defined,
                    body_well_defined,
                    body_in_ret_set,
                    local_env,
                };
                self.finish_binder_obj_success(Obj::FunctionSpace(FunctionSpace::AnonymousFn(value.clone())), verify_state, |p| {
                    ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(p))
                }, proof)
            }
            Err(reason) => Ok(VerifyObjWellDefinedResult::Failed {
                obj: Obj::FunctionSpace(FunctionSpace::AnonymousFn(value.clone())),
                reason: FailToVerifyObjWellDefinedResult::FunctionSpace(FailToVerifyFunctionSpaceObjWellDefinedResult::AnonymousFn(reason)),
            }),
        }
    }

    // `{x R: x > 0}` — param_set WD → binder x → each fact WD; keep local_env.
    pub(super) fn verify_set_builder_obj_well_definedness(
        &mut self,
        value: &SetBuilder,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let (inner, local_env) = self.run_in_local_env_and_take_env(|rt| {
            rt.verify_set_builder_obj_well_definedness_in_local(value, verify_state.clone())
        })?;
        match inner {
            Ok((param_set_well_defined, fact_well_defined)) => {
                let proof = SetBuilderObjWellDefinedProof {
                    param_set_well_defined,
                    fact_well_defined,
                    local_env,
                };
                self.finish_binder_obj_success(Obj::SetFormer(SetFormer::SetBuilder(value.clone())), verify_state, |p| {
                    ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::SetBuilder(p))
                }, proof)
            }
            Err(reason) => Ok(VerifyObjWellDefinedResult::Failed {
                obj: Obj::SetFormer(SetFormer::SetBuilder(value.clone())),
                reason: FailToVerifyObjWellDefinedResult::SetFormer(FailToVerifySetFormerObjWellDefinedResult::SetBuilder(reason)),
            }),
        }
    }

    fn finish_binder_obj_success<P>(
        &mut self,
        obj: Obj,
        verify_state: VerifyState,
        wrap: impl FnOnce(P) -> ObjWellDefinedProofByDef,
        proof: P,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        if verify_state.store_well_defined_fact {
            let wd_id = self.global_ids.allocate_well_definedness_id();
            self.top_exec_env_mut()
                .well_defined_objects
                .record(obj.clone(), wd_id);
        }
        Ok(VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef {
            obj,
            proof: wrap(proof),
        }))
    }

    fn verify_fn_set_obj_well_definedness_in_local(
        &mut self,
        value: &FnSet,
        verify_state: VerifyState,
    ) -> RuntimeResult<
        Result<
            (
                Vec<Box<ObjWellDefinedProof>>,
                Vec<FactWellDefinedProof>,
                Box<ObjWellDefinedProof>,
            ),
            FailToVerifyFnSetObjWellDefined,
        >,
    > {
        if let Some(failed_index) =
            super::helper::set_bound_param_type_cites_earlier_binder(&value.set_bound_parameters)
        {
            return Ok(Err(
                FailToVerifyFnSetObjWellDefined::ParamTypeCitesEarlierBinder { failed_index },
            ));
        }

        let param_type_well_defined =
            match self.verify_set_bound_param_types_well_defined(
                &value.set_bound_parameters,
                verify_state.clone(),
            )? {
                Ok(proofs) => proofs,
                Err((failed_index, succeeded, failed_obj, failed)) => {
                    return Ok(Err(FailToVerifyFnSetObjWellDefined::ParamType {
                        failed_index,
                        succeeded,
                        failed_obj,
                        failed: Box::new(failed),
                    }));
                }
            };

        let typed = set_bound_parameters_to_typed_parameter_list(&value.set_bound_parameters);
        self.define_typed_parameters_in_current_env(&typed, None)?;

        let dom_fact_well_defined = match self.verify_quantifier_free_facts_well_defined(
            &value.dom_facts,
            verify_state.clone(),
        )? {
            Ok(proofs) => proofs,
            Err((failed_index, succeeded_dom, failed_dom)) => {
                return Ok(Err(FailToVerifyFnSetObjWellDefined::DomFact {
                    failed_index,
                    param_type_well_defined,
                    succeeded_dom,
                    failed_dom: Box::new(failed_dom),
                }));
            }
        };

        match self.verify_obj_well_definedness(value.ret_set.as_ref(), verify_state)? {
            VerifyObjWellDefinedResult::Success(ret_set_well_defined) => Ok(Ok((
                param_type_well_defined,
                dom_fact_well_defined,
                Box::new(ret_set_well_defined),
            ))),
            VerifyObjWellDefinedResult::Failed { obj: failed_obj, reason: failed } => {
                Ok(Err(FailToVerifyFnSetObjWellDefined::RetSet {
                    param_type_well_defined,
                    dom_fact_well_defined,
                    failed_obj,
                    failed: Box::new(failed),
                }))
            }
        }
    }

    fn verify_anonymous_fn_obj_well_definedness_in_local(
        &mut self,
        value: &AnonymousFn,
        verify_state: VerifyState,
    ) -> RuntimeResult<
        Result<
            (
                Vec<Box<ObjWellDefinedProof>>,
                Vec<FactWellDefinedProof>,
                Box<ObjWellDefinedProof>,
                Box<ObjWellDefinedProof>,
                VerifyFactResult,
            ),
            FailToVerifyAnonymousFnObjWellDefined,
        >,
    > {
        if let Some(failed_index) = super::helper::set_bound_param_type_cites_earlier_binder(
            &value.body.set_bound_parameters,
        ) {
            return Ok(Err(
                FailToVerifyAnonymousFnObjWellDefined::ParamTypeCitesEarlierBinder {
                    failed_index,
                },
            ));
        }

        let param_type_well_defined =
            match self.verify_set_bound_param_types_well_defined(
                &value.body.set_bound_parameters,
                verify_state.clone(),
            )? {
                Ok(proofs) => proofs,
                Err((failed_index, succeeded, failed_obj, failed)) => {
                    return Ok(Err(FailToVerifyAnonymousFnObjWellDefined::ParamType {
                        failed_index,
                        succeeded,
                        failed_obj,
                        failed: Box::new(failed),
                    }));
                }
            };

        let typed = set_bound_parameters_to_typed_parameter_list(&value.body.set_bound_parameters);
        self.define_typed_parameters_in_current_env(&typed, None)?;

        let dom_fact_well_defined = match self.verify_quantifier_free_facts_well_defined(
            &value.body.dom_facts,
            verify_state.clone(),
        )? {
            Ok(proofs) => proofs,
            Err((failed_index, succeeded_dom, failed_dom)) => {
                return Ok(Err(FailToVerifyAnonymousFnObjWellDefined::DomFact {
                    failed_index,
                    param_type_well_defined,
                    succeeded_dom,
                    failed_dom: Box::new(failed_dom),
                }));
            }
        };

        let ret_set_well_defined =
            match self.verify_obj_well_definedness(value.body.ret_set.as_ref(), verify_state.clone())?
            {
                VerifyObjWellDefinedResult::Success(proof) => Box::new(proof),
                VerifyObjWellDefinedResult::Failed { obj: failed_obj, reason: failed } => {
                    return Ok(Err(FailToVerifyAnonymousFnObjWellDefined::RetSet {
                        param_type_well_defined,
                        dom_fact_well_defined,
                        failed_obj,
                        failed: Box::new(failed),
                    }));
                }
            };

        let body_well_defined =
            match self.verify_obj_well_definedness(value.equal_to.as_ref(), verify_state.clone())? {
                VerifyObjWellDefinedResult::Success(proof) => Box::new(proof),
                VerifyObjWellDefinedResult::Failed { obj: failed_obj, reason: failed } => {
                    return Ok(Err(FailToVerifyAnonymousFnObjWellDefined::Body {
                        param_type_well_defined,
                        dom_fact_well_defined,
                        ret_set_well_defined,
                        failed_obj,
                        failed: Box::new(failed),
                    }));
                }
            };

        let membership_fact = AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: value.equal_to.as_ref().clone(),
            set: value.body.ret_set.as_ref().clone(),
            line_file: None,
        });
        let body_in_ret_set = self.verify_required_atomic_fact(
            membership_fact,
            verify_state,
            "anonymous function body must belong to the return set".to_string(),
        )?;
        if body_in_ret_set.is_failed() {
            return Ok(Err(FailToVerifyAnonymousFnObjWellDefined::BodyInRetSet {
                param_type_well_defined,
                dom_fact_well_defined,
                ret_set_well_defined,
                body_well_defined,
                failed: body_in_ret_set,
            }));
        }

        Ok(Ok((
            param_type_well_defined,
            dom_fact_well_defined,
            ret_set_well_defined,
            body_well_defined,
            body_in_ret_set,
        )))
    }

    fn verify_set_builder_obj_well_definedness_in_local(
        &mut self,
        value: &SetBuilder,
        verify_state: VerifyState,
    ) -> RuntimeResult<
        Result<
            (Box<ObjWellDefinedProof>, Vec<FactWellDefinedProof>),
            FailToVerifySetBuilderObjWellDefined,
        >,
    > {
        let param_set_well_defined =
            match self.verify_obj_well_definedness(value.param_set.as_ref(), verify_state.clone())? {
                VerifyObjWellDefinedResult::Success(proof) => Box::new(proof),
                VerifyObjWellDefinedResult::Failed { obj, reason: failed } => {
                    return Ok(Err(FailToVerifySetBuilderObjWellDefined::ParamSet {
                        obj,
                        failed: Box::new(failed),
                    }));
                }
            };

        let typed = TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![value.param_binding.clone()],
                param_type: ParamType::Obj(value.param_set.as_ref().clone()),
            }],
        };
        self.define_typed_parameters_in_current_env(&typed, None)?;

        let fact_well_defined =
            match self.verify_quantifier_free_facts_well_defined(&value.facts, verify_state)? {
                Ok(proofs) => proofs,
                Err((failed_index, succeeded, failed_fact)) => {
                    return Ok(Err(FailToVerifySetBuilderObjWellDefined::Fact {
                        failed_index,
                        param_set_well_defined,
                        succeeded,
                        failed: Box::new(failed_fact),
                    }));
                }
            };

        Ok(Ok((param_set_well_defined, fact_well_defined)))
    }

    fn verify_set_bound_param_types_well_defined(
        &mut self,
        list: &crate::ast::param::SetBoundParameterList,
        verify_state: VerifyState,
    ) -> RuntimeResult<
        Result<
            Vec<Box<ObjWellDefinedProof>>,
            (
                usize,
                Vec<Box<ObjWellDefinedProof>>,
                Obj,
                FailToVerifyObjWellDefinedResult,
            ),
        >,
    > {
        let mut succeeded = Vec::new();
        let mut index = 0usize;
        for group in &list.groups {
            let param_type = group.param_type.as_ref();
            match self.verify_obj_well_definedness(param_type, verify_state.clone())? {
                VerifyObjWellDefinedResult::Success(proof) => {
                    succeeded.push(Box::new(proof));
                }
                VerifyObjWellDefinedResult::Failed { obj: failed_obj, reason: failed } => {
                    return Ok(Err((index, succeeded, failed_obj, failed)));
                }
            }
            index += 1;
        }
        Ok(Ok(succeeded))
    }

    fn verify_quantifier_free_facts_well_defined(
        &mut self,
        facts: &[QuantifierFreeFact],
        verify_state: VerifyState,
    ) -> RuntimeResult<
        Result<
            Vec<FactWellDefinedProof>,
            (usize, Vec<FactWellDefinedProof>, FailToVerifyFactWellDefinedResult),
        >,
    > {
        let mut succeeded = Vec::with_capacity(facts.len());
        for (failed_index, fact) in facts.iter().enumerate() {
            let as_fact = quantifier_free_fact_to_fact(fact.clone());
            match self.verify_fact_well_definedness(&as_fact, verify_state.clone())? {
                VerifyFactWellDefinedResult::Success(proof) => {
                    // Assume earlier facts in binder scopes (FnSet/AnonymousFn dom,
                    // SetBuilder facts) before later WD checks.
                    let _ = self.store_fact_and_infer(&as_fact)?;
                    succeeded.push(proof);
                }
                VerifyFactWellDefinedResult::Failed(failed) => {
                    return Ok(Err((failed_index, succeeded, failed)));
                }
            }
        }
        Ok(Ok(succeeded))
    }
}
