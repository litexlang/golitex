//! Function / atom / standard-set object WD.

use super::entry::{ObjWellDefinedProof, VerifyObjWellDefinedResult};
use super::fail_to_verify_obj_well_defined::*;
use super::helper::{
    fn_obj_head_as_obj, set_bound_parameter_count, set_bound_params_to_arg_map,
};
use super::obj_well_defined_by_def_common::ObjWellDefinedByDefCommonStages;
use super::obj_well_defined_proof_by_def::*;
use crate::ast::fact::{AtomicFact, EqualFact, Fact, InFact};
use crate::ast::obj::{
    FnObj, FnObjHead, FnRange, FnSet, FunctionSpace, IdentifierObj, Literal, Obj,
};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::KnownEqualityPathProof;
use crate::exec_env::SpecialProperty;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::equivalence_class_graph::equivalence_class_members_with_paths_in_adjacency;
use crate::runtime::runtime_ids::FactId;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Identifier: must be defined in the exec-env stack (let/have/binder/…).
    // Example: after `have a R = 1`, WD of `a` succeeds; bare `ghost` fails Undefined.
    pub(super) fn verify_identifier_obj_well_definedness(
        &mut self,
        value: &IdentifierObj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        if self.stored_identifier_definition_visible(value).is_none() {
            let obj = Obj::Identifier(value.clone());
            return Ok(VerifyObjWellDefinedResult::Failed {
                obj: obj.clone(),
                reason: FailToVerifyObjWellDefinedResult::Identifier(
                    FailToVerifyIdentifierObjWellDefined::Undefined { obj },
                ),
            });
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

        let by_def = match &obj {
            Obj::Identifier(_) => {
                ObjWellDefinedProofByDef::Identifier(IdentifierObjWellDefinedProof::new())
            }
            Obj::Literal(Literal::Number(_)) => ObjWellDefinedProofByDef::Literal(
                LiteralObjWellDefinedProofByDef::Number(NumberObjWellDefinedProof::new()),
            ),
            Obj::StandardSet(_) => {
                ObjWellDefinedProofByDef::StandardSet(StandardSetObjWellDefinedProof::new())
            }
            _ => ObjWellDefinedProofByDef::Identifier(IdentifierObjWellDefinedProof::new()),
        };
        Ok(VerifyObjWellDefinedResult::Success(
            ObjWellDefinedProof::ByDef {
                obj,
                proof: by_def,
            },
        ))
    }

    // Identifier- or template-instance-headed application: look up InFunctionSet,
    // check arity, param $in, and instantiated dom_facts.
    // Example: after `let f = fn(x R) R {x}`, WD of `f(a)` needs `a $in R`.
    // Example: after a `have fn` template instance WD, `\const_on_S<R, 0>(2)`.
    pub(super) fn verify_in_function_set_headed_fn_obj_well_definedness(
        &mut self,
        value: &FnObj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let head_obj = match value.head.as_ref() {
            FnObjHead::Identifier(head_id) => Obj::Identifier(head_id.clone()),
            FnObjHead::InstantiatedTemplateObj(inst) => {
                Obj::InstantiatedTemplateObj(inst.clone())
            }
            _ => {
                return Err(crate::runtime::RuntimeError::InternalBug(
                    "verify_in_function_set_headed_fn_obj expects Identifier or InstantiatedTemplateObj head"
                        .to_string(),
                ));
            }
        };
        let root = Obj::FnObj(value.clone());
        if value.body.is_empty() {
            return Ok(VerifyObjWellDefinedResult::Failed {
                obj: root.clone(), reason: FailToVerifyObjWellDefinedResult::FnObj(
                    FailToVerifyFnObjObjWellDefined::Domain(ObjWellDefinedByDefCommonStages::leaf().into_common_fail(&root))),
            });
        }
        let mut finite_domain_failure = None;
        for source in self.finite_function_signatures(&head_obj) {
            let head_wd = self.verify_obj_well_definedness(&head_obj, verify_state)?;
            if head_wd.is_failed() { continue; }
            match self.try_verify_fn_obj_against_fn_set(value, &source.signature, verify_state)? {
                Ok(mut stages) => {
                    stages.child_obj_well_defined.insert(0, head_wd);
                    let (child_obj_well_defined, requirement_fact_verified) = stages.into_success_child_proofs();
                    return Ok(VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef {
                        obj: root, proof: ObjWellDefinedProofByDef::FnObj(FnObjObjWellDefinedProof {
                            domain_fn_set: Some(FnObjDomainFnSetEvidence::FiniteFunction(Box::new(source))),
                            child_obj_well_defined, requirement_fact_verified,
                        }),
                    }));
                }
                Err(stages) => finite_domain_failure = Some(stages),
            }
        }
        // An equality alias retains the checked template's callable contract.
        // Instance WD still checks template parameters and guards before use.
        for (candidate, path) in equivalence_class_members_with_paths_in_adjacency(
            &self.visible_equivalence_class_adjacency(), &head_obj,
        ) {
            let Obj::InstantiatedTemplateObj(instance) = &candidate else { continue; };
            let head_wd = self.verify_obj_well_definedness(&candidate, verify_state)?;
            if head_wd.is_failed() {
                if path.is_empty() {
                    return Ok(VerifyObjWellDefinedResult::Failed {
                        obj: root,
                        reason: FailToVerifyObjWellDefinedResult::FnObj(
                            FailToVerifyFnObjObjWellDefined::Domain(
                                ObjWellDefinedByDefCommonStages::from_children(vec![head_wd])
                                    .into_common_fail(&Obj::FnObj(value.clone())),
                            ),
                        ),
                    });
                }
                continue;
            }
            if let Some(fn_set) = self.instantiated_template_function_signature(instance) {
                match self.try_verify_fn_obj_against_fn_set(value, &fn_set, verify_state)? {
                    Ok(mut stages) => {
                        stages.child_obj_well_defined.insert(0, head_wd);
                        let (child_obj_well_defined, requirement_fact_verified) = stages.into_success_child_proofs();
                        return Ok(VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef {
                            obj: root,
                            proof: ObjWellDefinedProofByDef::FnObj(FnObjObjWellDefinedProof {
                                domain_fn_set: Some(FnObjDomainFnSetEvidence::TemplateDefinition {
                                    fn_set, function_equal: KnownEqualityPathProof::new(path),
                                }),
                                child_obj_well_defined,
                                requirement_fact_verified,
                            }),
                        }));
                    }
                    Err(stages) if path.is_empty() => return Ok(VerifyObjWellDefinedResult::Failed {
                        obj: root.clone(),
                        reason: FailToVerifyObjWellDefinedResult::FnObj(FailToVerifyFnObjObjWellDefined::Domain(stages.into_common_fail(&root))),
                    }),
                    Err(_) => continue,
                }
            }
        }
        let candidates = self.collect_in_function_set_candidates(&head_obj);
        if candidates.is_empty() {
            if let Some(stages) = finite_domain_failure {
                return Ok(VerifyObjWellDefinedResult::Failed {
                    obj: root.clone(), reason: FailToVerifyObjWellDefinedResult::FnObj(
                        FailToVerifyFnObjObjWellDefined::Domain(stages.into_common_fail(&root))),
                });
            }
            return Ok(VerifyObjWellDefinedResult::Failed {
                obj: root,
                reason: FailToVerifyObjWellDefinedResult::FnObj(
                    FailToVerifyFnObjObjWellDefined::NotInFunctionSet,
                ),
            });
        }
        if value.body.is_empty() {
            return Ok(VerifyObjWellDefinedResult::Failed {
                obj: root,
                reason: FailToVerifyObjWellDefinedResult::FnObj(
                    FailToVerifyFnObjObjWellDefined::Domain(
                        ObjWellDefinedByDefCommonStages::leaf()
                            .into_common_fail(&Obj::FnObj(value.clone())),
                    ),
                ),
            });
        }

        let mut last_domain_fail: Option<ObjWellDefinedByDefCommonStages> = None;
        for (fn_set, fact_id) in candidates {
            let source = match self.fact_by_id_in_stack(fact_id) {
                Some(Fact::AtomicFact(AtomicFact::InFact(fact))) => SpecialProperty::Membership(fact.clone()),
                Some(Fact::AtomicFact(AtomicFact::EqualFact(fact))) => SpecialProperty::Equality(fact.clone()),
                _ => continue,
            };
            let Some(subject) = source.function_subject() else { continue; };
            let Some(path) = self.equivalence_class_path(&head_obj, subject) else { continue; };
            match self.try_verify_fn_obj_against_fn_set(value, &fn_set, verify_state.clone())? {
                Ok(stages) => {
                    let (child_obj_well_defined, requirement_fact_verified) =
                        stages.into_success_child_proofs();
                    let proof = FnObjObjWellDefinedProof {
                        domain_fn_set: Some(FnObjDomainFnSetEvidence::InFunctionSet {
                            fn_set,
                            fact_id,
                            function_equal: KnownEqualityPathProof::new(path),
                        }),
                        child_obj_well_defined,
                        requirement_fact_verified,
                    };

                    return Ok(VerifyObjWellDefinedResult::Success(
                        ObjWellDefinedProof::ByDef {
                            obj: root,
                            proof: ObjWellDefinedProofByDef::FnObj(proof),
                        },
                    ));
                }
                Err(stages) => {
                    last_domain_fail = Some(stages);
                }
            }
        }

        let fail_stages = last_domain_fail.unwrap_or_else(ObjWellDefinedByDefCommonStages::leaf);
        Ok(VerifyObjWellDefinedResult::Failed {
            obj: Obj::FnObj(value.clone()),
            reason: FailToVerifyObjWellDefinedResult::FnObj(
                FailToVerifyFnObjObjWellDefined::Domain(
                    fail_stages.into_common_fail(&Obj::FnObj(value.clone())),
                ),
            ),
        })
    }

    // `fn(x R: x > 0) R {x}(a)`: WD the literal, then check args against its own FnSet
    // (param membership + instantiated dom_facts). No InFunctionSet lookup.
    // Example: `fn(x R: x > 0) R {x}(1)` needs `1 $in R` and `1 > 0`.
    pub(super) fn verify_anonymous_fn_literal_headed_fn_obj_well_definedness(
        &mut self,
        value: &FnObj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let FnObjHead::AnonymousFnLiteral(anon) = value.head.as_ref() else {
            return Err(crate::runtime::RuntimeError::InternalBug(
                "verify_anonymous_fn_literal_headed_fn_obj expects AnonymousFnLiteral head"
                    .to_string(),
            ));
        };
        let root = Obj::FnObj(value.clone());
        let anon_obj = Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon.as_ref().clone()));
        let head_wd = self.verify_obj_well_definedness(&anon_obj, verify_state.clone())?;
        if head_wd.is_failed() {
            return Ok(VerifyObjWellDefinedResult::Failed {
                obj: root,
                reason: FailToVerifyObjWellDefinedResult::FnObj(
                    FailToVerifyFnObjObjWellDefined::Domain(
                        ObjWellDefinedByDefCommonStages::from_children(vec![head_wd])
                            .into_common_fail(&Obj::FnObj(value.clone())),
                    ),
                ),
            });
        }
        if value.body.is_empty() {
            return Ok(VerifyObjWellDefinedResult::Failed {
                obj: root,
                reason: FailToVerifyObjWellDefinedResult::FnObj(
                    FailToVerifyFnObjObjWellDefined::Domain(
                        ObjWellDefinedByDefCommonStages::from_children(vec![head_wd])
                            .into_common_fail(&Obj::FnObj(value.clone())),
                    ),
                ),
            });
        }

        let fn_set = anon.body.clone();
        match self.try_verify_fn_obj_against_fn_set(value, &fn_set, verify_state.clone())? {
            Ok(mut stages) => {
                let mut children = vec![head_wd];
                children.append(&mut stages.child_obj_well_defined);
                let (child_proofs, _) = ObjWellDefinedByDefCommonStages::from_children(children)
                    .into_success_child_proofs();
                let proof = FnObjObjWellDefinedProof {
                    domain_fn_set: Some(FnObjDomainFnSetEvidence::AnonymousLiteral { fn_set }),
                    child_obj_well_defined: child_proofs,
                    requirement_fact_verified: stages.requirement_fact_verified,
                };

                Ok(VerifyObjWellDefinedResult::Success(
                    ObjWellDefinedProof::ByDef {
                        obj: root,
                        proof: ObjWellDefinedProofByDef::FnObj(proof),
                    },
                ))
            }
            Err(mut stages) => {
                let mut children = vec![head_wd];
                children.append(&mut stages.child_obj_well_defined);
                stages.child_obj_well_defined = children;
                Ok(VerifyObjWellDefinedResult::Failed {
                    obj: root,
                    reason: FailToVerifyObjWellDefinedResult::FnObj(
                        FailToVerifyFnObjObjWellDefined::Domain(
                            stages.into_common_fail(&Obj::FnObj(value.clone())),
                        ),
                    ),
                })
            }
        }
    }

    // `p.f(a)`: WD the FieldAccess head, then domain-check args against the field's
    // declared FnSet type (or a stored InFunctionSet on the field object).
    // Example: after `struct Bundle: f fn(x R) R` and `forall p &Bundle:`, WD of `p.f(0)`.
    pub(super) fn verify_field_access_headed_fn_obj_well_definedness(
        &mut self,
        value: &FnObj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let FnObjHead::FieldAccess(access) = value.head.as_ref() else {
            return Err(crate::runtime::RuntimeError::InternalBug(
                "verify_field_access_headed_fn_obj expects FieldAccess head".to_string(),
            ));
        };
        let root = Obj::FnObj(value.clone());
        let head_obj = fn_obj_head_as_obj(value.head.as_ref());
        let head_wd = self.verify_obj_well_definedness(&head_obj, verify_state.clone())?;
        if head_wd.is_failed() {
            return Ok(VerifyObjWellDefinedResult::Failed {
                obj: root,
                reason: FailToVerifyObjWellDefinedResult::FnObj(
                    FailToVerifyFnObjObjWellDefined::Domain(
                        ObjWellDefinedByDefCommonStages::from_children(vec![head_wd])
                            .into_common_fail(&Obj::FnObj(value.clone())),
                    ),
                ),
            });
        }
        if value.body.is_empty() {
            return Ok(VerifyObjWellDefinedResult::Failed {
                obj: root,
                reason: FailToVerifyObjWellDefinedResult::FnObj(
                    FailToVerifyFnObjObjWellDefined::Domain(
                        ObjWellDefinedByDefCommonStages::from_children(vec![head_wd])
                            .into_common_fail(&Obj::FnObj(value.clone())),
                    ),
                ),
            });
        }

        let mut candidate_spaces: Vec<FnSet> = self
            .collect_in_function_set_candidates(&head_obj)
            .into_iter()
            .map(|(fs, _)| fs)
            .collect();
        if let Some(field_type) = self.resolve_field_access_field_type(access) {
            match field_type {
                Obj::FunctionSpace(FunctionSpace::FnSet(fs)) => candidate_spaces.push(fs),
                Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) => {
                    candidate_spaces.push(anon.body)
                }
                _ => {}
            }
        }
        if candidate_spaces.is_empty() {
            return Ok(VerifyObjWellDefinedResult::Failed {
                obj: root,
                reason: FailToVerifyObjWellDefinedResult::FnObj(
                    FailToVerifyFnObjObjWellDefined::NotInFunctionSet,
                ),
            });
        }

        let mut last_domain_fail: Option<ObjWellDefinedByDefCommonStages> = None;
        for fn_set in candidate_spaces {
            match self.try_verify_fn_obj_against_fn_set(value, &fn_set, verify_state.clone())? {
                Ok(mut stages) => {
                    let mut children = vec![head_wd];
                    children.append(&mut stages.child_obj_well_defined);
                    let (child_proofs, _) = ObjWellDefinedByDefCommonStages::from_children(children)
                        .into_success_child_proofs();
                    let proof = FnObjObjWellDefinedProof {
                        domain_fn_set: Some(FnObjDomainFnSetEvidence::AnonymousLiteral { fn_set }),
                        child_obj_well_defined: child_proofs,
                        requirement_fact_verified: stages.requirement_fact_verified,
                    };

                    return Ok(VerifyObjWellDefinedResult::Success(
                        ObjWellDefinedProof::ByDef {
                            obj: root,
                            proof: ObjWellDefinedProofByDef::FnObj(proof),
                        },
                    ));
                }
                Err(stages) => {
                    last_domain_fail = Some(stages);
                }
            }
        }

        let fail_stages = match last_domain_fail {
            Some(mut stages) => {
                let mut children = vec![head_wd];
                children.append(&mut stages.child_obj_well_defined);
                stages.child_obj_well_defined = children;
                stages
            }
            None => ObjWellDefinedByDefCommonStages::from_children(vec![head_wd]),
        };
        Ok(VerifyObjWellDefinedResult::Failed {
            obj: root,
            reason: FailToVerifyObjWellDefinedResult::FnObj(
                FailToVerifyFnObjObjWellDefined::Domain(
                    fail_stages.into_common_fail(&Obj::FnObj(value.clone())),
                ),
            ),
        })
    }

    pub(super) fn verify_fn_obj_well_definedness_by_def(
        &mut self,
        value: &FnObj,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        // Dedicated entry paths handle all current FnObjHead variants.
        if matches!(
            value.head.as_ref(),
            FnObjHead::AnonymousFnLiteral(_)
                | FnObjHead::Identifier(_)
                | FnObjHead::InstantiatedTemplateObj(_)
                | FnObjHead::FieldAccess(_)
        ) {
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
            FnObjHead::Identifier(_) | FnObjHead::AnonymousFnLiteral(_) => {}
            FnObjHead::FieldAccess(access) => {
                children.push(access.obj.as_ref());
            }
            FnObjHead::InstantiatedTemplateObj(inst) => {
                for arg in &inst.args {
                    children.push(arg);
                }
            }
        }
    }

    // Visible InFunctionSet rows for `obj` and its equality-class neighbors.
    pub(crate) fn collect_in_function_set_candidates(&self, obj: &Obj) -> Vec<(FnSet, FactId)> {
        let mut keys = self.equivalence_class_keys(obj);
        let self_ir = obj.ir();
        if !keys.iter().any(|k| k == &self_ir) {
            keys.push(self_ir);
        }
        let mut out = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            for key in &keys {
                let Some(props) = env.special_properties.get(key) else {
                    continue;
                };
                for prop in props {
                    // A space alias C=fn(...)S identifies a set. It does not
                    // construct a function with that signature. Function
                    // equality to an anonymous function remains callable.
                    if let crate::exec_env::SpecialProperty::Equality(fact) = prop {
                        if !matches!(&fact.left, Obj::FunctionSpace(FunctionSpace::AnonymousFn(_)))
                            && !matches!(&fact.right, Obj::FunctionSpace(FunctionSpace::AnonymousFn(_))) {
                            continue;
                        }
                    }
                    if let Some(signature) = prop.function_signature() {
                        let candidate = (signature, prop.fact_id());
                        if !out.contains(&candidate) {
                            out.push(candidate);
                        }
                    }
                }
            }
        }
        out
    }

    // Ok(stages) = candidate matched; Err(stages) = soft miss for this candidate.
    pub(crate) fn try_verify_fn_obj_against_fn_set(
        &mut self,
        value: &FnObj,
        fn_set: &FnSet,
        verify_state: VerifyState,
    ) -> RuntimeResult<Result<ObjWellDefinedByDefCommonStages, ObjWellDefinedByDefCommonStages>>
    {
        let (proof, _local_env) = self.run_in_local_env_and_take_env(|rt| {
            // A candidate scope is discarded, so returned child/requirement
            // proofs must not cite WD ids created only inside that scope.
            // Existing ancestor ids remain usable; success records the whole
            // application in the caller's environment after candidate selection.
            rt.verify_fn_obj_against_fn_set_in_local(
                value, fn_set, verify_state,
            )
        })?;
        Ok(proof)
    }

    // After a successful domain match, return the fully applied return set.
    // Example: `f $in fn(x N) N` and args `[n-1]` → `N`.
    pub(crate) fn applied_fn_set_return_set(
        &mut self,
        value: &FnObj,
        fn_set: &FnSet,
    ) -> Option<Obj> {
        let mut space = fn_set.clone();
        let last = value.body.len().checked_sub(1)?;
        for (layer_index, layer) in value.body.iter().enumerate() {
            let args: Vec<Obj> = layer.iter().map(|a| a.as_ref().clone()).collect();
            if args.len() != set_bound_parameter_count(&space.set_bound_parameters) {
                return None;
            }
            let subst = set_bound_params_to_arg_map(&space.set_bound_parameters, &args);
            let next_ret = self.inst_obj(space.ret_set.as_ref(), &subst).ok()?;
            if layer_index < last {
                space = self.returned_function_signature(&next_ret)?.0;
            } else {
                return Some(next_ret);
            }
        }
        None
    }

    fn verify_fn_obj_against_fn_set_in_local(
        &mut self,
        value: &FnObj,
        fn_set: &FnSet,
        verify_state: VerifyState,
    ) -> RuntimeResult<Result<ObjWellDefinedByDefCommonStages, ObjWellDefinedByDefCommonStages>>
    {
        let mut proof = ObjWellDefinedByDefCommonStages::leaf();
        let mut space = fn_set.clone();
        let Some(last) = value.body.len().checked_sub(1) else { return Ok(Err(proof)); };
        for (layer_index, layer) in value.body.iter().enumerate() {
            let args: Vec<Obj> = layer.iter().map(|a| a.as_ref().clone()).collect();
            let expected = set_bound_parameter_count(&space.set_bound_parameters);
            if args.len() != expected {
                return Ok(Err(proof));
            }
            for arg in &args {
                let child = self.verify_obj_well_definedness(arg, verify_state.clone())?;
                let failed = child.is_failed();
                proof.child_obj_well_defined.push(child);
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
                        fact_id: self.global_ids.allocate_fact_id(),
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
                // Every function-valued return uses its exact space contract;
                // seq/finite_seq and set aliases preserve the call layers.
                let Some((next_space, carrier)) = self.returned_function_signature(&next_ret)
                else { return Ok(Err(proof)); };
                if carrier != next_ret {
                    let equality = AtomicFact::EqualFact(EqualFact {
                        fact_id: self.global_ids.allocate_fact_id(), left: next_ret,
                        right: carrier, line_file: None,
                    });
                    let requirement = self.verify_fact(&Fact::AtomicFact(equality), verify_state)?;
                    let failed = requirement.is_failed();
                    proof.requirement_fact_verified.push(requirement);
                    if failed { return Ok(Err(proof)); }
                }
                space = next_space;
            }
        }
        Ok(Ok(proof))
    }

    // fn_range(f): children, then f is a literal AnonymousFn or has InFunctionSet.
    // Example: `fn_range(fn(x R) R {1})` and, after `have fn f(...)`, `fn_range(f)`.
    pub(super) fn verify_fn_range_obj_well_definedness(
        &mut self,
        value: &FnRange,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let stages = self.verify_unary_obj_well_definedness_by_def(
            value.function.as_ref(),
            verify_state.clone(),
        )?;
        let root = Obj::FunctionSpace(FunctionSpace::FnRange(value.clone()));
        if !stages.is_fully_known() {
            return Ok(VerifyObjWellDefinedResult::Failed {
                obj: root,
                reason: FailToVerifyObjWellDefinedResult::FunctionSpace(
                    FailToVerifyFunctionSpaceObjWellDefinedResult::FnRange(
                        FailToVerifyFnRangeObjWellDefined::Domain(stages.into_common_fail(
                            &Obj::FunctionSpace(FunctionSpace::FnRange(value.clone())),
                        )),
                    ),
                ),
            });
        }
        let is_anonymous_fn =
            matches!(value.function.as_ref(), Obj::FunctionSpace(FunctionSpace::AnonymousFn(_)));
        if !is_anonymous_fn
            && self
                .collect_in_function_set_candidates(value.function.as_ref())
                .is_empty()
        {
            return Ok(VerifyObjWellDefinedResult::Failed {
                obj: root,
                reason: FailToVerifyObjWellDefinedResult::FunctionSpace(
                    FailToVerifyFunctionSpaceObjWellDefinedResult::FnRange(
                        FailToVerifyFnRangeObjWellDefined::NotInFunctionSet,
                    ),
                ),
            });
        }

        Ok(VerifyObjWellDefinedResult::Success(
            ObjWellDefinedProof::ByDef {
                obj: root,
                proof: ObjWellDefinedProofByDef::FunctionSpace(
                    FunctionSpaceObjWellDefinedProofByDef::FnRange(
                        FnRangeObjWellDefinedProof::from_stages(stages),
                    ),
                ),
            },
        ))
    }

    pub(super) fn obj_has_in_function_set(&self, obj: &Obj) -> bool {
        !self.collect_in_function_set_candidates(obj).is_empty()
    }
}
