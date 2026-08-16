use crate::prelude::*;
use std::rc::Rc;

use super::runtime::WellDefinednessObjectCaptureFrame;

impl Runtime {
    /// Reuse a completed proof visible in the current environment chain.
    pub(crate) fn verify_atomic_fact_from_statement_memo(
        &self,
        fact: &AtomicFact,
    ) -> Option<StmtResult> {
        let key = fact.to_string();
        self.iter_environments_from_top().find_map(|environment| {
            environment
                .statement_verified_atomic_facts
                .get(&key)
                .map(|source| {
                    FactualStmtSuccess::new_with_statement_memo(
                        fact.clone().into(),
                        InferResult::new(),
                        source.clone(),
                    )
                    .into()
                })
        })
    }

    /// Remember truth and its complete proof without committing the fact or running inference.
    pub(crate) fn remember_successful_atomic_fact_for_statement(
        &mut self,
        fact: &AtomicFact,
        result: StmtResult,
    ) -> StmtResult {
        if result.is_unknown() {
            return result;
        }

        let key = fact.to_string();
        let existing_source = {
            self.iter_environments_from_top().find_map(|environment| {
                environment
                    .statement_verified_atomic_facts
                    .get(&key)
                    .cloned()
            })
        };
        if let Some(source) = existing_source {
            let _ = self.record_well_definedness_proof_if_active(source);
            return result;
        }

        let success = result
            .into_factual_success()
            .expect("successful atomic fact verification must return a factual result");
        let infers = success.infers.clone();
        let source = Rc::new(success);
        self.top_level_env()
            .statement_verified_atomic_facts
            .insert(key, source.clone());
        let _ = self.record_well_definedness_proof_if_active(source.clone());

        FactualStmtSuccess::new_with_statement_memo(fact.clone().into(), infers, source).into()
    }

    fn record_well_definedness_proof_if_active(
        &mut self,
        proof: Rc<FactualStmtSuccess>,
    ) -> Option<WellDefinedFactId> {
        if self.well_definedness_capture_depth == 0
            || !self.captures_litex_to_lean_well_definedness()
        {
            return None;
        }
        let statement_capture_depth = self.well_definedness_capture_stack.len();
        if statement_capture_depth == 0 {
            return None;
        }
        let fact_id = if let Some(fact_id) = self.well_defined_fact_id_for_proof(&proof) {
            fact_id
        } else {
            let fact_id = self
                .allocate_well_defined_fact_id()
                .expect("runtime-wide WD fact ID allocation should not exhaust");
            let proposition = proof.stmt.clone();
            let ambient_binder_scope_ids = self
                .well_definedness_binder_scope_capture_stack
                .iter()
                .map(|scope| scope.id)
                .collect();
            let proof = Rc::new(WellDefinedFactProof::new(
                fact_id,
                proposition,
                proof,
                ambient_binder_scope_ids,
            ));
            let environment = self.top_level_env();
            environment.well_defined_fact_proofs.insert(fact_id, proof);
            environment.well_defined_fact_order.push(fact_id);
            fact_id
        };
        if let Some(frame) = self
            .well_definedness_object_capture_stack
            .iter_mut()
            .rev()
            .find(|frame| frame.statement_capture_depth == statement_capture_depth)
        {
            if !frame.fact_ids.contains(&fact_id) {
                frame.fact_ids.push(fact_id);
            }
        }
        Some(fact_id)
    }

    pub(crate) fn begin_well_definedness_object_capture(
        &mut self,
        object: &Obj,
        cache_key: WellDefinedCacheKey,
        cacheable: bool,
    ) {
        if !self.captures_litex_to_lean_well_definedness()
            || self.well_definedness_capture_stack.is_empty()
        {
            return;
        }
        let statement_capture_depth = self.well_definedness_capture_stack.len();
        let ambient_binder_scope_ids = self
            .well_definedness_binder_scope_capture_stack
            .iter()
            .map(|scope| scope.id)
            .collect();
        self.well_definedness_object_capture_stack
            .push(WellDefinednessObjectCaptureFrame::new(
                object.clone(),
                cache_key,
                cacheable,
                statement_capture_depth,
                ambient_binder_scope_ids,
            ));
    }

    pub(crate) fn end_well_definedness_object_capture(
        &mut self,
        succeeded: bool,
        intrinsic_result_set: Option<Obj>,
    ) -> Result<Option<WellDefinedObjId>, RuntimeError> {
        if !self.captures_litex_to_lean_well_definedness() {
            return Ok(None);
        }
        let statement_capture_depth = self.well_definedness_capture_stack.len();
        let Some(frame) = self.well_definedness_object_capture_stack.pop() else {
            return Ok(None);
        };
        if frame.statement_capture_depth != statement_capture_depth || !succeeded {
            return Ok(None);
        }
        let proof_id = self.allocate_well_defined_obj_id()?;
        let proof = Rc::new(WellDefinedObjProof::new(
            proof_id,
            frame.object,
            frame.cache_key.clone(),
            frame.child_uses,
            frame.fact_ids,
            frame.target_requirements,
            intrinsic_result_set,
            frame.ambient_binder_scope_ids,
            frame.owned_binder_scope,
        ));
        let environment = self.top_level_env();
        environment.well_defined_obj_proofs.insert(proof_id, proof);
        if frame.cacheable {
            environment
                .cache_well_defined_obj
                .insert(frame.cache_key, CachedWellDefinedObj::with_obj(proof_id));
        }
        Ok(Some(proof_id))
    }

    pub(crate) fn begin_well_definedness_binder_scope(
        &mut self,
        owner_object: &Obj,
    ) -> Result<Option<WellDefinedBinderScopeId>, RuntimeError> {
        if !self.captures_litex_to_lean_well_definedness()
            || self.well_definedness_capture_stack.is_empty()
        {
            return Ok(None);
        }
        let statement_capture_depth = self.well_definedness_capture_stack.len();
        let owner_key = obj_equality_key(owner_object);
        let owner = self
            .well_definedness_object_capture_stack
            .iter()
            .rev()
            .find(|frame| {
                frame.statement_capture_depth == statement_capture_depth
                    && obj_equality_key(&frame.object) == owner_key
            })
            .ok_or_else(|| {
                missing_well_definedness_proof_error(format!(
                    "binder scope for `{owner_object}` has no active owner object frame"
                ))
            })?;
        if owner.owned_binder_scope.is_some() {
            return Err(missing_well_definedness_proof_error(format!(
                "binder-owning object `{owner_object}` opened more than one WD scope"
            )));
        }
        let id = self.allocate_well_defined_binder_scope_id()?;
        let ambient_scope_ids = self
            .well_definedness_binder_scope_capture_stack
            .iter()
            .map(|scope| scope.id)
            .collect();
        self.well_definedness_binder_scope_capture_stack.push(
            super::runtime::WellDefinednessBinderScopeCaptureFrame {
                id,
                owner_object: owner_object.clone(),
                ambient_scope_ids,
                premises: Vec::new(),
                assumption_infers: InferResult::new(),
                statement_capture_depth,
            },
        );
        Ok(Some(id))
    }

    pub(crate) fn record_well_definedness_binder_parameter_group(
        &mut self,
        scope_id: Option<WellDefinedBinderScopeId>,
        parameter_group_index: usize,
        group: &ParamGroupWithSet,
        infer_result: &InferResult,
    ) -> Result<(), RuntimeError> {
        let Some(scope_id) = scope_id else {
            return Ok(());
        };
        let scope = self
            .well_definedness_binder_scope_capture_stack
            .last_mut()
            .filter(|scope| scope.id == scope_id)
            .ok_or_else(|| {
                missing_well_definedness_proof_error(format!(
                    "WD binder scope {} is not active while recording parameter group {parameter_group_index}",
                    scope_id.value()
                ))
            })?;
        let parameter_reason = InferReason::ParameterDefinition.store_reason();
        let expected_facts = group.facts_for_binding_scope(ParamObjType::FnSet);
        if expected_facts.len() != group.params.len() {
            return Err(missing_well_definedness_proof_error(
                "binder parameter group produced a mismatched fact list".to_string(),
            ));
        }
        for (parameter_index, (binding, expected)) in
            group.params.iter().zip(expected_facts.iter()).enumerate()
        {
            let matches = infer_result
                .store_fact_outputs
                .iter()
                .filter(|output| {
                    output.itself_and_why_itself_is_stored.1 == parameter_reason
                        && output.itself_and_why_itself_is_stored.0.to_string()
                            == expected.to_string()
                })
                .collect::<Vec<_>>();
            if matches.len() != 1 {
                return Err(missing_well_definedness_proof_error(format!(
                    "WD binder scope {} retained {} parameter outputs for `{expected}`; expected exactly one",
                    scope_id.value(),
                    matches.len()
                )));
            }
            let fact_id = matches[0].fact_id.ok_or_else(|| {
                missing_well_definedness_proof_error(format!(
                    "WD binder parameter premise `{expected}` has no FactId"
                ))
            })?;
            scope.premises.push(WellDefinedBinderPremiseProof::new(
                WellDefinedBinderPremiseRole::ParameterMembership {
                    parameter_group_index,
                    parameter_index,
                },
                Some(binding.id()),
                fact_id,
                expected.clone(),
            ));
        }
        scope
            .assumption_infers
            .new_infer_result_inside(infer_result.clone());
        Ok(())
    }

    pub(crate) fn record_well_definedness_binder_domain(
        &mut self,
        scope_id: Option<WellDefinedBinderScopeId>,
        domain_index: usize,
        expected: Fact,
        infer_result: &InferResult,
    ) -> Result<(), RuntimeError> {
        let Some(scope_id) = scope_id else {
            return Ok(());
        };
        let scope = self
            .well_definedness_binder_scope_capture_stack
            .last_mut()
            .filter(|scope| scope.id == scope_id)
            .ok_or_else(|| {
                missing_well_definedness_proof_error(format!(
                    "WD binder scope {} is not active while recording domain {domain_index}",
                    scope_id.value()
                ))
            })?;
        let matches = infer_result
            .store_fact_outputs
            .iter()
            .filter(|output| {
                output.itself_and_why_itself_is_stored.0.to_string() == expected.to_string()
            })
            .collect::<Vec<_>>();
        if matches.len() != 1 {
            return Err(missing_well_definedness_proof_error(format!(
                "WD binder scope {} retained {} primary domain outputs for `{expected}`; expected exactly one",
                scope_id.value(),
                matches.len()
            )));
        }
        let fact_id = matches[0].fact_id.ok_or_else(|| {
            missing_well_definedness_proof_error(format!(
                "WD binder domain premise `{expected}` has no FactId"
            ))
        })?;
        scope.premises.push(WellDefinedBinderPremiseProof::new(
            WellDefinedBinderPremiseRole::Domain { domain_index },
            None,
            fact_id,
            expected,
        ));
        scope
            .assumption_infers
            .new_infer_result_inside(infer_result.clone());
        Ok(())
    }

    pub(crate) fn record_well_definedness_set_builder_parameter(
        &mut self,
        scope_id: Option<WellDefinedBinderScopeId>,
        binding: &SymbolBinding,
        expected: Fact,
        infer_result: &InferResult,
    ) -> Result<(), RuntimeError> {
        self.record_well_definedness_binder_premise(
            scope_id,
            WellDefinedBinderPremiseRole::ParameterMembership {
                parameter_group_index: 0,
                parameter_index: 0,
            },
            Some(binding.id()),
            expected,
            infer_result,
            "set-builder parameter",
        )
    }

    pub(crate) fn record_well_definedness_set_builder_condition(
        &mut self,
        scope_id: Option<WellDefinedBinderScopeId>,
        condition_index: usize,
        expected: Fact,
        infer_result: &InferResult,
    ) -> Result<(), RuntimeError> {
        self.record_well_definedness_binder_premise(
            scope_id,
            WellDefinedBinderPremiseRole::LocalCondition { condition_index },
            None,
            expected,
            infer_result,
            "set-builder condition",
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn record_well_definedness_binder_premise(
        &mut self,
        scope_id: Option<WellDefinedBinderScopeId>,
        role: WellDefinedBinderPremiseRole,
        symbol_id: Option<SymbolId>,
        expected: Fact,
        infer_result: &InferResult,
        description: &str,
    ) -> Result<(), RuntimeError> {
        let Some(scope_id) = scope_id else {
            return Ok(());
        };
        let scope = self
            .well_definedness_binder_scope_capture_stack
            .last_mut()
            .filter(|scope| scope.id == scope_id)
            .ok_or_else(|| {
                missing_well_definedness_proof_error(format!(
                    "WD binder scope {} is not active while recording {description}",
                    scope_id.value()
                ))
            })?;
        let matches = infer_result
            .store_fact_outputs
            .iter()
            .filter(|output| {
                output.itself_and_why_itself_is_stored.0.to_string() == expected.to_string()
            })
            .collect::<Vec<_>>();
        if matches.len() != 1 {
            return Err(missing_well_definedness_proof_error(format!(
                "WD binder scope {} retained {} primary {description} outputs for `{expected}`; expected exactly one",
                scope_id.value(),
                matches.len()
            )));
        }
        let fact_id = matches[0].fact_id.ok_or_else(|| {
            missing_well_definedness_proof_error(format!(
                "WD binder {description} premise `{expected}` has no FactId"
            ))
        })?;
        scope.premises.push(WellDefinedBinderPremiseProof::new(
            role, symbol_id, fact_id, expected,
        ));
        scope
            .assumption_infers
            .new_infer_result_inside(infer_result.clone());
        Ok(())
    }

    pub(crate) fn end_well_definedness_binder_scope(
        &mut self,
        scope_id: Option<WellDefinedBinderScopeId>,
        succeeded: bool,
    ) -> Result<(), RuntimeError> {
        let Some(scope_id) = scope_id else {
            return Ok(());
        };
        let scope = self
            .well_definedness_binder_scope_capture_stack
            .pop()
            .ok_or_else(|| {
                missing_well_definedness_proof_error(format!(
                    "WD binder scope {} disappeared before completion",
                    scope_id.value()
                ))
            })?;
        if scope.id != scope_id {
            return Err(missing_well_definedness_proof_error(format!(
                "WD binder scopes closed out of order: expected {}, got {}",
                scope_id.value(),
                scope.id.value()
            )));
        }
        if !succeeded {
            return Ok(());
        }
        let owner_key = obj_equality_key(&scope.owner_object);
        let owner = self
            .well_definedness_object_capture_stack
            .iter_mut()
            .rev()
            .find(|frame| {
                frame.statement_capture_depth == scope.statement_capture_depth
                    && obj_equality_key(&frame.object) == owner_key
            })
            .ok_or_else(|| {
                missing_well_definedness_proof_error(format!(
                    "completed WD binder scope {} has no active owner object",
                    scope_id.value()
                ))
            })?;
        if owner.owned_binder_scope.is_some() {
            return Err(missing_well_definedness_proof_error(format!(
                "WellDefinedObj owner of scope {} already owns another binder scope",
                scope_id.value()
            )));
        }
        owner.owned_binder_scope = Some(WellDefinedBinderScopeProof {
            id: scope.id,
            owner_object: scope.owner_object,
            ambient_scope_ids: scope.ambient_scope_ids,
            premises: scope.premises,
            assumption_infers: scope.assumption_infers,
        });
        Ok(())
    }

    /// Freeze an already-verified proper prefix of a layered application as
    /// its own cache/DAG node, then make that prefix the direct callable child
    /// of the still-active outer application.  This mirrors Litex evaluation:
    /// `g(1)(2)` first establishes the fixed object `g(1)`, and the second
    /// layer consumes exactly that object rather than replaying layer one.
    pub(crate) fn freeze_active_fn_application_prefix(
        &mut self,
        prefix: &Obj,
        result_set: Obj,
        through_layer_index: usize,
    ) -> Result<Option<WellDefinedObjId>, RuntimeError> {
        if !self.captures_litex_to_lean_well_definedness()
            || self.well_definedness_object_capture_stack.is_empty()
        {
            return Ok(None);
        }

        let reusable_cache_key = self.well_defined_cache_key_for_obj(prefix);
        let cache_key = reusable_cache_key
            .clone()
            .unwrap_or_else(|| WellDefinedCacheKey::without_function_contract(prefix.to_string()));
        let cached_id = reusable_cache_key
            .as_ref()
            .and_then(|key| self.well_defined_cache_entry(key))
            .and_then(|entry| entry.obj_id);

        let statement_capture_depth = self.well_definedness_capture_stack.len();
        let (child_uses, fact_ids, target_requirements) = {
            let frame = self
                .well_definedness_object_capture_stack
                .last_mut()
                .expect("checked nonempty WD object capture stack");
            if frame.statement_capture_depth != statement_capture_depth {
                return Err(missing_well_definedness_proof_error(
                    "layered application prefix escaped its statement capture".to_string(),
                ));
            }
            (
                std::mem::take(&mut frame.child_uses),
                std::mem::take(&mut frame.fact_ids),
                std::mem::take(&mut frame.target_requirements),
            )
        };

        let obj_id = if let Some(obj_id) = cached_id {
            obj_id
        } else {
            let obj_id = self.allocate_well_defined_obj_id()?;
            let proof = Rc::new(WellDefinedObjProof::new(
                obj_id,
                prefix.clone(),
                cache_key.clone(),
                child_uses,
                fact_ids,
                target_requirements,
                Some(result_set),
                self.well_definedness_binder_scope_capture_stack
                    .iter()
                    .map(|scope| scope.id)
                    .collect(),
                None,
            ));
            let environment = self.top_level_env();
            environment.well_defined_obj_proofs.insert(obj_id, proof);
            if reusable_cache_key.is_some() {
                environment
                    .cache_well_defined_obj
                    .insert(cache_key, CachedWellDefinedObj::with_obj(obj_id));
            }
            obj_id
        };

        self.record_well_defined_obj_proof_use(
            prefix,
            obj_id,
            Some(WellDefinedObjChildRole::FunctionPrefix {
                through_layer_index,
            }),
        )?;
        Ok(Some(obj_id))
    }

    pub(crate) fn record_well_defined_obj_proof_use(
        &mut self,
        source_object: &Obj,
        proof_id: WellDefinedObjId,
        child_role: Option<WellDefinedObjChildRole>,
    ) -> Result<(), RuntimeError> {
        let statement_capture_depth = self.well_definedness_capture_stack.len();
        if statement_capture_depth == 0 {
            return Ok(());
        }
        let phase = self
            .well_definedness_target_requirement_phase_stack
            .last()
            .copied()
            .ok_or_else(|| {
                missing_well_definedness_proof_error(
                    "WD target-requirement phase stack is missing its statement frame".to_string(),
                )
            })?;
        let record_source_self = !matches!(
            child_role,
            Some(WellDefinedObjChildRole::FunctionPrefix { .. })
        );
        self.record_well_defined_source_object_use_closure(
            source_object,
            proof_id,
            phase,
            record_source_self,
        )?;
        let target_requirement_use = match source_object {
            Obj::FnObj(application) => application.source_occurrence_id.map(|occurrence_id| {
                self.well_defined_obj_proof(proof_id)
                    .map(|proof| (occurrence_id, proof.target_requirements.clone()))
                    .ok_or_else(|| {
                        missing_well_definedness_proof_error(format!(
                            "well-defined object proof {} is outside the active environment chain",
                            proof_id.value()
                        ))
                    })
            }),
            _ => None,
        }
        .transpose()?;
        if let Some(parent) = self
            .well_definedness_object_capture_stack
            .iter_mut()
            .rev()
            .find(|frame| frame.statement_capture_depth == statement_capture_depth)
        {
            let child_role = child_role.unwrap_or_else(|| {
                let dependency_index = parent
                    .child_uses
                    .iter()
                    .filter(|child| {
                        matches!(
                            child.role,
                            WellDefinedObjChildRole::VerificationDependency { .. }
                        )
                    })
                    .count();
                WellDefinedObjChildRole::VerificationDependency { dependency_index }
            });
            parent.child_uses.push(WellDefinedObjChildUse::new(
                child_role,
                proof_id,
                source_object.clone(),
            ));
        } else {
            let certificate = self
                .well_definedness_capture_stack
                .last_mut()
                .expect("checked nonempty WD capture stack");
            if !certificate.root_obj_ids.contains(&proof_id) {
                certificate.root_obj_ids.push(proof_id);
            }
            let root_use = WellDefinednessRootObjectProofUse::new(proof_id, phase);
            if !certificate.root_proof_uses.contains(&root_use) {
                certificate.root_proof_uses.push(root_use);
            }
        }

        if let Some((source_occurrence_id, requirements)) = target_requirement_use {
            let certificate = self
                .well_definedness_capture_stack
                .last_mut()
                .expect("checked nonempty WD capture stack");
            for requirement in requirements {
                let target_use = WellDefinedTargetRequirementUse::new(
                    source_occurrence_id,
                    proof_id,
                    phase,
                    requirement.role,
                    requirement.fact_id,
                    requirement.expected_proposition,
                );
                if let Some(index) =
                    certificate
                        .target_requirement_uses
                        .iter()
                        .position(|existing| {
                            existing.source_occurrence_id == source_occurrence_id
                                && existing.role == requirement.role
                                && existing.phase == phase
                        })
                {
                    // Keep the final verifier use in one phase, matching the
                    // canonical source-object use selected during freezing.
                    certificate.target_requirement_uses[index] = target_use;
                } else {
                    certificate.target_requirement_uses.push(target_use);
                }
            }
        }
        Ok(())
    }

    /// Record exact source-use edges for a checked object and, on a cache hit,
    /// project its already-verified constructor recipe onto the new source
    /// occurrence tree. This is positional: it follows typed child roles and
    /// never searches for a structurally equal object.
    fn record_well_defined_source_object_use_closure(
        &mut self,
        source_object: &Obj,
        proof_id: WellDefinedObjId,
        phase: WellDefinednessTargetRequirementPhase,
        record_self: bool,
    ) -> Result<(), RuntimeError> {
        if record_self {
            if let Some(source_occurrence_id) = source_object.source_occurrence_id() {
                let certificate = self
                    .well_definedness_capture_stack
                    .last_mut()
                    .expect("checked nonempty WD capture stack");
                if let Some(existing) = certificate.source_object_uses.iter().find(|existing| {
                    existing.source_occurrence_id == source_occurrence_id
                        && existing.phase == phase
                        && existing.well_defined_obj_id == proof_id
                }) {
                    if obj_equality_key(&existing.source_object) != obj_equality_key(source_object)
                    {
                        return Err(missing_well_definedness_proof_error(format!(
                            "source occurrence {} changed object in phase {:?}",
                            source_occurrence_id.value(),
                            phase,
                        )));
                    }
                } else {
                    certificate
                        .source_object_uses
                        .push(WellDefinednessSourceObjectUse::new(
                            source_occurrence_id,
                            source_object.clone(),
                            proof_id,
                            phase,
                        ));
                }
            }
        }

        let proof = self.well_defined_obj_proof(proof_id).ok_or_else(|| {
            missing_well_definedness_proof_error(format!(
                "WellDefinedObjId {} is outside the active environment chain while projecting a source occurrence",
                proof_id.value()
            ))
        })?;
        let child_uses = proof.child_uses.clone();
        match source_object {
            Obj::FnObj(application) => {
                for child in child_uses {
                    match child.role {
                        WellDefinedObjChildRole::FunctionPrefix {
                            through_layer_index,
                        } => {
                            let prefix = application.prefix_obj(through_layer_index + 1);
                            self.record_well_defined_source_object_use_closure(
                                &prefix,
                                child.obj_id,
                                phase,
                                false,
                            )?;
                        }
                        WellDefinedObjChildRole::FunctionHead => {
                            let head: Obj = application.head.as_ref().clone().into();
                            self.record_well_defined_source_object_use_closure(
                                &head,
                                child.obj_id,
                                phase,
                                true,
                            )?;
                        }
                        WellDefinedObjChildRole::FunctionArgument {
                            layer_index,
                            argument_index,
                        } => {
                            let argument = application
                                .body
                                .get(layer_index)
                                .and_then(|layer| layer.get(argument_index))
                                .ok_or_else(|| {
                                    missing_well_definedness_proof_error(format!(
                                        "WellDefinedObjId {} has an out-of-range function argument role ({layer_index}, {argument_index})",
                                        proof_id.value()
                                    ))
                                })?;
                            self.record_well_defined_source_object_use_closure(
                                argument.as_ref(),
                                child.obj_id,
                                phase,
                                true,
                            )?;
                        }
                        WellDefinedObjChildRole::VerificationDependency { .. } => {
                            // Audit dependencies are retained in the WD DAG,
                            // but are not source application value slots and
                            // therefore never manufacture occurrence edges.
                        }
                        other => {
                            return Err(missing_well_definedness_proof_error(format!(
                                "WellDefinedObjId {} retained unexpected application child role {other:?}",
                                proof_id.value()
                            )));
                        }
                    }
                }
            }
            Obj::Add(value) => self.record_binary_source_object_uses(
                value.left.as_ref(),
                value.right.as_ref(),
                proof_id,
                phase,
                &child_uses,
            )?,
            Obj::Sub(value) => self.record_binary_source_object_uses(
                value.left.as_ref(),
                value.right.as_ref(),
                proof_id,
                phase,
                &child_uses,
            )?,
            Obj::Mul(value) => self.record_binary_source_object_uses(
                value.left.as_ref(),
                value.right.as_ref(),
                proof_id,
                phase,
                &child_uses,
            )?,
            Obj::Div(value) => self.record_binary_source_object_uses(
                value.left.as_ref(),
                value.right.as_ref(),
                proof_id,
                phase,
                &child_uses,
            )?,
            Obj::ListSet(value) => {
                for child in child_uses {
                    let argument_index = match child.role {
                        WellDefinedObjChildRole::ConstructorArgument { argument_index } => {
                            argument_index
                        }
                        WellDefinedObjChildRole::VerificationDependency { .. } => continue,
                        other => {
                            return Err(missing_well_definedness_proof_error(format!(
                                "WellDefinedObjId {} retained unexpected list-set child role {other:?}",
                                proof_id.value()
                            )));
                        }
                    };
                    let argument = value.list.get(argument_index).ok_or_else(|| {
                        missing_well_definedness_proof_error(format!(
                            "WellDefinedObjId {} has an out-of-range list-set argument role {argument_index}",
                            proof_id.value()
                        ))
                    })?;
                    self.record_well_defined_source_object_use_closure(
                        argument.as_ref(),
                        child.obj_id,
                        phase,
                        true,
                    )?;
                }
            }
            Obj::FnSet(value) => {
                for child in child_uses {
                    let source_child = match child.role {
                        WellDefinedObjChildRole::BinderParameterCarrier {
                            parameter_group_index,
                        } => value
                            .body
                            .params_def_with_set
                            .get(parameter_group_index)
                            .map(ParamGroupWithSet::set_obj),
                        WellDefinedObjChildRole::BinderReturnCarrier => {
                            Some(value.body.ret_set.as_ref())
                        }
                        WellDefinedObjChildRole::VerificationDependency { .. } => continue,
                        other => {
                            return Err(missing_well_definedness_proof_error(format!(
                                "WellDefinedObjId {} retained unexpected function-set child role {other:?}",
                                proof_id.value()
                            )));
                        }
                    }
                    .ok_or_else(|| {
                        missing_well_definedness_proof_error(format!(
                            "WellDefinedObjId {} retained an out-of-range function-set binder carrier",
                            proof_id.value()
                        ))
                    })?;
                    self.record_well_defined_source_object_use_closure(
                        source_child,
                        child.obj_id,
                        phase,
                        true,
                    )?;
                }
            }
            Obj::AnonymousFn(value) => {
                for child in child_uses {
                    let source_child = match child.role {
                        WellDefinedObjChildRole::BinderParameterCarrier {
                            parameter_group_index,
                        } => value
                            .body
                            .params_def_with_set
                            .get(parameter_group_index)
                            .map(ParamGroupWithSet::set_obj),
                        WellDefinedObjChildRole::BinderReturnCarrier => {
                            Some(value.body.ret_set.as_ref())
                        }
                        WellDefinedObjChildRole::BinderBody => Some(value.equal_to.as_ref()),
                        WellDefinedObjChildRole::VerificationDependency { .. } => continue,
                        other => {
                            return Err(missing_well_definedness_proof_error(format!(
                                "WellDefinedObjId {} retained unexpected anonymous-function child role {other:?}",
                                proof_id.value()
                            )));
                        }
                    }
                    .ok_or_else(|| {
                        missing_well_definedness_proof_error(format!(
                            "WellDefinedObjId {} retained an out-of-range anonymous-function binder carrier",
                            proof_id.value()
                        ))
                    })?;
                    self.record_well_defined_source_object_use_closure(
                        source_child,
                        child.obj_id,
                        phase,
                        true,
                    )?;
                }
            }
            Obj::SetBuilder(value) => {
                for child in child_uses {
                    let source_child = match child.role {
                        WellDefinedObjChildRole::BinderParameterCarrier {
                            parameter_group_index: 0,
                        } => value.param_set.as_ref(),
                        WellDefinedObjChildRole::VerificationDependency { .. } => continue,
                        other => {
                            return Err(missing_well_definedness_proof_error(format!(
                                "WellDefinedObjId {} retained unexpected set-builder child role {other:?}",
                                proof_id.value()
                            )));
                        }
                    };
                    self.record_well_defined_source_object_use_closure(
                        source_child,
                        child.obj_id,
                        phase,
                        true,
                    )?;
                }
            }
            _ => {
                for child in child_uses {
                    let argument_index = match child.role {
                        WellDefinedObjChildRole::ConstructorArgument { argument_index } => {
                            argument_index
                        }
                        WellDefinedObjChildRole::VerificationDependency { .. } => continue,
                        other => {
                            return Err(missing_well_definedness_proof_error(format!(
                                "WellDefinedObjId {} retained unexpected ordinary-constructor child role {other:?}",
                                proof_id.value()
                            )));
                        }
                    };
                    let argument = source_object
                        .well_definedness_constructor_argument(argument_index)
                        .ok_or_else(|| {
                            missing_well_definedness_proof_error(format!(
                                "WellDefinedObjId {} has no constructor argument at index {argument_index}",
                                proof_id.value()
                            ))
                        })?;
                    self.record_well_defined_source_object_use_closure(
                        &argument,
                        child.obj_id,
                        phase,
                        true,
                    )?;
                }
            }
        }
        Ok(())
    }

    fn record_binary_source_object_uses(
        &mut self,
        left: &Obj,
        right: &Obj,
        proof_id: WellDefinedObjId,
        phase: WellDefinednessTargetRequirementPhase,
        child_uses: &[WellDefinedObjChildUse],
    ) -> Result<(), RuntimeError> {
        let arguments = [left, right];
        for child in child_uses {
            let argument_index = match child.role {
                WellDefinedObjChildRole::BuiltinArgument { argument_index } => argument_index,
                WellDefinedObjChildRole::VerificationDependency { .. } => {
                    // Verifier-only audit dependency, not an operand slot.
                    continue;
                }
                other => {
                    return Err(missing_well_definedness_proof_error(format!(
                        "WellDefinedObjId {} retained unexpected builtin child role {other:?}",
                        proof_id.value()
                    )));
                }
            };
            let argument = arguments.get(argument_index).ok_or_else(|| {
                missing_well_definedness_proof_error(format!(
                    "WellDefinedObjId {} has an out-of-range builtin argument role {argument_index}",
                    proof_id.value()
                ))
            })?;
            self.record_well_defined_source_object_use_closure(
                argument,
                child.obj_id,
                phase,
                true,
            )?;
        }
        Ok(())
    }

    pub(crate) fn record_well_definedness_target_requirement(
        &mut self,
        source_object: &Obj,
        role: WellDefinednessRequirementRole,
        result: StmtResult,
    ) -> Result<(), RuntimeError> {
        if !self.captures_litex_to_lean_well_definedness() {
            return Ok(());
        }
        let success = result.into_factual_success().ok_or_else(|| {
            missing_well_definedness_proof_error(format!(
                "target WD requirement {role:?} for `{source_object}` has no factual proof"
            ))
        })?;
        let expected_proposition = success.stmt.clone();
        let proof = if let VerifiedByResult::StatementMemo(proof) = &success.verified_by {
            proof.clone()
        } else {
            // A successful requirement need not have passed through the memo
            // cache. Preserve that exact verifier result rather than losing
            // the target proof reference or asking the Lean backend to search.
            Rc::new(success)
        };
        let fact_id = self
            .record_well_definedness_proof_if_active(proof)
            .ok_or_else(|| {
                missing_well_definedness_proof_error(format!(
                    "target WD requirement {role:?} for `{source_object}` was not captured"
                ))
            })?;
        let statement_capture_depth = self.well_definedness_capture_stack.len();
        let source_key = obj_equality_key(source_object);
        let frame = self
            .well_definedness_object_capture_stack
            .iter_mut()
            .rev()
            .find(|frame| {
                frame.statement_capture_depth == statement_capture_depth
                    && obj_equality_key(&frame.object) == source_key
            })
            .ok_or_else(|| {
                missing_well_definedness_proof_error(format!(
                    "target WD requirement {role:?} for `{source_object}` has no active object frame"
                ))
            })?;
        if frame
            .target_requirements
            .iter()
            .any(|requirement| requirement.role == role && requirement.fact_id == fact_id)
        {
            return Ok(());
        }
        frame
            .target_requirements
            .push(WellDefinedTargetRequirementProof::new(
                source_object.clone(),
                role,
                fact_id,
                expected_proposition,
            ));
        Ok(())
    }

    pub(crate) fn record_well_definedness_parameter_facts(
        &mut self,
        params: &ParamDefWithType,
        infer_result: &InferResult,
    ) -> Result<(), RuntimeError> {
        if !self.captures_litex_to_lean_well_definedness()
            || self.well_definedness_capture_stack.is_empty()
        {
            return Ok(());
        }
        let parameter_reason = InferReason::ParameterDefinition.store_reason();
        let outputs = infer_result
            .store_fact_outputs
            .iter()
            .filter(|output| output.itself_and_why_itself_is_stored.1 == parameter_reason)
            .collect::<Vec<_>>();
        let bindings = params.collect_param_bindings();
        if outputs.len() != bindings.len() {
            return Err(missing_well_definedness_proof_error(format!(
                "nested forall retained {} parameter facts for {} bindings",
                outputs.len(),
                bindings.len()
            )));
        }

        let mut additions = Vec::with_capacity(bindings.len());
        for (binding, output) in bindings.iter().zip(outputs) {
            let proposition = output.itself_and_why_itself_is_stored.0.clone();
            let fact_id = self.known_fact_id_for_fact(&proposition)?.ok_or_else(|| {
                missing_well_definedness_proof_error(format!(
                    "nested forall parameter fact `{proposition}` has no FactId"
                ))
            })?;
            additions.push(WellDefinednessParameterFactEvidence::new(
                binding.id(),
                fact_id,
                proposition,
            ));
        }
        let certificate = self
            .well_definedness_capture_stack
            .last_mut()
            .expect("checked nonempty WD capture stack");
        for evidence in additions {
            if !certificate.parameter_facts.iter().any(|existing| {
                existing.symbol_id == evidence.symbol_id && existing.fact_id == evidence.fact_id
            }) {
                certificate.parameter_facts.push(evidence);
            }
        }
        Ok(())
    }

    pub(crate) fn freeze_well_definedness_certificate(
        &self,
        mut certificate: WellDefinednessCertificate,
    ) -> Result<WellDefinednessCertificate, RuntimeError> {
        let mut object_proofs = std::collections::HashMap::new();
        let mut pending = certificate.root_obj_ids.clone();
        while let Some(proof_id) = pending.pop() {
            if object_proofs.contains_key(&proof_id) {
                continue;
            }
            let proof = self.well_defined_obj_proof(proof_id).ok_or_else(|| {
                missing_well_definedness_proof_error(format!(
                    "well-defined object proof {} is outside the active environment chain",
                    proof_id.value()
                ))
            })?;
            pending.extend(proof.child_uses.iter().map(|child| child.obj_id));
            object_proofs.insert(proof_id, proof);
        }

        let live_source_object_uses = std::mem::take(&mut certificate.source_object_uses);
        let mut selected_source_object_uses: Vec<WellDefinednessSourceObjectUse> = Vec::new();
        let mut selected_source_object_indices =
            std::collections::HashMap::<SourceObjectOccurrenceId, usize>::new();
        for source_use in live_source_object_uses {
            if !object_proofs.contains_key(&source_use.well_defined_obj_id) {
                return Err(missing_well_definedness_proof_error(format!(
                    "source occurrence {} cites WellDefinedObjId {} outside the frozen root closure",
                    source_use.source_occurrence_id.value(),
                    source_use.well_defined_obj_id.value(),
                )));
            }
            if let Some(index) = selected_source_object_indices
                .get(&source_use.source_occurrence_id)
                .copied()
            {
                let selected = selected_source_object_uses[index].clone();
                let source_priority = target_requirement_phase_priority(source_use.phase);
                let selected_priority = target_requirement_phase_priority(selected.phase);
                if source_priority == selected_priority
                    && obj_equality_key(&selected.source_object)
                        != obj_equality_key(&source_use.source_object)
                {
                    return Err(missing_well_definedness_proof_error(format!(
                        "source occurrence {} changed object within canonical phase {:?}",
                        source_use.source_occurrence_id.value(),
                        source_use.phase,
                    )));
                }
                if source_priority >= selected_priority {
                    // Later verifier use wins within one phase. The frozen
                    // certificate retains this direct choice, so the emitter
                    // never repeats the ordering decision.
                    selected_source_object_uses[index] = source_use;
                }
            } else {
                selected_source_object_indices.insert(
                    source_use.source_occurrence_id,
                    selected_source_object_uses.len(),
                );
                selected_source_object_uses.push(source_use);
            }
        }
        selected_source_object_uses
            .sort_by_key(|source_use| source_use.source_occurrence_id.value());
        certificate.source_object_uses = selected_source_object_uses;

        let mut ordered_object_ids = object_proofs.keys().copied().collect::<Vec<_>>();
        ordered_object_ids.sort_by_key(|proof_id| proof_id.value());
        let mut referenced_fact_ids = std::collections::HashSet::new();
        for proof in object_proofs.values() {
            referenced_fact_ids.extend(proof.fact_ids.iter().copied());
            referenced_fact_ids.extend(
                proof
                    .target_requirements
                    .iter()
                    .map(|requirement| requirement.fact_id),
            );
        }
        referenced_fact_ids.extend(
            certificate
                .target_requirement_uses
                .iter()
                .map(|requirement| requirement.fact_id),
        );
        let mut ordered_fact_ids = referenced_fact_ids.into_iter().collect::<Vec<_>>();
        ordered_fact_ids.sort_by_key(|fact_id| fact_id.value());
        certificate.facts = ordered_fact_ids
            .iter()
            .map(|fact_id| {
                let proof = self.well_defined_fact_proof(*fact_id).ok_or_else(|| {
                    missing_well_definedness_proof_error(format!(
                        "well-defined fact {} is outside the active environment chain",
                        fact_id.value()
                    ))
                })?;
                Ok(WellDefinednessFactEvidence {
                    well_defined_fact_id: *fact_id,
                    proof: proof.proof.clone(),
                    ambient_binder_scope_ids: proof.ambient_binder_scope_ids.clone(),
                })
            })
            .collect::<Result<Vec<_>, RuntimeError>>()?;

        certificate.objects = ordered_object_ids
            .iter()
            .map(|proof_id| {
                let proof = &object_proofs[proof_id];
                WellDefinednessObjectEvidence::new(
                    *proof_id,
                    proof.object.clone(),
                    proof.cache_key.function_contracts.clone(),
                    proof.intrinsic_result_set.clone(),
                    proof.child_uses.clone(),
                    proof.fact_ids.clone(),
                    proof.target_requirements.clone(),
                    proof.ambient_binder_scope_ids.clone(),
                    proof.owned_binder_scope.as_ref().map(|scope| scope.id),
                )
            })
            .collect();

        let mut binder_scopes = object_proofs
            .values()
            .filter_map(|proof| proof.owned_binder_scope.clone())
            .collect::<Vec<_>>();
        binder_scopes.sort_by_key(|scope| scope.id.value());
        let mut seen_binder_scope_ids = std::collections::HashSet::new();
        for scope in binder_scopes.iter() {
            if !seen_binder_scope_ids.insert(scope.id) {
                return Err(missing_well_definedness_proof_error(format!(
                    "WD binder scope {} is owned by more than one frozen object",
                    scope.id.value()
                )));
            }
        }
        certificate.binder_scopes = binder_scopes
            .into_iter()
            .map(|scope| WellDefinednessBinderScopeEvidence { scope })
            .collect();

        let target_requirement_uses = std::mem::take(&mut certificate.target_requirement_uses);
        let mut selected_target_requirement_uses: Vec<WellDefinedTargetRequirementUse> = Vec::new();
        let mut selected_indices: std::collections::HashMap<
            (SourceObjectOccurrenceId, WellDefinednessRequirementRole),
            usize,
        > = std::collections::HashMap::new();
        for requirement in target_requirement_uses {
            let key = (requirement.source_occurrence_id, requirement.role);
            if let Some(index) = selected_indices.get(&key).copied() {
                if target_requirement_phase_priority(requirement.phase)
                    >= target_requirement_phase_priority(
                        selected_target_requirement_uses[index].phase,
                    )
                {
                    selected_target_requirement_uses[index] = requirement;
                }
            } else {
                selected_indices.insert(key, selected_target_requirement_uses.len());
                selected_target_requirement_uses.push(requirement);
            }
        }
        certificate.target_requirements = selected_target_requirement_uses
            .into_iter()
            .map(|requirement| {
                let proof = object_proofs
                    .get(&requirement.well_defined_obj_id)
                    .ok_or_else(|| {
                        missing_well_definedness_proof_error(format!(
                            "target requirement cites missing well-defined object proof {}",
                            requirement.well_defined_obj_id.value()
                        ))
                    })?;
                if !proof.target_requirements.iter().any(|retained| {
                    retained.role == requirement.role
                        && retained.fact_id == requirement.fact_id
                        && retained.expected_proposition.to_string()
                            == requirement.expected_proposition.to_string()
                }) {
                    return Err(missing_well_definedness_proof_error(format!(
                        "target requirement is not an edge of well-defined object proof {}",
                        requirement.well_defined_obj_id.value()
                    )));
                }
                Ok(WellDefinednessTargetRequirementEvidence::new(
                    requirement.source_occurrence_id,
                    requirement.well_defined_obj_id,
                    requirement.phase,
                    requirement.role,
                    requirement.fact_id,
                    requirement.expected_proposition,
                ))
            })
            .collect::<Result<Vec<_>, RuntimeError>>()?;
        Ok(certificate)
    }

    /// End the statement-local lifetime on every active scope of the current execution frame.
    pub(crate) fn clear_statement_verified_atomic_facts(&mut self) {
        let Some(frame) = self.execution_stack.last_mut() else {
            return;
        };
        let module_id = frame.module_id;
        let layer = frame.layer;
        for environment in frame.local_environment_stack.iter_mut() {
            environment.statement_verified_atomic_facts.clear();
        }

        let Some(module) = self.module_manager.module_mut(module_id) else {
            return;
        };
        module
            .main_environment
            .statement_verified_atomic_facts
            .clear();
        if let ExecutionLayer::File(file_id) = layer {
            if let Some(file) = module.file_mut(file_id) {
                file.environment.statement_verified_atomic_facts.clear();
            }
        }
    }
}

fn missing_well_definedness_proof_error(message: String) -> RuntimeError {
    UnknownRuntimeError(RuntimeErrorStruct::new_with_just_msg(message)).into()
}

fn target_requirement_phase_priority(phase: WellDefinednessTargetRequirementPhase) -> u8 {
    match phase {
        WellDefinednessTargetRequirementPhase::Store => 0,
        WellDefinednessTargetRequirementPhase::Preflight => 1,
        WellDefinednessTargetRequirementPhase::Proof => 2,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn successful_atomic_fact_is_shared_until_statement_memo_is_cleared() {
        let mut runtime = new_test_runtime();
        let fact = parse_atomic_fact(&mut runtime, "1 < 2");

        let first = runtime
            .verify_atomic_fact(&fact, &UseContextVerifyState::new(0, false))
            .expect("first verification should run");
        let first_source = statement_memo_source(&first);
        assert!(runtime
            .top_level_env()
            .statement_verified_atomic_facts
            .contains_key(&fact.to_string()));
        assert!(runtime
            .verify_fact_from_cache_using_display_string(&fact.clone().into())
            .is_none());

        let second = runtime
            .verify_atomic_fact(&fact, &UseContextVerifyState::new(0, false))
            .expect("second verification should hit the statement memo");
        let second_source = statement_memo_source(&second);
        assert!(Rc::ptr_eq(first_source, second_source));
        assert!(second.infer_result().is_empty());
        let output = display_stmt_exec_result_json(&runtime, &second, false);
        assert!(output.contains("number comparison"), "{output}");
        assert!(!output.contains("statement memo"), "{output}");

        runtime.clear_statement_verified_atomic_facts();
        assert!(runtime
            .top_level_env()
            .statement_verified_atomic_facts
            .is_empty());
    }

    #[test]
    fn unknown_atomic_fact_is_not_remembered() {
        let mut runtime = new_test_runtime();
        let fact = parse_atomic_fact(&mut runtime, "1 = 2");

        let result = runtime
            .verify_atomic_fact(&fact, &UseContextVerifyState::new(0, false))
            .expect("unknown verification should not error");
        assert!(result.is_unknown());
        assert!(!runtime
            .top_level_env()
            .statement_verified_atomic_facts
            .contains_key(&fact.to_string()));

        runtime.clear_statement_verified_atomic_facts();
        let stmt = parse_stmt(&mut runtime, "1 = 2");
        assert!(runtime.exec_stmt(&stmt).is_err());
        assert!(runtime
            .top_level_env()
            .statement_verified_atomic_facts
            .is_empty());
    }

    #[test]
    fn local_environment_memo_is_visible_inward_and_discarded_outward() {
        let mut runtime = new_test_runtime();
        let parent_fact = parse_atomic_fact(&mut runtime, "1 < 2");
        let child_fact = parse_atomic_fact(&mut runtime, "2 < 3");
        runtime
            .verify_atomic_fact(&parent_fact, &UseContextVerifyState::new(0, false))
            .expect("parent fact should verify");

        runtime
            .run_in_local_env(|runtime| {
                assert!(runtime
                    .verify_atomic_fact_from_statement_memo(&parent_fact)
                    .is_some());
                runtime.verify_atomic_fact(&child_fact, &UseContextVerifyState::new(0, false))?;
                assert!(runtime
                    .top_level_env()
                    .statement_verified_atomic_facts
                    .contains_key(&child_fact.to_string()));
                Ok::<(), RuntimeError>(())
            })
            .expect("local verification should succeed");

        assert!(runtime
            .verify_atomic_fact_from_statement_memo(&parent_fact)
            .is_some());
        assert!(runtime
            .verify_atomic_fact_from_statement_memo(&child_fact)
            .is_none());
    }

    #[test]
    fn known_only_entry_points_reuse_statement_proofs() {
        let mut runtime = new_test_runtime();
        let set_fact = parse_atomic_fact(&mut runtime, "$is_set(R)");
        let first_set_result = runtime
            .verify_atomic_fact(&set_fact, &UseContextVerifyState::new(0, false))
            .expect("builtin set fact should verify");
        let set_source = statement_memo_source(&first_set_result).clone();
        let known_set_result = runtime
            .verify_non_equational_atomic_fact_with_known_atomic_facts(&set_fact)
            .expect("known-only non-equality entry should consult the statement memo");
        assert!(Rc::ptr_eq(
            &set_source,
            statement_memo_source(&known_set_result)
        ));

        let equality = parse_atomic_fact(&mut runtime, "1 = 1");
        let first_equality_result = runtime
            .verify_atomic_fact(&equality, &UseContextVerifyState::new(0, false))
            .expect("reflexive equality should verify");
        let equality_source = statement_memo_source(&first_equality_result).clone();
        let AtomicFact::EqualFact(equality_fact) = equality else {
            unreachable!()
        };
        let known_equality_result = runtime.verify_objs_are_equal_by_known_equality(
            &equality_fact.left,
            &equality_fact.right,
            equality_fact.line_file,
        );
        assert!(Rc::ptr_eq(
            &equality_source,
            statement_memo_source(&known_equality_result)
        ));
    }

    #[test]
    fn next_statement_does_not_inherit_the_previous_memo_source() {
        let mut runtime = new_test_runtime();
        let fact = parse_atomic_fact(&mut runtime, "1 < 2");
        let first = runtime
            .verify_atomic_fact(&fact, &UseContextVerifyState::new(0, false))
            .expect("temporary proof should verify");
        let first_source = statement_memo_source(&first).clone();

        let stmt = parse_stmt(&mut runtime, "1 < 2");
        let second = runtime
            .exec_stmt(&stmt)
            .expect("the next statement should verify independently");
        let second_source = statement_memo_source(&second);
        assert!(!Rc::ptr_eq(&first_source, second_source));
        assert!(runtime
            .top_level_env()
            .statement_verified_atomic_facts
            .is_empty());
    }

    #[test]
    fn exec_stmt_clears_temporary_successes_but_keeps_the_proof_evidence() {
        let mut runtime = new_test_runtime();
        let stmt = parse_stmt(&mut runtime, "1 < 2");
        let Stmt::Fact(Fact::AtomicFact(fact)) = &stmt else {
            unreachable!()
        };
        let result = runtime.exec_stmt(&stmt).expect("statement should verify");

        assert!(runtime
            .top_level_env()
            .statement_verified_atomic_facts
            .is_empty());
        assert!(runtime
            .verify_fact_from_cache_using_display_string(&fact.clone().into())
            .is_some());
        let output = display_stmt_exec_result_json(&runtime, &result, false);
        assert!(output.contains("number comparison"), "{output}");
        assert!(!output.contains("statement memo"), "{output}");
    }

    #[test]
    fn compile_to_lean_capture_retains_function_domain_well_definedness_proof() {
        let mut runtime = new_test_runtime();
        runtime.replace_litex_to_lean_well_definedness_mode(true);
        let stmt = parse_stmt(&mut runtime, "forall f fn(x R: x > 0) R:\n    f(2) = f(2)");

        let result = runtime
            .exec_stmt(&stmt)
            .expect("restricted-domain application should verify in Litex");
        let certificate = &result
            .factual_success()
            .expect("forall should return a factual success")
            .well_definedness;

        assert!(
            certificate
                .facts
                .iter()
                .any(|evidence| evidence.proof.stmt.to_string() == "2 > 0"),
            "captured facts: {:?}",
            certificate
                .facts
                .iter()
                .map(|evidence| evidence.proof.stmt.to_string())
                .collect::<Vec<_>>()
        );
        let requirements = certificate
            .target_requirements
            .iter()
            .filter(|requirement| {
                requirement.expected_proposition.to_string() == "2 > 0"
                    && requirement.role
                        == WellDefinednessRequirementRole::FunctionDomain {
                            layer_index: 0,
                            domain_index: 0,
                        }
            })
            .collect::<Vec<_>>();
        assert_eq!(
            requirements.len(),
            2,
            "each source application must retain an exact target-use edge"
        );
        assert_ne!(
            requirements[0].source_occurrence_id, requirements[1].source_occurrence_id,
            "equal source expressions still have distinct parser-owned occurrences"
        );
        assert_eq!(
            requirements[0].well_defined_obj_id, requirements[1].well_defined_obj_id,
            "the second occurrence should cite the first occurrence's cached proof"
        );
        assert_eq!(
            requirements[0].well_defined_fact_id, requirements[1].well_defined_fact_id,
            "both cached uses should cite the same checked domain fact"
        );
        assert!(
            requirements.iter().all(
                |requirement| requirement.phase == WellDefinednessTargetRequirementPhase::Proof
            ),
            "the final target edge must come from the statement's proof scope"
        );
        let requirement = requirements[0];
        let object = certificate
            .objects
            .iter()
            .find(|object| object.well_defined_obj_id == requirement.well_defined_obj_id)
            .expect("the domain-proof reference must point to a checked object proof");
        assert!(object.object.to_string().ends_with("f(2)"));
        assert!(object
            .well_defined_fact_ids
            .contains(&requirement.well_defined_fact_id));
    }

    #[test]
    fn compile_to_lean_capture_retains_all_division_target_requirements() {
        let mut runtime = new_test_runtime();
        runtime.replace_litex_to_lean_well_definedness_mode(true);
        let stmt = parse_stmt(
            &mut runtime,
            "forall a, b C:\n    b != 0\n    =>:\n        a / b = a / b",
        );

        let result = runtime
            .exec_stmt(&stmt)
            .expect("nonzero complex division should verify in Litex");
        let certificate = &result
            .factual_success()
            .expect("forall should return a factual success")
            .well_definedness;
        let divisions = certificate
            .objects
            .iter()
            .filter(|object| matches!(&object.object, Obj::Div(_)))
            .collect::<Vec<_>>();
        assert!(!divisions.is_empty(), "division must have a frozen WD node");
        for division in divisions {
            assert_eq!(
                division.target_requirements.len(),
                3,
                "division must retain two complex memberships and one nonzero proof"
            );
            assert!(division.target_requirements.iter().any(|requirement| {
                requirement.role
                    == WellDefinednessRequirementRole::BuiltinArgumentMembership {
                        argument_index: 0,
                    }
            }));
            assert!(division.target_requirements.iter().any(|requirement| {
                requirement.role
                    == WellDefinednessRequirementRole::BuiltinArgumentMembership {
                        argument_index: 1,
                    }
            }));
            assert!(division.target_requirements.iter().any(|requirement| {
                requirement.role
                    == WellDefinednessRequirementRole::BuiltinArgumentNonzero { argument_index: 1 }
            }));
        }
    }

    #[test]
    fn compile_to_lean_capture_retains_list_set_children_and_pairwise_requirements() {
        fn check() {
            let mut runtime = new_test_runtime();
            runtime.replace_litex_to_lean_well_definedness_mode(true);
            let stmt = parse_stmt(
                &mut runtime,
                "forall a, b set:\n    a != b\n    =>:\n        {a, b} = {a, b}",
            );

            let result = runtime
                .exec_stmt(&stmt)
                .expect("a pairwise-distinct finite set literal should verify in Litex");
            let certificate = &result
                .factual_success()
                .expect("forall should return a factual success")
                .well_definedness;
            let list_sets = certificate
                .objects
                .iter()
                .filter(|object| matches!(&object.object, Obj::ListSet(_)))
                .collect::<Vec<_>>();
            assert!(
                !list_sets.is_empty(),
                "the list-set constructor must have a frozen WD node"
            );
            for list_set in list_sets {
                assert_eq!(
                    list_set.child_uses.len(),
                    2,
                    "the constructor must retain one ordered child edge per entry"
                );
                for argument_index in 0..2 {
                    assert!(list_set.child_uses.iter().any(|child| {
                        child.role
                            == WellDefinedObjChildRole::ConstructorArgument { argument_index }
                    }));
                }
                assert_eq!(
                    list_set.target_requirements.len(),
                    1,
                    "a two-entry list set must retain one distinctness proof"
                );
                let requirement = &list_set.target_requirements[0];
                assert_eq!(
                    requirement.role,
                    WellDefinednessRequirementRole::ConstructorPairwiseDistinct {
                        left_index: 0,
                        right_index: 1,
                    }
                );
                let Fact::AtomicFact(AtomicFact::NotEqualFact(pair)) =
                    &requirement.expected_proposition
                else {
                    panic!("the indexed list-set requirement must be an inequality")
                };
                let Obj::ListSet(source) = &list_set.object else {
                    unreachable!("filtered to list-set WD nodes")
                };
                assert_eq!(
                    obj_equality_key(&pair.left),
                    obj_equality_key(source.list[0].as_ref())
                );
                assert_eq!(
                    obj_equality_key(&pair.right),
                    obj_equality_key(source.list[1].as_ref())
                );
                assert!(
                    list_set
                        .well_defined_fact_ids
                        .contains(&requirement.fact_id),
                    "the indexed target edge must cite an environment-owned WD fact"
                );
            }
        }

        std::thread::Builder::new()
            .name("list_set_wd_capture_test".to_string())
            .stack_size(64 * 1024 * 1024)
            .spawn(check)
            .expect("spawn list-set WD capture test")
            .join()
            .expect("list-set WD capture test thread panicked");
    }

    #[test]
    fn compile_to_lean_capture_does_not_accept_a_boolean_obj_cache_without_proof_evidence() {
        let mut runtime = new_test_runtime();
        let warmup = parse_stmt(&mut runtime, "2 > 0");
        runtime
            .exec_stmt(&warmup)
            .expect("warmup fact should populate ordinary verifier caches");

        runtime.replace_litex_to_lean_well_definedness_mode(true);
        let stmt = parse_stmt(&mut runtime, "forall f fn(x R: x > 0) R:\n    f(2) = f(2)");
        let result = runtime
            .exec_stmt(&stmt)
            .expect("cached restricted-domain application should still verify");
        let certificate = &result.factual_success().unwrap().well_definedness;
        assert!(certificate
            .facts
            .iter()
            .any(|evidence| evidence.proof.stmt.to_string() == "2 > 0"));
    }

    #[test]
    fn compile_to_lean_capture_retains_have_fn_body_well_definedness_proofs() {
        let mut runtime = new_test_runtime();
        runtime.replace_litex_to_lean_well_definedness_mode(true);
        let stmt = parse_stmt(&mut runtime, "have fn reciprocal(x R: x != 0) R = 1 / x");

        let result = runtime
            .exec_stmt(&stmt)
            .expect("restricted function definition should verify in Litex");
        let success = result
            .non_factual_success()
            .expect("have-fn should return a non-factual success");
        let captured = success
            .well_definedness
            .facts
            .iter()
            .map(|evidence| evidence.proof.stmt.to_string())
            .collect::<Vec<_>>();

        assert!(
            captured.iter().any(|fact| fact.ends_with("x != 0")),
            "captured facts: {captured:?}"
        );
        assert_eq!(
            success.inside_results.len(),
            1,
            "have-fn must retain its checked return-membership result"
        );
        let verification = success
            .function_definition_verification
            .as_ref()
            .expect("have-fn must freeze its body-to-environment verification mapping");
        assert_eq!(verification.return_check_index, 0);
        assert_eq!(
            verification.assumption_infers.store_fact_outputs.len(),
            2,
            "the function parameter and domain premise must both be retained"
        );
        assert!(verification
            .assumption_infers
            .store_fact_outputs
            .iter()
            .all(|output| output.fact_id.is_some()));
        assert!(verification
            .function_membership
            .to_string()
            .contains("reciprocal $in fn"));
        assert!(verification
            .defining_equality
            .to_string()
            .contains("reciprocal = fn"));
        let return_check = success.inside_results[0]
            .factual_success()
            .expect("the retained return check must be factual");
        assert!(
            return_check.stmt.to_string().ends_with("x $in R"),
            "return check: {}",
            return_check.stmt
        );
        assert_eq!(
            success.infers.store_fact_outputs.len(),
            2,
            "stored function effects: {:?}",
            success.infers
        );
        assert!(
            success
                .infers
                .store_fact_outputs
                .iter()
                .all(|output| output.inferred_facts.is_empty()),
            "unexpected inferred function effects: {:?}",
            success.infers
        );
    }

    #[test]
    fn well_defined_application_cache_reuses_the_environment_proof_id() {
        let mut runtime = new_test_runtime();
        let declaration = parse_stmt(&mut runtime, "have f fn(x R) R");
        runtime
            .exec_stmt(&declaration)
            .expect("function declaration should verify");
        runtime.replace_litex_to_lean_well_definedness_mode(true);
        let application = equality_left_obj(&mut runtime, "f(1) = f(1)");

        let first = capture_well_defined_obj(&mut runtime, &application);
        let proof_count = runtime.top_level_env().well_defined_obj_proofs.len();
        let fact_count = runtime.top_level_env().well_defined_fact_proofs.len();
        runtime.clear_statement_verified_atomic_facts();
        let second = capture_well_defined_obj(&mut runtime, &application);

        assert_eq!(first.root_obj_ids.len(), 1);
        assert_eq!(second.root_obj_ids, first.root_obj_ids);
        assert_eq!(
            runtime.top_level_env().well_defined_obj_proofs.len(),
            proof_count
        );
        assert_eq!(
            runtime.top_level_env().well_defined_fact_proofs.len(),
            fact_count
        );
        assert_eq!(
            second
                .facts
                .iter()
                .map(|evidence| evidence.well_defined_fact_id)
                .collect::<Vec<_>>(),
            first
                .facts
                .iter()
                .map(|evidence| evidence.well_defined_fact_id)
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn root_object_proof_use_retains_each_execution_phase() {
        let mut runtime = new_test_runtime();
        runtime.replace_litex_to_lean_well_definedness_mode(true);
        let object = equality_left_obj(&mut runtime, "1 = 1");
        runtime.begin_statement_well_definedness_capture();
        runtime
            .verify_obj_well_defined_and_store_cache(
                &object,
                &UseContextVerifyState::new_with_final_round(false),
            )
            .expect("preflight numeral should be well-defined");
        runtime.set_well_definedness_target_requirement_phase(
            WellDefinednessTargetRequirementPhase::Proof,
        );
        runtime
            .verify_obj_well_defined_and_store_cache(
                &object,
                &UseContextVerifyState::new_with_final_round(false),
            )
            .expect("proof-phase numeral should reuse its WD cache node");
        let certificate = runtime
            .end_statement_well_definedness_capture()
            .expect("phase-labelled root uses should freeze");

        assert_eq!(certificate.root_obj_ids.len(), 1);
        assert_eq!(certificate.root_proof_uses.len(), 2);
        assert!(certificate.root_proof_uses.iter().any(|root_use| {
            root_use.phase == WellDefinednessTargetRequirementPhase::Preflight
                && root_use.well_defined_obj_id == certificate.root_obj_ids[0]
        }));
        assert!(certificate.root_proof_uses.iter().any(|root_use| {
            root_use.phase == WellDefinednessTargetRequirementPhase::Proof
                && root_use.well_defined_obj_id == certificate.root_obj_ids[0]
        }));
    }

    #[test]
    fn replacing_the_current_function_contract_invalidates_application_cache() {
        let mut runtime = new_test_runtime();
        let declaration = parse_stmt(&mut runtime, "have f fn(x R) R");
        runtime
            .exec_stmt(&declaration)
            .expect("function declaration should verify");
        let old_contract_id = current_function_membership_fact_id(&runtime, "f");
        runtime.replace_litex_to_lean_well_definedness_mode(true);
        let application = equality_left_obj(&mut runtime, "f(1) = f(1)");
        let first = capture_well_defined_obj(&mut runtime, &application);

        runtime.replace_litex_to_lean_well_definedness_mode(false);
        let replacement = parse_stmt(&mut runtime, "f $in fn(x R) R+");
        let Stmt::Fact(replacement_fact) = replacement else {
            panic!("expected function membership fact")
        };
        runtime
            .store_without_well_defined_verification_and_infer(replacement_fact)
            .expect("test setup should replace the current function slot");
        let new_contract_id = current_function_membership_fact_id(&runtime, "f");
        assert_ne!(new_contract_id, old_contract_id);

        runtime.replace_litex_to_lean_well_definedness_mode(true);
        runtime.clear_statement_verified_atomic_facts();
        let second = capture_well_defined_obj(&mut runtime, &application);
        assert_ne!(second.root_obj_ids, first.root_obj_ids);
        let second_root = runtime
            .well_defined_obj_proof(second.root_obj_ids[0])
            .expect("new application proof should remain environment-visible");
        assert!(second_root.cache_key.function_contracts.contains(
            &WellDefinedFunctionContract::StoredMembershipFact(new_contract_id)
        ));
        assert!(!second_root.cache_key.function_contracts.contains(
            &WellDefinedFunctionContract::StoredMembershipFact(old_contract_id)
        ));
    }

    #[test]
    fn nested_function_application_is_retained_as_a_direct_proof_dag() {
        let mut runtime = new_test_runtime();
        runtime.replace_litex_to_lean_well_definedness_mode(true);
        let stmt = parse_stmt(
            &mut runtime,
            "forall f fn(u R) R, g fn(v R) R, h fn(w R) R, x R:\n    f(g(h(x))) = f(g(h(x)))",
        );
        let result = runtime
            .exec_stmt(&stmt)
            .expect("nested function application should verify");
        let certificate = &result.factual_success().unwrap().well_definedness;
        let object_names = certificate
            .objects
            .iter()
            .map(|proof| strip_free_param_numeric_tags_in_display(&proof.object.to_string()))
            .collect::<Vec<_>>();
        let outer = certificate
            .objects
            .iter()
            .find(|proof| {
                strip_free_param_numeric_tags_in_display(&proof.object.to_string())
                    .ends_with("f(g(h(x)))")
            })
            .unwrap_or_else(|| panic!("outer application proof; objects: {object_names:?}"));
        let middle = outer
            .child_uses
            .iter()
            .find_map(|child| {
                certificate.objects.iter().find(|proof| {
                    proof.well_defined_obj_id == child.obj_id
                        && strip_free_param_numeric_tags_in_display(&proof.object.to_string())
                            .ends_with("g(h(x))")
                })
            })
            .expect("outer proof should cite the direct middle application proof");
        assert!(middle.child_uses.iter().any(|child| {
            certificate.objects.iter().any(|proof| {
                proof.well_defined_obj_id == child.obj_id
                    && strip_free_param_numeric_tags_in_display(&proof.object.to_string())
                        .ends_with("h(x)")
            })
        }));
        let outer_ids = certificate
            .objects
            .iter()
            .filter(|proof| {
                strip_free_param_numeric_tags_in_display(&proof.object.to_string())
                    .ends_with("f(g(h(x)))")
            })
            .map(|proof| proof.well_defined_obj_id)
            .collect::<std::collections::HashSet<_>>();
        assert!(!outer_ids.is_empty());
    }

    #[test]
    fn layered_function_application_freezes_the_callable_prefix() {
        let mut runtime = new_test_runtime();
        runtime.replace_litex_to_lean_well_definedness_mode(true);
        let stmt = parse_stmt(
            &mut runtime,
            "forall g fn(x R) fn(y R) R:\n    g(1)(2) = g(1)(2)",
        );
        let result = runtime
            .exec_stmt(&stmt)
            .expect("layered function application should verify");
        let certificate = &result.factual_success().unwrap().well_definedness;
        let outer = certificate
            .objects
            .iter()
            .find(|object| {
                strip_free_param_numeric_tags_in_display(&object.object.to_string())
                    .ends_with("g(1)(2)")
            })
            .expect("the full layered application must have an object ID");
        let prefix_uses = outer
            .child_uses
            .iter()
            .filter(|child| {
                child.role
                    == WellDefinedObjChildRole::FunctionPrefix {
                        through_layer_index: 0,
                    }
            })
            .collect::<Vec<_>>();
        assert_eq!(prefix_uses.len(), 1);
        let prefix = certificate
            .objects
            .iter()
            .find(|object| object.well_defined_obj_id == prefix_uses[0].obj_id)
            .expect("the callable-prefix edge must resolve to a frozen object");
        assert!(
            strip_free_param_numeric_tags_in_display(&prefix.object.to_string()).ends_with("g(1)")
        );
        assert!(matches!(prefix.intrinsic_result_set, Some(Obj::FnSet(_))));
        assert!(outer.child_uses.iter().any(|child| {
            child.role
                == WellDefinedObjChildRole::FunctionArgument {
                    layer_index: 1,
                    argument_index: 0,
                }
        }));
    }

    #[test]
    fn repeated_function_argument_keeps_both_ordered_child_uses() {
        let mut runtime = new_test_runtime();
        runtime.replace_litex_to_lean_well_definedness_mode(true);
        let stmt = parse_stmt(
            &mut runtime,
            "forall f fn(u, v R) R, g fn(x R) R, a R:\n    f(g(a), g(a)) = f(g(a), g(a))",
        );
        let result = runtime
            .exec_stmt(&stmt)
            .expect("repeated cached argument should verify");
        let certificate = &result.factual_success().unwrap().well_definedness;
        let outer = certificate
            .objects
            .iter()
            .find(|object| {
                strip_free_param_numeric_tags_in_display(&object.object.to_string())
                    .ends_with("f(g(a), g(a))")
            })
            .expect("outer application object should be retained");
        let argument_uses = outer
            .child_uses
            .iter()
            .filter(|child| {
                matches!(
                    child.role,
                    WellDefinedObjChildRole::FunctionArgument { layer_index: 0, .. }
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(argument_uses.len(), 2);
        assert_eq!(argument_uses[0].obj_id, argument_uses[1].obj_id);
        assert_eq!(
            argument_uses[0].role,
            WellDefinedObjChildRole::FunctionArgument {
                layer_index: 0,
                argument_index: 0,
            }
        );
        assert_eq!(
            argument_uses[1].role,
            WellDefinedObjChildRole::FunctionArgument {
                layer_index: 0,
                argument_index: 1,
            }
        );
    }

    #[test]
    fn nested_function_application_dag_names_each_direct_child_before_parent() {
        let mut runtime = new_test_runtime();
        runtime.replace_litex_to_lean_well_definedness_mode(true);
        let stmt = parse_stmt(
            &mut runtime,
            "forall f fn(u, v R) R, g fn(x R) R, t fn(y R) R, a, b R:\n    f(g(a), t(b)) = f(g(a), t(b))",
        );
        let result = runtime
            .exec_stmt(&stmt)
            .expect("nested cached application should verify");
        let certificate = &result.factual_success().unwrap().well_definedness;
        let outer = certificate
            .objects
            .iter()
            .find(|object| {
                strip_free_param_numeric_tags_in_display(&object.object.to_string())
                    .ends_with("f(g(a), t(b))")
            })
            .expect("outer application object should be retained");
        let direct_arguments = outer
            .child_uses
            .iter()
            .filter(|child| {
                matches!(
                    child.role,
                    WellDefinedObjChildRole::FunctionArgument { layer_index: 0, .. }
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(direct_arguments.len(), 2);
        assert_eq!(
            direct_arguments[0].role,
            WellDefinedObjChildRole::FunctionArgument {
                layer_index: 0,
                argument_index: 0,
            }
        );
        assert_eq!(
            direct_arguments[1].role,
            WellDefinedObjChildRole::FunctionArgument {
                layer_index: 0,
                argument_index: 1,
            }
        );
        assert_ne!(direct_arguments[0].obj_id, direct_arguments[1].obj_id);

        let first_child = certificate
            .objects
            .iter()
            .find(|object| object.well_defined_obj_id == direct_arguments[0].obj_id)
            .expect("g(a) child ID should resolve in the frozen environment DAG");
        let second_child = certificate
            .objects
            .iter()
            .find(|object| object.well_defined_obj_id == direct_arguments[1].obj_id)
            .expect("t(b) child ID should resolve in the frozen environment DAG");
        assert!(
            strip_free_param_numeric_tags_in_display(&first_child.object.to_string())
                .ends_with("g(a)")
        );
        assert!(
            strip_free_param_numeric_tags_in_display(&second_child.object.to_string())
                .ends_with("t(b)")
        );
        assert!(certificate
            .root_obj_ids
            .contains(&outer.well_defined_obj_id));
    }

    #[test]
    fn compiler_well_defined_facts_do_not_enter_the_ordinary_fact_cache() {
        let mut runtime = new_test_runtime();
        runtime.replace_litex_to_lean_well_definedness_mode(true);
        let stmt = parse_stmt(&mut runtime, "forall f fn(x R: x > 0) R:\n    f(2) = f(2)");
        let result = runtime.exec_stmt(&stmt).expect("statement should verify");
        let certificate = &result.factual_success().unwrap().well_definedness;
        let positivity = certificate
            .facts
            .iter()
            .find(|evidence| evidence.proof.stmt.to_string() == "2 > 0")
            .expect("WD environment should retain the checked domain fact");
        assert!(runtime
            .well_defined_fact_proof(positivity.well_defined_fact_id)
            .is_some());
        assert!(runtime
            .known_fact_id_for_fact(&positivity.proof.stmt)
            .expect("fact lookup should succeed")
            .is_none());
    }

    #[test]
    fn binder_owned_boolean_cache_is_not_reused_as_a_compiler_proof() {
        let mut runtime = new_test_runtime();
        let membership = parse_atomic_fact(&mut runtime, "1 $in {x R: x > 0}");
        let AtomicFact::InFact(membership) = membership else {
            unreachable!()
        };
        let set_builder: Obj = membership.set;
        let ordinary_key = WellDefinedCacheKey::without_function_contract(set_builder.to_string());

        runtime
            .verify_obj_well_defined_and_store_cache(
                &set_builder,
                &UseContextVerifyState::new_with_final_round(false),
            )
            .expect("ordinary verification should cache the binder-owned object");
        assert!(runtime
            .well_defined_cache_key_for_obj(&set_builder)
            .is_none());
        assert_eq!(
            runtime
                .well_defined_cache_entry(&ordinary_key)
                .and_then(|entry| entry.obj_id),
            None,
            "the ordinary binder cache should remain proofless"
        );

        runtime.replace_litex_to_lean_well_definedness_mode(true);
        let certificate = capture_well_defined_obj(&mut runtime, &set_builder);
        assert_eq!(certificate.root_obj_ids.len(), 1);
        assert!(
            certificate
                .objects
                .iter()
                .any(|proof| proof.well_defined_obj_id == certificate.root_obj_ids[0]),
            "To-Lean must recompute and retain a real DAG instead of citing the boolean entry"
        );
        assert_eq!(
            runtime
                .well_defined_cache_entry(&ordinary_key)
                .and_then(|entry| entry.obj_id),
            None,
            "a binder-owned compiler proof is deliberately not reusable as a cache entry"
        );
    }

    #[test]
    fn temporary_child_wd_store_sees_parent_and_does_not_leak_outward() {
        let mut runtime = new_test_runtime();
        let declaration = parse_stmt(&mut runtime, "have f fn(x R) R");
        runtime
            .exec_stmt(&declaration)
            .expect("function declaration should verify");
        runtime.replace_litex_to_lean_well_definedness_mode(true);

        let parent_application = equality_left_obj(&mut runtime, "f(1) = f(1)");
        let parent_certificate = capture_well_defined_obj(&mut runtime, &parent_application);
        let child_application = equality_left_obj(&mut runtime, "f(2) = f(2)");
        let child_key = runtime
            .well_defined_cache_key_for_obj(&child_application)
            .expect("named application should have a cache key");

        let child_certificate = runtime
            .run_in_local_env(|runtime| {
                let reused_parent = capture_well_defined_obj(runtime, &parent_application);
                assert_eq!(
                    reused_parent.root_obj_ids, parent_certificate.root_obj_ids,
                    "a child environment should cite its parent's exact proof ID"
                );
                Ok::<_, RuntimeError>(capture_well_defined_obj(runtime, &child_application))
            })
            .expect("temporary child verification should succeed");

        assert_eq!(child_certificate.root_obj_ids.len(), 1);
        assert!(
            child_certificate
                .objects
                .iter()
                .any(|proof| proof.well_defined_obj_id == child_certificate.root_obj_ids[0]),
            "the frozen StmtResult projection should own its child proof snapshot"
        );
        assert!(
            runtime
                .well_defined_obj_proof(child_certificate.root_obj_ids[0])
                .is_none(),
            "an unreferenced temporary child proof must disappear with its environment"
        );
        assert!(
            runtime.well_defined_cache_entry(&child_key).is_none(),
            "a temporary child cache entry must not leak into its parent"
        );
    }

    #[test]
    fn outer_capture_promotes_referenced_child_wd_dag_but_not_child_cache() {
        let mut runtime = new_test_runtime();
        let declaration = parse_stmt(&mut runtime, "have f fn(x R) R");
        runtime
            .exec_stmt(&declaration)
            .expect("function declaration should verify");
        runtime.replace_litex_to_lean_well_definedness_mode(true);
        let application = equality_left_obj(&mut runtime, "f(2) = f(2)");
        let cache_key = runtime
            .well_defined_cache_key_for_obj(&application)
            .expect("named application should have a cache key");

        runtime.begin_statement_well_definedness_capture();
        runtime
            .run_in_local_env(|runtime| {
                runtime.verify_obj_well_defined_and_store_cache(
                    &application,
                    &UseContextVerifyState::new_with_final_round(false),
                )?;
                Ok::<(), RuntimeError>(())
            })
            .expect("child verification should succeed");
        let certificate = runtime
            .end_statement_well_definedness_capture()
            .expect("the parent should be able to freeze the referenced child DAG");

        assert_eq!(certificate.root_obj_ids.len(), 1);
        assert!(runtime
            .well_defined_obj_proof(certificate.root_obj_ids[0])
            .is_some());
        assert!(
            runtime.well_defined_cache_entry(&cache_key).is_none(),
            "proof projection does not make a child-scope cache reusable"
        );
    }

    #[test]
    fn committed_child_merges_wd_store_and_cache() {
        let mut runtime = new_test_runtime();
        let declaration = parse_stmt(&mut runtime, "have f fn(x R) R");
        runtime
            .exec_stmt(&declaration)
            .expect("function declaration should verify");
        runtime.replace_litex_to_lean_well_definedness_mode(true);
        let application = equality_left_obj(&mut runtime, "f(3) = f(3)");
        let cache_key = runtime
            .well_defined_cache_key_for_obj(&application)
            .expect("named application should have a cache key");

        let certificate = runtime
            .run_in_local_env_and_commit(|runtime| {
                Ok(capture_well_defined_obj(runtime, &application))
            })
            .expect("committed child verification should succeed");

        let root_id = certificate.root_obj_ids[0];
        assert!(runtime.well_defined_obj_proof(root_id).is_some());
        assert_eq!(
            runtime
                .well_defined_cache_entry(&cache_key)
                .and_then(|entry| entry.obj_id),
            Some(root_id),
            "committing an environment should merge its WD proof store and cache"
        );
    }

    fn new_test_runtime() -> Runtime {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("statement_memo_test.lit");
        runtime
    }

    fn parse_atomic_fact(runtime: &mut Runtime, source: &str) -> AtomicFact {
        let stmt = parse_stmt(runtime, source);
        let Stmt::Fact(Fact::AtomicFact(fact)) = stmt else {
            panic!("expected an atomic fact: {source}");
        };
        fact
    }

    fn equality_left_obj(runtime: &mut Runtime, source: &str) -> Obj {
        let stmt = parse_stmt(runtime, source);
        let Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(fact))) = stmt else {
            panic!("expected equality fact: {source}")
        };
        fact.left
    }

    fn capture_well_defined_obj(runtime: &mut Runtime, object: &Obj) -> WellDefinednessCertificate {
        runtime.begin_statement_well_definedness_capture();
        runtime
            .verify_obj_well_defined_and_store_cache(
                object,
                &UseContextVerifyState::new_with_final_round(false),
            )
            .expect("object should be well-defined");
        runtime
            .end_statement_well_definedness_capture()
            .expect("environment proof projection should freeze")
    }

    fn current_function_membership_fact_id(runtime: &Runtime, name: &str) -> FactId {
        runtime
            .iter_environments_from_top()
            .find_map(|environment| {
                environment
                    .known_objs_in_fn_sets
                    .get(name)
                    .and_then(|info| info.fn_set_membership_fact_id)
            })
            .expect("function slot should retain its installing membership FactId")
    }

    fn parse_stmt(runtime: &mut Runtime, source: &str) -> Stmt {
        let tokenizer = Tokenizer::new();
        let mut blocks = tokenizer
            .parse_blocks(source, Rc::from("statement_memo_test.lit"))
            .expect("test statement should tokenize");
        assert_eq!(blocks.len(), 1);
        runtime
            .parse_stmt(&mut blocks[0])
            .expect("test statement should parse")
    }

    fn statement_memo_source(result: &StmtResult) -> &Rc<FactualStmtSuccess> {
        let success = result
            .factual_success()
            .expect("memoized atomic fact should be factual");
        let VerifiedByResult::StatementMemo(source) = &success.verified_by else {
            panic!("atomic success should retain its statement memo source");
        };
        source
    }
}
