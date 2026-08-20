use super::*;
use crate::prelude::{Fact, FactId, Obj, SourceObjectOccurrenceId, SuccessInferResult};
use std::collections::HashMap;
use std::rc::Rc;

/// Transitional backend projection. The canonical verifier result is the
/// recursive structure; legacy WD node IDs are allocated here, after
/// execution, solely for the existing Lean emitter.
pub(crate) fn project_compositional_well_definedness(
    result: &SuccessVerifyFactWellDefinedResult,
) -> Result<WellDefinednessCertificate, String> {
    project_compositional_well_definedness_many(std::slice::from_ref(result))
}

pub(crate) fn project_compositional_well_definedness_many(
    results: &[SuccessVerifyFactWellDefinedResult],
) -> Result<WellDefinednessCertificate, String> {
    let mut projector = CompositionalWellDefinednessProjector::default();
    for result in results {
        let recursive = result
            .recursive
            .as_deref()
            .ok_or_else(|| "successful fact WD result has no recursive proof".to_string())?;
        projector.walk_fact_proof(recursive, &[])?;
    }
    Ok(projector.certificate)
}

#[derive(Default)]
struct CompositionalWellDefinednessProjector {
    certificate: WellDefinednessCertificate,
    next_object_id: u64,
    next_fact_id: u64,
    next_scope_id: u64,
    // The canonical Rc proof can be reused from more than one lexical body.
    // The legacy backend node still carries an ambient path, so one canonical
    // proof must be projected once per backend scope context.
    object_ids_by_result: HashMap<(usize, Vec<WellDefinedBinderScopeId>), WellDefinedObjId>,
    active_object_ids_by_key: HashMap<String, WellDefinedObjId>,
    source_uses: HashMap<SourceObjectOccurrenceId, WellDefinedObjId>,
}

impl CompositionalWellDefinednessProjector {
    fn allocate_object_id(&mut self) -> WellDefinedObjId {
        self.next_object_id += 1;
        WellDefinedObjId::new(self.next_object_id)
    }

    fn allocate_fact_id(&mut self) -> WellDefinedFactId {
        self.next_fact_id += 1;
        WellDefinedFactId::new(self.next_fact_id)
    }

    fn allocate_scope_id(&mut self) -> WellDefinedBinderScopeId {
        self.next_scope_id += 1;
        WellDefinedBinderScopeId::new(self.next_scope_id)
    }

    fn premise_fact_id(
        &self,
        proposition: &Fact,
        infers: &SuccessInferResult,
    ) -> Result<FactId, String> {
        let proposition_key = proposition.to_string();
        infers
            .store_fact_outputs
            .iter()
            .find(|output| output.itself_and_why_itself_is_stored.0.to_string() == proposition_key)
            .and_then(|output| output.fact_id)
            .ok_or_else(|| format!("binder premise `{proposition}` has no frozen ordinary FactId"))
    }

    fn add_fact_evidence(
        &mut self,
        verification: Rc<SuccessVerifyFactResult>,
        ambient_scope_ids: &[WellDefinedBinderScopeId],
    ) -> WellDefinedFactId {
        let id = self.allocate_fact_id();
        self.certificate.facts.push(WellDefinednessFactEvidence {
            well_defined_fact_id: id,
            proof: verification,
            ambient_binder_scope_ids: ambient_scope_ids.to_vec(),
        });
        id
    }

    fn record_root(&mut self, object_id: WellDefinedObjId) {
        if !self.certificate.root_obj_ids.contains(&object_id) {
            self.certificate.root_obj_ids.push(object_id);
            self.certificate
                .root_proof_uses
                .push(WellDefinednessRootObjectProofUse::new(
                    object_id,
                    WellDefinednessTargetRequirementPhase::Proof,
                ));
        }
    }

    fn record_source_use(&mut self, object: &Obj, object_id: WellDefinedObjId) {
        let Some(source_occurrence_id) = object.source_occurrence_id() else {
            return;
        };
        if let Some(previous) = self.source_uses.insert(source_occurrence_id, object_id) {
            if previous == object_id {
                return;
            }
        }
        self.certificate
            .source_object_uses
            .retain(|source_use| source_use.source_occurrence_id != source_occurrence_id);
        self.certificate
            .source_object_uses
            .push(WellDefinednessSourceObjectUse::new(
                source_occurrence_id,
                object.clone(),
                object_id,
                WellDefinednessTargetRequirementPhase::Proof,
            ));
    }

    fn walk_fact_result(
        &mut self,
        result: &SuccessVerifyFactWellDefinedResult,
        ambient_scope_ids: &[WellDefinedBinderScopeId],
    ) -> Result<(), String> {
        let recursive = result
            .recursive
            .as_deref()
            .ok_or_else(|| "nested successful fact WD result has no recursive proof".to_string())?;
        self.walk_fact_proof(recursive, ambient_scope_ids)
    }

    fn walk_fact_binder(
        &mut self,
        binder: &SuccessVerifyFactBinderResult,
        ambient_scope_ids: &[WellDefinedBinderScopeId],
    ) -> Result<(), String> {
        for group in &binder.parameter_groups {
            if let Some(carrier) = &group.carrier {
                let object_id = self.walk_object(&carrier.result, ambient_scope_ids)?;
                self.record_root(object_id);
            }
            for parameter in &group.parameters {
                self.walk_fact_result(&parameter.well_definedness, ambient_scope_ids)?;
                let symbol_id = parameter
                    .symbol_id
                    .ok_or_else(|| "quantifier parameter premise has no SymbolId".to_string())?;
                self.certificate
                    .parameter_facts
                    .push(WellDefinednessParameterFactEvidence::new(
                        symbol_id,
                        self.premise_fact_id(&parameter.proposition, &parameter.infers)?,
                        parameter.proposition.clone(),
                    ));
            }
        }
        Ok(())
    }

    fn walk_local_fact(
        &mut self,
        result: &SuccessVerifyLocalFactWellDefinedResult,
        ambient_scope_ids: &[WellDefinedBinderScopeId],
    ) -> Result<(), String> {
        self.walk_fact_proof(&result.well_definedness, ambient_scope_ids)
    }

    fn walk_fact_proof(
        &mut self,
        result: &SuccessVerifyFactWellDefinedProofResult,
        ambient_scope_ids: &[WellDefinedBinderScopeId],
    ) -> Result<(), String> {
        match result {
            SuccessVerifyFactWellDefinedProofResult::AtomicFact(result) => {
                for argument in &result.arguments {
                    let object_id = self.walk_object(&argument.result, ambient_scope_ids)?;
                    self.record_root(object_id);
                }
            }
            SuccessVerifyFactWellDefinedProofResult::AndFact(result) => {
                for conjunct in &result.conjuncts {
                    self.walk_fact_proof(conjunct, ambient_scope_ids)?;
                }
            }
            SuccessVerifyFactWellDefinedProofResult::ChainFact(result) => {
                for comparison in &result.comparisons {
                    self.walk_fact_proof(comparison, ambient_scope_ids)?;
                }
            }
            SuccessVerifyFactWellDefinedProofResult::OrFact(result) => {
                for branch in &result.branches {
                    self.walk_fact_proof(branch, ambient_scope_ids)?;
                }
            }
            SuccessVerifyFactWellDefinedProofResult::ExistFact(result) => {
                self.walk_fact_binder(&result.binder, ambient_scope_ids)?;
                for body in &result.body {
                    self.walk_local_fact(body, ambient_scope_ids)?;
                }
            }
            SuccessVerifyFactWellDefinedProofResult::ForallFact(result) => {
                self.walk_fact_binder(&result.binder, ambient_scope_ids)?;
                for premise in &result.premises {
                    self.walk_local_fact(premise, ambient_scope_ids)?;
                }
                for conclusion in &result.conclusions {
                    self.walk_local_fact(conclusion, ambient_scope_ids)?;
                }
            }
            SuccessVerifyFactWellDefinedProofResult::ForallFactWithIff(result) => {
                self.walk_fact_proof(&result.forward, ambient_scope_ids)?;
                self.walk_fact_proof(&result.reverse, ambient_scope_ids)?;
            }
            SuccessVerifyFactWellDefinedProofResult::NotForallFact(result) => {
                self.walk_fact_proof(&result.inner, ambient_scope_ids)?;
            }
        }
        Ok(())
    }

    fn walk_child(
        &mut self,
        child: &SuccessVerifyChildObjWellDefinedResult,
        ambient_scope_ids: &[WellDefinedBinderScopeId],
    ) -> Result<WellDefinedObjChildUse, String> {
        let object_id = self.walk_object(&child.result, ambient_scope_ids)?;
        Ok(WellDefinedObjChildUse::new(
            child.role,
            object_id,
            child.source_object.clone(),
        ))
    }

    fn add_premise(
        &mut self,
        premise: &SuccessVerifyBinderPremiseResult,
        scope_ambient_ids: &[WellDefinedBinderScopeId],
        premises: &mut Vec<WellDefinedBinderPremiseProof>,
        assumption_infers: &mut SuccessInferResult,
    ) -> Result<(), String> {
        self.walk_fact_result(&premise.well_definedness, scope_ambient_ids)?;
        premises.push(WellDefinedBinderPremiseProof::new(
            premise.role,
            premise.symbol_id,
            self.premise_fact_id(&premise.proposition, &premise.infers)?,
            premise.proposition.clone(),
        ));
        assumption_infers.new_infer_result_inside(premise.infers.clone());
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn walk_object_binder(
        &mut self,
        owner_object: &Obj,
        binder: &SuccessVerifyBinderObjectWellDefinedResult,
        ambient_scope_ids: &[WellDefinedBinderScopeId],
        child_uses: &mut Vec<WellDefinedObjChildUse>,
        fact_ids: &mut Vec<WellDefinedFactId>,
        object_requirements: &mut Vec<WellDefinedTargetRequirementProof>,
    ) -> Result<Option<WellDefinedBinderScopeProof>, String> {
        // Iteration, finite-aggregate, reduce, and structure binders are
        // verifier-internal recursive subproofs. Their source constructor
        // children (including anonymous functions) have already been walked
        // above and own any lexical scopes required by Lean rendering. The
        // legacy backend certificate has no faithful premise-role vocabulary
        // for interval bounds, reduction laws, or structure fields, so do not
        // manufacture a fake flattened scope for them.
        if matches!(
            binder,
            SuccessVerifyBinderObjectWellDefinedResult::Iteration(_)
                | SuccessVerifyBinderObjectWellDefinedResult::FiniteAggregate(_)
                | SuccessVerifyBinderObjectWellDefinedResult::Reduce(_)
                | SuccessVerifyBinderObjectWellDefinedResult::Structure(_)
        ) {
            return Ok(None);
        }
        let scope_id = self.allocate_scope_id();
        let mut scope_ambient_ids = ambient_scope_ids.to_vec();
        scope_ambient_ids.push(scope_id);
        let mut premises = Vec::new();
        let mut assumption_infers = SuccessInferResult::new();

        match binder {
            SuccessVerifyBinderObjectWellDefinedResult::SetBuilder(result) => {
                child_uses.push(self.walk_child(&result.parameter_carrier, ambient_scope_ids)?);
                self.add_premise(
                    &result.parameter,
                    &scope_ambient_ids,
                    &mut premises,
                    &mut assumption_infers,
                )?;
                for condition in &result.conditions {
                    self.walk_fact_result(&condition.well_definedness, &scope_ambient_ids)?;
                    let fact_id = condition.store.fact_id.ok_or_else(|| {
                        "set-builder condition store has no frozen FactId".to_string()
                    })?;
                    premises.push(WellDefinedBinderPremiseProof::new(
                        WellDefinedBinderPremiseRole::LocalCondition {
                            condition_index: condition.condition_index,
                        },
                        None,
                        fact_id,
                        condition.store.fact.clone(),
                    ));
                    assumption_infers.new_infer_result_inside(condition.store.infers.clone());
                }
            }
            SuccessVerifyBinderObjectWellDefinedResult::FunctionSet(result) => {
                for child in &result.parameter_carriers {
                    child_uses.push(self.walk_child(child, &scope_ambient_ids)?);
                }
                for premise in &result.parameters {
                    self.add_premise(
                        premise,
                        &scope_ambient_ids,
                        &mut premises,
                        &mut assumption_infers,
                    )?;
                }
                for premise in &result.domains {
                    self.add_premise(
                        premise,
                        &scope_ambient_ids,
                        &mut premises,
                        &mut assumption_infers,
                    )?;
                }
                child_uses.push(self.walk_child(&result.return_carrier, &scope_ambient_ids)?);
            }
            SuccessVerifyBinderObjectWellDefinedResult::AnonymousFunction(result) => {
                for child in &result.parameter_carriers {
                    child_uses.push(self.walk_child(child, &scope_ambient_ids)?);
                }
                for premise in &result.parameters {
                    self.add_premise(
                        premise,
                        &scope_ambient_ids,
                        &mut premises,
                        &mut assumption_infers,
                    )?;
                }
                for premise in &result.domains {
                    self.add_premise(
                        premise,
                        &scope_ambient_ids,
                        &mut premises,
                        &mut assumption_infers,
                    )?;
                }
                child_uses.push(self.walk_child(&result.return_carrier, &scope_ambient_ids)?);
                child_uses.push(self.walk_child(&result.body, &scope_ambient_ids)?);
                let requirement_fact_id = self.add_fact_evidence(
                    result.body_membership.verification.clone(),
                    &scope_ambient_ids,
                );
                fact_ids.push(requirement_fact_id);
                object_requirements.push(WellDefinedTargetRequirementProof::new(
                    result.body_membership.source_object.clone(),
                    result.body_membership.role,
                    requirement_fact_id,
                    result.body_membership.expected_proposition.clone(),
                ));
            }
            SuccessVerifyBinderObjectWellDefinedResult::Iteration(_)
            | SuccessVerifyBinderObjectWellDefinedResult::FiniteAggregate(_)
            | SuccessVerifyBinderObjectWellDefinedResult::Reduce(_)
            | SuccessVerifyBinderObjectWellDefinedResult::Structure(_) => {
                unreachable!("non-projectable binder families returned above")
            }
        }

        let scope = WellDefinedBinderScopeProof {
            id: scope_id,
            owner_object: owner_object.clone(),
            ambient_scope_ids: ambient_scope_ids.to_vec(),
            premises,
            assumption_infers,
        };
        self.certificate
            .binder_scopes
            .push(WellDefinednessBinderScopeEvidence {
                scope: scope.clone(),
            });
        Ok(Some(scope))
    }

    fn walk_object(
        &mut self,
        result: &Rc<SuccessVerifyObjWellDefinedResult>,
        ambient_scope_ids: &[WellDefinedBinderScopeId],
    ) -> Result<WellDefinedObjId, String> {
        let result_key = Rc::as_ptr(result) as usize;
        let scoped_result_key = (result_key, ambient_scope_ids.to_vec());
        if let Some(object_id) = self.object_ids_by_result.get(&scoped_result_key) {
            return Ok(*object_id);
        }
        match result.as_ref() {
            SuccessVerifyObjWellDefinedResult::Reuse(result) => {
                let object_id = self.walk_object(&result.source, ambient_scope_ids)?;
                self.record_source_use(&result.object, object_id);
                Ok(object_id)
            }
            SuccessVerifyObjWellDefinedResult::RecursiveReference(result) => {
                let object_id = self
                    .active_object_ids_by_key
                    .get(&result.ancestor_key)
                    .copied()
                    .ok_or_else(|| {
                        format!(
                            "recursive WD reference `{}` has no active ancestor",
                            result.object
                        )
                    })?;
                self.record_source_use(&result.object, object_id);
                Ok(object_id)
            }
            SuccessVerifyObjWellDefinedResult::Direct(result) => {
                let object_id = self.allocate_object_id();
                self.object_ids_by_result
                    .insert(scoped_result_key, object_id);
                self.active_object_ids_by_key
                    .insert(result.cache_key.object_key.clone(), object_id);

                let mut child_uses = Vec::new();
                for child in &result.steps.children {
                    child_uses.push(self.walk_child(child, ambient_scope_ids)?);
                }
                let mut fact_ids = Vec::new();
                for check in &result.steps.fact_checks {
                    fact_ids.push(
                        self.add_fact_evidence(check.verification.clone(), ambient_scope_ids),
                    );
                }
                let mut object_requirements = Vec::new();
                for requirement in &result.steps.target_requirements {
                    let fact_id =
                        self.add_fact_evidence(requirement.verification.clone(), ambient_scope_ids);
                    fact_ids.push(fact_id);
                    object_requirements.push(WellDefinedTargetRequirementProof::new(
                        requirement.source_object.clone(),
                        requirement.role,
                        fact_id,
                        requirement.expected_proposition.clone(),
                    ));
                }
                if result.steps.template_materialization.is_some() {
                    return Err(format!(
                        "Lean WD projection does not yet support template materialization `{}`",
                        result.object
                    ));
                }
                let owned_binder_scope = if let Some(binder) = &result.steps.binder {
                    self.walk_object_binder(
                        &result.object,
                        binder,
                        ambient_scope_ids,
                        &mut child_uses,
                        &mut fact_ids,
                        &mut object_requirements,
                    )?
                } else {
                    None
                };

                // Backend-level target requirements model function-call
                // application contracts. Constructor-local requirements for
                // arithmetic and other objects remain owned by that object's
                // recursive WD node and must not be reclassified as a call.
                if let Obj::FnObj(_) = &result.object {
                    if let Some(source_occurrence_id) = result.object.source_occurrence_id() {
                        for requirement in &object_requirements {
                            self.certificate.target_requirements.push(
                                WellDefinednessTargetRequirementEvidence::new(
                                    source_occurrence_id,
                                    object_id,
                                    WellDefinednessTargetRequirementPhase::Proof,
                                    requirement.role,
                                    requirement.fact_id,
                                    requirement.expected_proposition.clone(),
                                ),
                            );
                        }
                    }
                }
                self.certificate
                    .objects
                    .push(WellDefinednessObjectEvidence::new(
                        object_id,
                        result.object.clone(),
                        result.cache_key.function_contracts.clone(),
                        result.intrinsic_result_set.clone(),
                        child_uses,
                        fact_ids,
                        object_requirements,
                        ambient_scope_ids.to_vec(),
                        owned_binder_scope.as_ref().map(|scope| scope.id),
                    ));
                self.record_source_use(&result.object, object_id);
                self.active_object_ids_by_key
                    .remove(&result.cache_key.object_key);
                Ok(object_id)
            }
        }
    }
}
