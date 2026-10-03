//! Introduce typed parameters into the current top ExecEnv.
//!
//! Shared by `have` / `trust have` / `prop` / `forall` / … whenever a
//! `TypedParameterList` must become live identifiers with type facts.
//!
//! Pipeline (field order matches):
//! 1. param-type WD
//! 2. define identifiers + store type-membership facts
//! 3. auto-open one struct layer for each `&Struct` binding (optional)
//!
//! Callers that insert extra stages between WD and define (e.g. `have`'s
//! nonempty checks) should call the stages separately, then
//! `auto_open_struct_layers_for_typed_parameters`.

use crate::ast::fact::{
    AtomicFact, Fact, InFact, IsFiniteSetFact, IsNonemptySetFact, IsSetFact,
};
use crate::ast::obj::{Obj, StructAndFieldAccessObj};
use crate::ast::param::{ParamType, TypedParameterList};
use crate::ast::stmt::{
    HaveByReplacementAxiomStmt, HaveObjByExistFactsStmt, HaveObjEqualStmt,
    HaveObjInNonemptySetOrParamTypeStmt, TrustHaveStmt,
};
use crate::exec_env::SpecialProperty;
use crate::exec_env::StoredIdentifierDefinition;
use crate::execute::execute_fact_stmt::{
    ParamTypeWellDefinedProof, VerifyObjWellDefinedResult, VerifyState,
};
use crate::execute::execute_have_obj_in_nonempty_set_stmt::StoreHaveObjAndInferResult;
use crate::execute::release_one_struct_layer::{
    FailToReleaseOneStructLayer, ReleaseOneStructLayerProof,
};
use crate::runtime::{Runtime, RuntimeError, RuntimeResult};
use std::rc::Rc;

/// Shared stmt body for multi-name `have` / `trust have` (name attached at insert).
#[derive(Clone)]
pub enum SharedHaveDefinition {
    HaveObjInNonemptySetOrParamType(Rc<HaveObjInNonemptySetOrParamTypeStmt>),
    HaveObjEqual(Rc<HaveObjEqualStmt>),
    HaveObjByExistFacts(Rc<HaveObjByExistFactsStmt>),
    TrustHave(Rc<TrustHaveStmt>),
    HaveByReplacementAxiom(Rc<HaveByReplacementAxiomStmt>),
}

impl SharedHaveDefinition {
    fn with_name(&self, name: String) -> StoredIdentifierDefinition {
        match self {
            SharedHaveDefinition::HaveObjInNonemptySetOrParamType(stmt) => {
                StoredIdentifierDefinition::HaveObjInNonemptySetOrParamType((
                    name,
                    Rc::clone(stmt),
                ))
            }
            SharedHaveDefinition::HaveObjEqual(stmt) => {
                StoredIdentifierDefinition::HaveObjEqual((name, Rc::clone(stmt)))
            }
            SharedHaveDefinition::HaveObjByExistFacts(stmt) => {
                StoredIdentifierDefinition::HaveObjByExistFacts((name, Rc::clone(stmt)))
            }
            SharedHaveDefinition::TrustHave(stmt) => {
                StoredIdentifierDefinition::TrustHave((name, Rc::clone(stmt)))
            }
            SharedHaveDefinition::HaveByReplacementAxiom(stmt) => {
                StoredIdentifierDefinition::HaveByReplacementAxiom((name, Rc::clone(stmt)))
            }
        }
    }
}

pub enum IntroduceTypedParametersFailed {
    ParamType(VerifyObjWellDefinedResult),
    AutoOpenStructLayer {
        param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
        defined_params: StoreHaveObjAndInferResult,
        opened_before_fail: Vec<ReleaseOneStructLayerProof>,
        failed: FailToReleaseOneStructLayer,
    },
}

// Stage-ordered evidence for introducing a TypedParameterList.
pub struct IntroduceTypedParametersResult {
    pub param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
    pub defined_params: StoreHaveObjAndInferResult,
    /// `None` when no param had a `&Struct` carrier; otherwise one proof per such binding.
    pub auto_opened_struct_layers: Option<Vec<ReleaseOneStructLayerProof>>,
}

impl Runtime {
    // Introduce groups in source order: WD each group's type, then define that
    // group, then the next. Later groups may mention earlier params
    // (`template<S set, z S>` / `forall S set, x S:`). That dependence is for
    // binder *kinds* / typed headers, not for FnSet obj carriers (those must be
    // fixed sets; see set_bound_param_type_cites_earlier_binder).
    // After all groups: auto-open `&Struct` layers.
    // Soft miss: Ok(Err(...)); operational / internal bug: Err(...).
    pub fn introduce_typed_parameters(
        &mut self,
        typed_parameters: &TypedParameterList,
        verify_state: VerifyState,
    ) -> RuntimeResult<Result<IntroduceTypedParametersResult, IntroduceTypedParametersFailed>> {
        self.introduce_typed_parameters_with_definition(typed_parameters, verify_state, None)
    }

    pub(in crate::execute) fn introduce_typed_parameters_with_definition(
        &mut self,
        typed_parameters: &TypedParameterList,
        verify_state: VerifyState,
        shared_have: Option<SharedHaveDefinition>,
    ) -> RuntimeResult<Result<IntroduceTypedParametersResult, IntroduceTypedParametersFailed>> {
        let mut param_type_well_defined = Vec::new();
        let mut stored_fact_ids = Vec::new();
        for group in &typed_parameters.groups {
            let one = TypedParameterList {
                groups: vec![group.clone()],
            };
            let proof = self
                .verify_param_type_well_definedness(&group.param_type, verify_state.clone())?;
            if proof.is_failed() {
                let failed = match proof {
                    ParamTypeWellDefinedProof::Obj(wd) => wd,
                    ParamTypeWellDefinedProof::Set
                    | ParamTypeWellDefinedProof::NonemptySet
                    | ParamTypeWellDefinedProof::FiniteSet => unreachable!(
                        "kind param types never soft-fail well-definedness"
                    ),
                };
                return Ok(Err(IntroduceTypedParametersFailed::ParamType(failed)));
            }
            param_type_well_defined.push(proof);
            let defined = self.define_typed_parameters_in_current_env(&one, shared_have.clone(), verify_state)?;
            stored_fact_ids.extend(defined.stored_fact_ids);
        }

        let defined_params = StoreHaveObjAndInferResult { stored_fact_ids };
        let auto_opened_struct_layers =
            match self.auto_open_struct_layers_for_typed_parameters(typed_parameters, verify_state)? {
                Ok(layers) => layers,
                Err((opened_before_fail, failed)) => {
                    return Ok(Err(IntroduceTypedParametersFailed::AutoOpenStructLayer {
                        param_type_well_defined,
                        defined_params,
                        opened_before_fail,
                        failed,
                    }));
                }
            };

        Ok(Ok(IntroduceTypedParametersResult {
            param_type_well_defined,
            defined_params,
            auto_opened_struct_layers,
        }))
    }

    // Stage 1 only: soft-fail when any ParamType WD fails.
    pub fn verify_typed_parameters_well_definedness_or_fail(
        &mut self,
        typed_parameters: &TypedParameterList,
        verify_state: VerifyState,
    ) -> RuntimeResult<Result<Vec<ParamTypeWellDefinedProof>, VerifyObjWellDefinedResult>> {
        let param_type_well_defined =
            self.verify_typed_parameters_well_definedness(typed_parameters, verify_state)?;
        let mut kept = Vec::with_capacity(param_type_well_defined.len());
        for proof in param_type_well_defined {
            if proof.is_failed() {
                let failed = match proof {
                    ParamTypeWellDefinedProof::Obj(wd) => wd,
                    ParamTypeWellDefinedProof::Set
                    | ParamTypeWellDefinedProof::NonemptySet
                    | ParamTypeWellDefinedProof::FiniteSet => unreachable!(
                        "kind param types never soft-fail well-definedness"
                    ),
                };
                return Ok(Err(failed));
            }
            kept.push(proof);
        }
        Ok(Ok(kept))
    }

    // Stage 2: bind each identifier and store its type fact into KnownFactMemory.
    // Example: `have x R` stores `x $in R`.
    //
    // Duplicate check is top-env only so a nested WD/witness local may bind
    // `k` when an ambient `obtain k` already owns that surface name in a parent.
    // Callers that forbid parent clashes (`have` / `let` / …) check the stack
    // themselves before calling.
    //
    // `shared_have`:
    // - `None` → each name is a scoped `ParamType` binder
    // - `Some(...)` → every name gets that have/trust-have stmt with its own name
    pub fn define_typed_parameters_in_current_env(
        &mut self,
        typed_parameters: &TypedParameterList,
        shared_have: Option<SharedHaveDefinition>,
     verify_state: crate::execute::execute_fact_stmt::VerifyState) -> RuntimeResult<StoreHaveObjAndInferResult> {
        let mut stored_fact_ids = Vec::new();
        for group in &typed_parameters.groups {
            for identifier in &group.params {
                if self
                    .top_exec_env()
                    .definitions
                    .identifiers
                    .contains_key(&identifier.name)
                {
                    return Err(RuntimeError::InternalBug(format!(
                        "identifier `{}` is already defined in this ExecEnv",
                        identifier.name
                    )));
                }
                let definition = match &shared_have {
                    Some(shared) => shared.with_name(identifier.name.clone()),
                    None => StoredIdentifierDefinition::ParamType((
                        identifier.clone(),
                        group.param_type.clone(),
                    )),
                };
                self.top_exec_env_mut()
                    .definitions
                    .identifiers
                    .insert(identifier.name.clone(), definition);
                // Env key is plain; type-fact mention qualifies at file root.
                let element = Obj::Identifier(self.identifier_obj_for_stored_mention(identifier));
                let type_fact = match &group.param_type {
                    ParamType::Obj(param_set) => {
                        let fact_id = self.global_ids.allocate_fact_id();
                        let membership = Fact::AtomicFact(AtomicFact::InFact(InFact {
                            fact_id,
                            element: element.clone(),
                            set: param_set.clone(),
                            line_file: None,
                        }));
                        if let Fact::AtomicFact(AtomicFact::InFact(in_fact)) = &membership {
                            self.record_default_struct_view(in_fact);
                        }
                        membership
                    }
                    ParamType::Set(_) => Fact::AtomicFact(AtomicFact::IsSetFact(IsSetFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        set: element,
                        line_file: None,
                    })),
                    ParamType::NonemptySet(_) => {
                        Fact::AtomicFact(AtomicFact::IsNonemptySetFact(IsNonemptySetFact {
                            fact_id: self.global_ids.allocate_fact_id(),
                            set: element,
                            line_file: None,
                        }))
                    }
                    ParamType::FiniteSet(_) => {
                        Fact::AtomicFact(AtomicFact::IsFiniteSetFact(IsFiniteSetFact {
                            fact_id: self.global_ids.allocate_fact_id(),
                            set: element,
                            line_file: None,
                        }))
                    }
                };
                let store_result = self.store_fact_and_infer(&type_fact, verify_state)?;
                stored_fact_ids.extend(store_result.stored_fact_ids());
            }
        }
        Ok(StoreHaveObjAndInferResult { stored_fact_ids })
    }

    // A typed definition selects the default field view; an ordinary membership does not.
    pub(crate) fn record_default_struct_view(&mut self, fact: &InFact) {
        if matches!(&fact.set, Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(_))) {
            self.top_exec_env_mut().record_special_property(
                fact.element.ir(),
                SpecialProperty::DefaultStructView(fact.clone()),
            );
        }
    }
}
