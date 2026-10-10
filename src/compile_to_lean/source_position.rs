use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{SetBuilderObjWellDefinedProof, SetFormerObjWellDefinedProofByDef};
use super::helper::verified_subject;
use super::LeanCompileError;
use crate::execute::execute_by_stmt::{ExecByDefStmtResult, ExecByDefStmtSuccess};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::UserDefinedPropDefinitionProof;
use crate::execute::{ExecHaveFnEqualStmtResult, ExecHaveFnEqualStmtSuccessResult};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::normalize_function_body::{FunctionBodyNormalizationProof, AnonymousFunctionBodyExpansionProof, FunctionBodyExpansionProof};
use crate::execute::{ExecDefPropStmtResult, ExecDefPropStmtSuccessResult};
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicExceptEqualityResult, InferAtomicFactResult, InferFactResult,
};

/// A borrowed position in the original execution evidence, not a replay registry.
#[derive(Clone, Copy)]
pub(super) struct SourcePosition<'a> {
    pub parent: Option<&'a SourcePosition<'a>>,
    pub owner: SourceOwner<'a>,
    pub before: usize,
}

// Run: completed statements. Headers: params, dom assumptions, then/body stages.
// WD/AtomicWD: child WD, then requirements. Call: types, doms, conclusion WD,
// then returned stores. HaveEqual: RHS WD, membership checks, alias definitions.
#[derive(Clone, Copy)]
pub(super) enum SourceOwner<'a> {
    Run(&'a RunLitexCodeResult),
    Statement(&'a ExecStmtResult),
    Verify(&'a VerifyFactResult),
    WD(&'a ObjWellDefinedProof),
    SetBuilder(&'a SetBuilder, &'a SetBuilderObjWellDefinedProof),
    Named(&'a ExecDefThmStmtSuccess),
    Forall(&'a VerifyForallFactSuccess),
    EmptyForall(&'a crate::execute::execute_fact_stmt::verify_forall_fact::VerifyEmptyParameterDomainForallProof),
    ForallWD(&'a ForallFact, &'a ForallFactWellDefinedProof),
    KnownForall(&'a VerifyKnownForallFactProof),
    Call(&'a ExecByThmStmtSuccess),
    HaveEqualType(&'a ExecHaveObjEqualStmtSuccessResult),
    AtomicWD(&'a AtomicFactWellDefinedProof),
    FactWD(&'a FactWellDefinedProof),
    HaveGroup(&'a ParamTypeWellDefinedProof, &'a ParamTypeFactCheckResult),
    ParamTypeWD(&'a ParamTypeWellDefinedProof),
    PropDefinition(&'a ExecDefPropStmtSuccessResult),
    ByDef(&'a ExecByDefStmtSuccess),
    PropRequirements(&'a UserDefinedPropDefinitionProof),
    PropInference(&'a StoreFactAndInferResult),
    FunctionNormalization(&'a FunctionBodyNormalizationProof),
    FunctionExpansion(&'a AnonymousFunctionBodyExpansionProof),
    FunctionDefinitionRewrite(&'a [AnonymousFunctionBodyExpansionProof]),
}

impl<'a> SourcePosition<'a> {
    pub fn new(parent: Option<&'a Self>, owner: SourceOwner<'a>, before: usize) -> Self {
        Self {
            parent,
            owner,
            before,
        }
    }

    /// Only already completed top-level ordinary-have introductions are arguments.
    pub fn context_parameters(&self) -> Vec<(&'a BoundName, Option<&'a Obj>, FactId)> {
        let mut parameters = Vec::new();
        let mut position = Some(self);
        while let Some(current) = position {
            if let SourceOwner::Run(run) = current.owner {
                for statement in run.statement_results.iter().take(current.before) {
                    if let Some(proof) = ordinary_have(statement) {
                        append_have_parameters(proof, usize::MAX, &mut parameters);
                    }
                }
                break;
            }
            position = current.parent;
        }
        let mut position = Some(self);
        while let Some(current) = position {
            if let SourceOwner::Statement(statement) = current.owner {
                if current
                    .parent
                    .map(|p| matches!(p.owner, SourceOwner::Run(_)))
                    .unwrap_or(false)
                {
                    if let Some(proof) = ordinary_have(statement) {
                        append_have_parameters(proof, current.before, &mut parameters);
                    }
                }
            }
            position = current.parent;
        }
        parameters
    }

    pub fn context_arguments(&self) -> String {
        self.context_parameters()
            .iter()
            .flat_map(|(p, _, fact_id)| {
                let id = p.id.value();
                [
                    format!("_Host_i{id}"),
                    format!("_rep_i{id}"),
                    format!("_value_i{id}"),
                    format!("h_{}", fact_id.value()),
                ]
            })
            .collect::<Vec<_>>()
            .join(" ")
    }

    pub fn is_local(&self) -> bool {
        let mut position = Some(self);
        while let Some(current) = position {
            match current.owner {
                SourceOwner::Named(_)
                | SourceOwner::Forall(_)
                | SourceOwner::EmptyForall(_)
                | SourceOwner::ForallWD(_, _)
                | SourceOwner::KnownForall(_)
                | SourceOwner::Call(_)
                | SourceOwner::HaveEqualType(_) => return true,
                SourceOwner::PropDefinition(_)
                | SourceOwner::ByDef(_)
                | SourceOwner::SetBuilder(_, _) => return true,
                SourceOwner::WD(proof) if function_binder(proof).is_some() => return true,
                _ => {}
            }
            position = current.parent;
        }
        false
    }

    pub fn visible_theorem(
        &self,
        name: &str,
    ) -> Result<(&'a DefThmStmt, Self, usize), LeanCompileError> {
        let mut position = Some(self);
        while let Some(current) = position {
            if let SourceOwner::Run(run) = current.owner {
                for (index, statement) in run
                    .statement_results
                    .iter()
                    .take(current.before)
                    .enumerate()
                    .rev()
                {
                    if let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
                        ExecDefThmStmtResult::Success(p),
                    )) = statement
                    {
                        if p.statement.name == name {
                            return Ok((
                                &p.statement,
                                Self::new(None, SourceOwner::Run(run), index),
                                index,
                            ));
                        }
                    }
                }
            }
            position = current.parent;
        }
        Err(LeanCompileError::new(
            "ByThm/Producer",
            "The named theorem has no prior declaration in the active source results.",
        ))
    }

    pub fn visible_prop(
        &self,
        predicate: &AtomicName,
    ) -> Result<(&'a ExecDefPropStmtSuccessResult, Self, usize), LeanCompileError> {
        let AtomicName::Plain { name } = predicate else {
            return Err(LeanCompileError::unsupported("Prop/QualifiedDeclaration"));
        };
        let mut position = Some(self);
        while let Some(current) = position {
            if let SourceOwner::Run(run) = current.owner {
                for (index, statement) in run
                    .statement_results
                    .iter()
                    .take(current.before)
                    .enumerate()
                    .rev()
                {
                    if let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
                        ExecDefPropStmtResult::Success(proof),
                    )) = statement
                    {
                        if &proof.statement.name == name {
                            return Ok((
                                proof,
                                Self::new(None, SourceOwner::Run(run), index),
                                index,
                            ));
                        }
                    }
                }
            }
            position = current.parent;
        }
        Err(LeanCompileError::new(
            "Prop/Producer",
            "The predicate has no preceding concrete definition in the original results.",
        ))
    }

    pub fn visible_function(
        &self,
        id: &IdentifierId,
    ) -> Result<(&'a ExecHaveFnEqualStmtSuccessResult, Self, usize), LeanCompileError> {
        let mut position = Some(self);
        while let Some(current) = position {
            match current.owner {
                SourceOwner::Run(run) => {
                    for (index, statement) in run
                        .statement_results
                        .iter()
                        .take(current.before)
                        .enumerate()
                        .rev()
                    {
                        if let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
                            ExecHaveFnEqualStmtResult::Success(proof),
                        )) = statement
                        {
                            if &proof.statement.name.id == id {
                                return Ok((
                                    proof,
                                    Self::new(None, SourceOwner::Run(run), index),
                                    index,
                                ));
                            }
                        }
                    }
                }
                SourceOwner::Statement(ExecStmtResult::Definition(
                    ExecDefinitionStmtResult::HaveFnEqual(ExecHaveFnEqualStmtResult::Success(
                        proof,
                    )),
                )) if current.before >= 2 && &proof.statement.name.id == id => {
                    if let Some(parent) = current.parent {
                        return Ok((proof, *parent, parent.before));
                    }
                }
                _ => {}
            }
            position = current.parent;
        }
        Err(LeanCompileError::new(
            "Function/Producer",
            "The function has no preceding definition in the original result prefix.",
        ))
    }

    pub fn source_fact(
        &self,
        id: FactId,
        runtime: &'a Runtime,
    ) -> Result<&'a Fact, LeanCompileError> {
        let mut position = Some(self);
        while let Some(current) = position {
            let env = match current.owner {
                SourceOwner::Named(p) => Some(p.local_env.as_ref()),
                SourceOwner::Forall(p) => Some(p.local_env.as_ref()),
                SourceOwner::EmptyForall(p) => Some(p.local_env.as_ref()),
                SourceOwner::ForallWD(_, p) => Some(p.local_env.as_ref()),
                SourceOwner::KnownForall(p) => Some(p.well_defined.local_env.as_ref()),
                SourceOwner::Call(p) => Some(p.local_env.as_ref()),
                SourceOwner::HaveEqualType(p) => Some(p.type_local_env.as_ref()),
                SourceOwner::PropDefinition(p) => Some(p.local_env.as_ref()),
                SourceOwner::ByDef(p) => Some(p.local_env.as_ref()),
                SourceOwner::SetBuilder(_, p) => Some(p.local_env.as_ref()),
                SourceOwner::WD(p) => function_binder(p).map(|(_, _, _, _, env)| env),
                _ => None,
            };
            if let Some(fact) = env.and_then(|env| env.facts.facts_by_id.get(&id)) {
                return Ok(fact);
            }
            position = current.parent;
        }
        runtime.fact_by_id_in_stack(id).ok_or_else(|| {
            LeanCompileError::new(
                "FactId/Resolution",
                "The cited fact is absent from the live scope context.",
            )
        })
    }

    pub fn source_wd(
        &self,
        id: WellDefinednessId,
        runtime: &'a Runtime,
    ) -> Result<&'a Obj, LeanCompileError> {
        let mut position = Some(self);
        while let Some(current) = position {
            let env = match current.owner {
                SourceOwner::Named(p) => Some(p.local_env.as_ref()),
                SourceOwner::Forall(p) => Some(p.local_env.as_ref()),
                SourceOwner::EmptyForall(p) => Some(p.local_env.as_ref()),
                SourceOwner::ForallWD(_, p) => Some(p.local_env.as_ref()),
                SourceOwner::KnownForall(p) => Some(p.well_defined.local_env.as_ref()),
                SourceOwner::Call(p) => Some(p.local_env.as_ref()),
                SourceOwner::HaveEqualType(p) => Some(p.type_local_env.as_ref()),
                SourceOwner::PropDefinition(p) => Some(p.local_env.as_ref()),
                SourceOwner::ByDef(p) => Some(p.local_env.as_ref()),
                SourceOwner::SetBuilder(_, p) => Some(p.local_env.as_ref()),
                SourceOwner::WD(p) => function_binder(p).map(|(_, _, _, _, env)| env),
                _ => None,
            };
            if let Some(object) =
                env.and_then(|env| env.well_defined_objects.wd_id_to_object.get(&id))
            {
                return Ok(object);
            }
            position = current.parent;
        }
        for env in runtime.execution_environments_stack.iter().rev() {
            if let Some(object) = env.well_defined_objects.wd_id_to_object.get(&id) {
                return Ok(object);
            }
        }
        Err(LeanCompileError::new(
            "WdId/Resolution",
            "The cited WD record is absent from the live scope context.",
        ))
    }

    /// Env resolution identifies a subject; the result prefix identifies its producer.
    pub fn visible_fact(
        &self,
        id: FactId,
        runtime: &'a Runtime,
    ) -> Result<(&'a Fact, String), LeanCompileError> {
        let actual = self.source_fact(id, runtime)?;
        let mut ceiling = Some(self);
        while let Some(current) = ceiling {
            if let SourceOwner::PropInference(store) = current.owner {
                if prop_inference_stages(store)
                    .iter()
                    .skip(current.before)
                    .any(|stage| stage.store_and_infer.stored_fact_ids().contains(&id))
                {
                    return Err(LeanCompileError::new(
                        "Inference/FutureProducer",
                        "The cited inference has not occurred at this captured formation stage.",
                    ));
                }
            }
            ceiling = current.parent;
        }
        let mut position = Some(self);
        while let Some(current) = position {
            if let Some(reference) = fact_reference_in_owner(current, id, actual)? {
                return Ok((actual, reference));
            }
            position = current.parent;
        }
        Err(LeanCompileError::new(
            "FactId/Producer",
            &format!(
                "FactId {} has no prior producer in the active source results.",
                id.value()
            ),
        ))
    }

    pub fn visible_parameter(
        &self,
        id: IdentifierId,
        runtime: &'a Runtime,
    ) -> Result<(&'a BoundName, Option<&'a Obj>, FactId, String), LeanCompileError> {
        let mut position = Some(self);
        while let Some(current) = position {
            if let Some((name, carrier, store)) = parameter_in_owner(current, id) {
                let fact_id = store.primary_fact_id();
                let fact = self.source_fact(fact_id, runtime)?;
                let object = Obj::Identifier(IdentifierObj::from_bound_name(name));
                match (fact, carrier) {
                    (Fact::AtomicFact(AtomicFact::InFact(f)), Some(carrier))
                        if f.element.ir() == object.ir() && f.set.ir() == carrier.ir() => {}
                    (Fact::AtomicFact(AtomicFact::IsSetFact(f)), None)
                        if f.set.ir() == object.ir() => {}
                    _ => {
                        return Err(LeanCompileError::new(
                            "Parameters/Subject",
                            "The actual parameter store differs from its source header.",
                        ))
                    }
                }
                check_store_subject(store, fact)?;
                return Ok((name, carrier, fact_id, format!("h_{}", fact_id.value())));
            }
            position = current.parent;
        }
        Err(LeanCompileError::new(
            "Identifier/Producer",
            "The identifier has no introduction in the active source results.",
        ))
    }

    pub fn with_visible_wd<T>(
        &self,
        object: &Obj,
        callback: &mut impl FnMut(
            &ObjWellDefinedProof,
            &SourcePosition<'_>,
        ) -> Result<T, LeanCompileError>,
    ) -> Result<Option<T>, LeanCompileError> {
        visit_visible(
            self,
            &mut |proof, position| {
                if matches!(proof, ObjWellDefinedProof::ByDef { obj, .. } if obj.ir() == object.ir())
                {
                    callback(proof, position).map(Some)
                } else {
                    Ok(None)
                }
            },
            &mut |_, _| Ok(None),
        )
    }

    pub fn with_visible_membership<T>(
        &self,
        object: &Obj,
        set: &Obj,
        callback: &mut impl FnMut(&VerifyFactResult, &SourcePosition<'_>) -> Result<T, LeanCompileError>,
    ) -> Result<Option<T>, LeanCompileError> {
        visit_visible(
            self,
            &mut |_, _| Ok(None),
            &mut |proof, position| match verified_subject(proof) {
                Some(Fact::AtomicFact(AtomicFact::InFact(f)))
                    if f.element.ir() == object.ir() && f.set.ir() == set.ir() =>
                {
                    callback(proof, position).map(Some)
                }
                _ => Ok(None),
            },
        )
    }

    pub fn with_visible_alias<T>(
        &self,
        object: &Obj,
        callback: &mut impl FnMut(
            &BoundName,
            &Obj,
            &VerifyObjWellDefinedResult,
            &SourcePosition<'_>,
        ) -> Result<T, LeanCompileError>,
    ) -> Result<Option<T>, LeanCompileError> {
        let mut position = Some(self);
        while let Some(current) = position {
            match current.owner {
                SourceOwner::Run(run) => {
                    for (index, statement) in run
                        .statement_results
                        .iter()
                        .take(current.before)
                        .enumerate()
                        .rev()
                    {
                        let prior = SourcePosition::new(None, SourceOwner::Run(run), index);
                        if let Some(value) =
                            alias_in_statement(statement, object, usize::MAX, &prior, callback)?
                        {
                            return Ok(Some(value));
                        }
                    }
                }
                SourceOwner::Statement(statement) => {
                    if let Some(parent) = current.parent {
                        if let Some(value) =
                            alias_in_statement(statement, object, current.before, parent, callback)?
                        {
                            return Ok(Some(value));
                        }
                    }
                }
                SourceOwner::Named(proof) => {
                    let (steps, head) = named_steps(proof);
                    for (index, statement) in steps
                        .iter()
                        .take(current.before.saturating_sub(head))
                        .enumerate()
                        .rev()
                    {
                        let prior = SourcePosition {
                            before: head + index,
                            ..*current
                        };
                        if let Some(value) =
                            alias_in_statement(statement, object, usize::MAX, &prior, callback)?
                        {
                            return Ok(Some(value));
                        }
                    }
                }
                _ => {}
            }
            position = current.parent;
        }
        Ok(None)
    }

    pub fn has_visible_inferred_natural_zero(&self) -> bool {
        let mut position = Some(self);
        while let Some(current) = position {
            let found = match current.owner {
                SourceOwner::Run(run) => {
                    run.statement_results
                        .iter()
                        .take(current.before)
                        .any(|stmt| {
                            ordinary_have(stmt)
                                .map(|p| have_has_natural_zero(p, usize::MAX))
                                .unwrap_or(false)
                        })
                }
                SourceOwner::Statement(stmt) => ordinary_have(stmt)
                    .map(|p| have_has_natural_zero(p, current.before))
                    .unwrap_or(false),
                SourceOwner::Forall(p) => {
                    introduction_has_natural_zero(&p.introduced_params, current.before)
                }
                SourceOwner::ForallWD(_, p) => {
                    introduction_has_natural_zero(&p.introduced_params, current.before)
                }
                SourceOwner::KnownForall(p) => {
                    introduction_has_natural_zero(&p.well_defined.introduced_params, current.before)
                }
                SourceOwner::Named(p) => match &p.body {
                    ExecDefThmBodyProof::Forall(b) => {
                        introduction_has_natural_zero(&b.introduced_params, current.before)
                    }
                    _ => false,
                },
                _ => false,
            };
            if found {
                return true;
            }
            position = current.parent;
        }
        false
    }
}

fn append_have_parameters<'a>(
    proof: &'a ExecHaveObjInNonemptySetStmtSuccessResult,
    before: usize,
    out: &mut Vec<(&'a BoundName, Option<&'a Obj>, FactId)>,
) {
    let mut index = 0;
    for group in &proof.statement.param_def.groups {
        for parameter in &group.params {
            if index >= before {
                return;
            }
            let carrier = match &group.param_type {
                ParamType::Obj(carrier) => Some(carrier),
                ParamType::Set(_) => None,
                _ => {
                    index += 1;
                    continue;
                }
            };
            if let Some(store) = proof
                .store_and_infer_result
                .store_and_infer_results
                .get(index)
            {
                out.push((parameter, carrier, store.primary_fact_id()));
            }
            index += 1;
        }
    }
}

fn context_arguments_before(run: &RunLitexCodeResult, before: usize) -> Vec<String> {
    let mut arguments = Vec::new();
    for statement in run.statement_results.iter().take(before) {
        if let Some(proof) = ordinary_have(statement) {
            let mut parameters = Vec::new();
            append_have_parameters(proof, usize::MAX, &mut parameters);
            for (parameter, _, fact_id) in parameters {
                let id = parameter.id.value();
                arguments.extend([
                    format!("_Host_i{id}"),
                    format!("_rep_i{id}"),
                    format!("_value_i{id}"),
                    format!("h_{}", fact_id.value()),
                ]);
            }
        }
    }
    arguments
}

fn application(name: &str, arguments: &[String]) -> String {
    if arguments.is_empty() {
        format!("({name} (M := M))")
    } else {
        let arguments = arguments
            .chunks_exact(4)
            .map(|group| {
                format!(
                    "({} := {}) ({} := {}) {} {}",
                    group[0], group[0], group[1], group[1], group[2], group[3]
                )
            })
            .collect::<Vec<_>>()
            .join(" ");
        format!("({name} (M := M) {arguments})")
    }
}

fn ordinary_have(statement: &ExecStmtResult) -> Option<&ExecHaveObjInNonemptySetStmtSuccessResult> {
    match statement {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjInNonemptySet(
                ExecHaveObjInNonemptySetStmtResult::Success(p),
            ),
        )) => Some(p),
        _ => None,
    }
}

fn parameter_from_groups<'a>(
    groups: &'a [TypedParameterGroup],
    stores: &'a [std::rc::Rc<StoreFactAndInferResult>],
    before: usize,
    id: IdentifierId,
) -> Option<(&'a BoundName, Option<&'a Obj>, &'a StoreFactAndInferResult)> {
    let mut index = 0;
    for group in groups {
        for parameter in &group.params {
            if index < before && parameter.id == id {
                let carrier = match &group.param_type {
                    ParamType::Obj(carrier) => Some(carrier),
                    ParamType::Set(_) => None,
                    _ => return None,
                };
                return stores
                    .get(index)
                    .map(|store| (parameter, carrier, store.as_ref()));
            }
            index += 1;
        }
    }
    None
}

fn parameter_in_owner<'a>(
    position: &SourcePosition<'a>,
    id: IdentifierId,
) -> Option<(&'a BoundName, Option<&'a Obj>, &'a StoreFactAndInferResult)> {
    match position.owner {
        SourceOwner::Forall(p) => parameter_from_groups(
            &p.fact.typed_parameters.groups,
            &p.introduced_params.defined_params.store_and_infer_results,
            position.before,
            id,
        ),
        SourceOwner::ForallWD(fact, p) => parameter_from_groups(
            &fact.typed_parameters.groups,
            &p.introduced_params.defined_params.store_and_infer_results,
            position.before,
            id,
        ),
        SourceOwner::KnownForall(p) => parameter_from_groups(
            &p.fact.typed_parameters.groups,
            &p.well_defined
                .introduced_params
                .defined_params
                .store_and_infer_results,
            position.before,
            id,
        ),
        SourceOwner::PropDefinition(p) => parameter_from_groups(
            &p.statement.typed_parameters.groups,
            &p.defined_params.store_and_infer_results,
            position.before,
            id,
        ),
        SourceOwner::SetBuilder(set, proof)
            if position.before > 1 && set.param_binding.id == id =>
        {
            proof
                .defined_params
                .store_and_infer_results
                .first()
                .map(|store| {
                    (
                        &set.param_binding,
                        Some(set.param_set.as_ref()),
                        store.as_ref(),
                    )
                })
        }
        SourceOwner::WD(proof) => {
            let (signature, carriers, parameters, _, _) = function_binder(proof)?;
            let before = position.before.saturating_sub(carriers.len());
            let mut index = 0;
            for group in &signature.set_bound_parameters.groups {
                for parameter in &group.params {
                    if index < before && parameter.id == id {
                        return parameters.store_and_infer_results.get(index).map(|store| {
                            (parameter, Some(group.param_type.as_ref()), store.as_ref())
                        });
                    }
                    index += 1;
                }
            }
            None
        }
        SourceOwner::Named(p) => match (&p.statement.fact, &p.body) {
            (Fact::ForallFact(fact), ExecDefThmBodyProof::Forall(body)) => parameter_from_groups(
                &fact.typed_parameters.groups,
                &body
                    .introduced_params
                    .defined_params
                    .store_and_infer_results,
                position.before,
                id,
            ),
            _ => None,
        },
        SourceOwner::Statement(statement) => ordinary_have(statement).and_then(|p| {
            parameter_from_groups(
                &p.statement.param_def.groups,
                &p.store_and_infer_result.store_and_infer_results,
                position.before,
                id,
            )
        }),
        SourceOwner::Run(run) => run
            .statement_results
            .iter()
            .take(position.before)
            .rev()
            .find_map(|statement| {
                ordinary_have(statement).and_then(|p| {
                    parameter_from_groups(
                        &p.statement.param_def.groups,
                        &p.store_and_infer_result.store_and_infer_results,
                        usize::MAX,
                        id,
                    )
                })
            }),
        _ => None,
    }
}

fn function_binder(
    proof: &ObjWellDefinedProof,
) -> Option<(
    &FnSet,
    &[Box<ObjWellDefinedProof>],
    &StoreHaveObjAndInferResult,
    &[AssumeDomFactResult],
    &crate::exec_env::ExecEnv,
)> {
    match proof {
        ObjWellDefinedProof::ByDef {
            obj: Obj::FunctionSpace(FunctionSpace::FnSet(signature)),
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::FnSet(
                    proof,
                )),
        } => Some((
            signature,
            &proof.param_type_well_defined,
            &proof.defined_params,
            &proof.assumed_dom_facts,
            &proof.local_env,
        )),
        ObjWellDefinedProof::ByDef {
            obj: Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)),
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(
                    FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(proof),
                ),
        } => Some((
            &function.body,
            &proof.param_type_well_defined,
            &proof.defined_params,
            &proof.assumed_dom_facts,
            &proof.local_env,
        )),
        _ => None,
    }
}

fn check_subject(expected: &Fact, actual: &Fact) -> Result<(), LeanCompileError> {
    if expected == actual {
        Ok(())
    } else {
        Err(LeanCompileError::new(
            "FactId/Producer",
            "The result producer differs from the exact cited source subject.",
        ))
    }
}

fn check_store_subject(
    store: &StoreFactAndInferResult,
    actual: &Fact,
) -> Result<(), LeanCompileError> {
    let expected = match &store.store {
        StoreFactResult::AtomicFact(p) => Fact::AtomicFact(p.fact.clone()),
        StoreFactResult::ForallFact(p) => Fact::ForallFact(p.fact.clone()),
        _ => return Err(LeanCompileError::unsupported("Store/Compound")),
    };
    if store.primary_fact_id() != actual.fact_id() {
        return Err(LeanCompileError::new(
            "Store/Subject",
            "The producer store ID differs from its subject.",
        ));
    }
    check_subject(&expected, actual)
}

fn infer_has_fact(
    store: &StoreFactAndInferResult,
    id: FactId,
    actual: &Fact,
) -> Result<bool, LeanCompileError> {
    if let InferFactResult::AtomicFact(InferAtomicFactResult::ExceptEquality(rules)) = &store.infer
    {
        for rule in rules {
            let derived = match rule {
                InferAtomicExceptEqualityResult::NormalAtomicParamTypes(p) => {
                    Some(p.derived.iter().collect::<Vec<_>>())
                }
                InferAtomicExceptEqualityResult::NormalAtomicExpandDefinition(p) => {
                    Some(p.derived.iter().collect::<Vec<_>>())
                }
                InferAtomicExceptEqualityResult::InFactSetBuilder(p) => Some(
                    p.steps
                        .iter()
                        .flat_map(|step| &step.derived)
                        .collect::<Vec<_>>(),
                ),
                _ => None,
            };
            if let Some(derived) = derived {
                for derived in derived {
                    let store = &derived.store_and_infer;
                    if store.primary_fact_id() == id {
                        check_store_subject(store, actual)?;
                        return Ok(true);
                    }
                    if infer_has_fact(store, id, actual)? {
                        return Ok(true);
                    }
                }
            }
            if let InferAtomicExceptEqualityResult::InFactSignedStandardSetSign(p) = rule {
                for derived in &p.derived {
                    if derived.primary_fact_id() == id {
                        check_store_subject(derived, actual)?;
                        return Ok(true);
                    }
                }
            }
        }
    }
    Ok(false)
}

fn prop_inference_stages(
    store: &StoreFactAndInferResult,
) -> Vec<&crate::store_fact_and_infer::StoreInferredFactAndInferResult> {
    let InferFactResult::AtomicFact(InferAtomicFactResult::ExceptEquality(rules)) = &store.infer
    else {
        return Vec::new();
    };
    rules
        .iter()
        .flat_map(|rule| match rule {
            InferAtomicExceptEqualityResult::NormalAtomicParamTypes(p) => {
                p.derived.iter().collect::<Vec<_>>()
            }
            InferAtomicExceptEqualityResult::NormalAtomicExpandDefinition(p) => {
                p.derived.iter().collect::<Vec<_>>()
            }
            InferAtomicExceptEqualityResult::InFactSetBuilder(p) => p
                .steps
                .iter()
                .flat_map(|step| &step.derived)
                .collect::<Vec<_>>(),
            _ => Vec::new(),
        })
        .collect()
}

fn have_reference(
    proof: &ExecHaveObjInNonemptySetStmtSuccessResult,
    before: usize,
    id: FactId,
    actual: &Fact,
) -> Result<Option<String>, LeanCompileError> {
    let mut index = 0;
    for group in &proof.statement.param_def.groups {
        for _parameter in &group.params {
            if index >= before {
                return Ok(None);
            }
            let Some(store) = proof
                .store_and_infer_result
                .store_and_infer_results
                .get(index)
            else {
                return Ok(None);
            };
            if store.primary_fact_id() == id {
                check_store_subject(store, actual)?;
                return Ok(Some(format!("h_{}", id.value())));
            }
            if infer_has_fact(store, id, actual)? {
                return Ok(Some(format!("h_{}", id.value())));
            }
            index += 1;
        }
    }
    Ok(None)
}

fn header_reference(
    groups: &[TypedParameterGroup],
    introduced: &IntroduceTypedParametersResult,
    doms: &[AssumeDomFactResult],
    before: usize,
    id: FactId,
    actual: &Fact,
) -> Result<Option<String>, LeanCompileError> {
    let mut index = 0;
    for group in groups {
        for _parameter in &group.params {
            if index >= before {
                return Ok(None);
            }
            let Some(store) = introduced.defined_params.store_and_infer_results.get(index) else {
                return Ok(None);
            };
            if store.primary_fact_id() == id {
                check_store_subject(store, actual)?;
                return Ok(Some(format!("h_{}", id.value())));
            }
            if infer_has_fact(store, id, actual)? {
                return Ok(Some(format!("h_{}", id.value())));
            }
            index += 1;
        }
    }
    for dom in doms.iter().take(before.saturating_sub(index)) {
        if dom.store_and_infer.primary_fact_id() == id {
            check_store_subject(&dom.store_and_infer, actual)?;
            return Ok(Some(format!("h_{}", id.value())));
        }
        if infer_has_fact(&dom.store_and_infer, id, actual)? {
            return Ok(Some(format!("h_{}", id.value())));
        }
    }
    Ok(None)
}

fn parameter_count(groups: &[TypedParameterGroup]) -> usize {
    groups.iter().map(|group| group.params.len()).sum()
}

fn statement_reference(
    statement: &ExecStmtResult,
    id: FactId,
    actual: &Fact,
    top: Option<(&RunLitexCodeResult, usize)>,
    before: usize,
) -> Result<Option<String>, LeanCompileError> {
    let internal = || format!("h_{}", id.value());
    let global_reference = |name: String| match top {
        Some((run, index)) => application(&name, &context_arguments_before(run, index)),
        None => name,
    };
    match statement {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
            ExecHaveFnEqualStmtResult::Success(p),
        )) => {
            let stores = &p.store_and_infer_result;
            for (stage, store) in [(3, &stores.membership), (4, &stores.defining_equal)] {
                if before < stage {
                    continue;
                }
                if store.primary_fact_id() == id {
                    check_store_subject(store, actual)?;
                    return Ok(Some(global_reference(internal())));
                }
                if infer_has_fact(store, id, actual)? {
                    return Ok(Some(global_reference(internal())));
                }
            }
            Ok(None)
        }
        ExecStmtResult::Fact(ExecFactStmtResult::Success(p))
            if before > 0 && p.store_and_infer_result.primary_fact_id() == id =>
        {
            check_store_subject(&p.store_and_infer_result, actual)?;
            check_subject(
                &verified_subject(&p.verify_result)
                    .ok_or_else(|| LeanCompileError::unsupported("Fact/Subject"))?,
                actual,
            )?;
            Ok(Some(global_reference(internal())))
        }
        ExecStmtResult::By(ExecByStmtResult::Def(ExecByDefStmtResult::Success(p)))
            if before > 0 =>
        {
            if p.stored.primary_fact_id() == id {
                check_store_subject(&p.stored, actual)?;
                check_subject(
                    &verified_subject(&p.proof)
                        .ok_or_else(|| LeanCompileError::unsupported("ByDef/Subject"))?,
                    actual,
                )?;
                return Ok(Some(global_reference(internal())));
            }
            if infer_has_fact(&p.stored, id, actual)? {
                return Ok(Some(global_reference(internal())));
            }
            Ok(None)
        }
        ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) if before > 0 => {
            if infer_has_fact(&p.store_and_infer_result, id, actual)? {
                Ok(Some(global_reference(internal())))
            } else {
                Ok(None)
            }
        }
        ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(p)))
            if before > 0 && p.stored.primary_fact_id() == id =>
        {
            check_store_subject(&p.stored, actual)?;
            check_subject(
                &verified_subject(&p.selected_proof)
                    .ok_or_else(|| LeanCompileError::unsupported("ByThm/Subject"))?,
                actual,
            )?;
            Ok(Some(global_reference(internal())))
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(p),
        )) if before > 0 && p.stored.primary_fact_id() == id => {
            check_store_subject(&p.stored, actual)?;
            check_subject(&p.statement.fact, actual)?;
            Ok(Some(global_reference(internal())))
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(p)),
        )) if before > 0 && p.stored_fact_ids.contains(&id) => {
            Ok(Some(global_reference(internal())))
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(p)),
        )) => {
            let count = p.statement.objs_equal_to.len();
            for (index, store) in p
                .store_and_infer_result
                .store_and_infer_results
                .iter()
                .enumerate()
            {
                let alias = if index < count { index } else { index - count };
                if before <= 2 * count + alias {
                    continue;
                }
                if store.primary_fact_id() == id {
                    check_store_subject(store, actual)?;
                    return Ok(Some(global_reference(internal())));
                }
                if infer_has_fact(store, id, actual)? {
                    return Ok(Some(global_reference(internal())));
                }
            }
            Ok(None)
        }
        _ => {
            if let Some(p) = ordinary_have(statement) {
                let reference = have_reference(p, before, id, actual)?;
                if let Some(reference) = reference {
                    if p.store_and_infer_result
                        .store_and_infer_results
                        .iter()
                        .take(before)
                        .any(|store| store.primary_fact_id() == id)
                    {
                        return Ok(Some(reference));
                    }
                    if let Some((run, statement_index)) = top {
                        let mut arguments = context_arguments_before(run, statement_index);
                        let mut prefix = 0;
                        for (index, store) in p
                            .store_and_infer_result
                            .store_and_infer_results
                            .iter()
                            .enumerate()
                        {
                            if infer_has_fact(store, id, actual)? {
                                prefix = index + 1;
                                break;
                            }
                        }
                        let mut parameters = Vec::new();
                        append_have_parameters(p, prefix, &mut parameters);
                        for (parameter, _, fact_id) in parameters {
                            let number = parameter.id.value();
                            arguments.extend([
                                format!("_Host_i{number}"),
                                format!("_rep_i{number}"),
                                format!("_value_i{number}"),
                                format!("h_{}", fact_id.value()),
                            ]);
                        }
                        return Ok(Some(application(&reference, &arguments)));
                    }
                    return Ok(Some(reference));
                }
            }
            Ok(None)
        }
    }
}

fn fact_reference_in_owner(
    position: &SourcePosition<'_>,
    id: FactId,
    actual: &Fact,
) -> Result<Option<String>, LeanCompileError> {
    match position.owner {
        SourceOwner::Run(run) => {
            for (index, statement) in run
                .statement_results
                .iter()
                .take(position.before)
                .enumerate()
                .rev()
            {
                if let Some(reference) =
                    statement_reference(statement, id, actual, Some((run, index)), usize::MAX)?
                {
                    return Ok(Some(reference));
                }
            }
            Ok(None)
        }
        SourceOwner::Statement(statement) => {
            let top = position.parent.and_then(|parent| match parent.owner {
                SourceOwner::Run(run) => Some((run, parent.before)),
                _ => None,
            });
            statement_reference(statement, id, actual, top, position.before)
        }
        SourceOwner::EmptyForall(p) => {
            if position.before > 0 && p.empty_carrier_store.primary_fact_id() == id {
                check_store_subject(&p.empty_carrier_store, actual)?;
                Ok(Some(format!("h_{}", id.value())))
            } else {
                Ok(None)
            }
        }
        SourceOwner::Forall(p) => {
            if let Some(reference) = header_reference(
                &p.fact.typed_parameters.groups,
                &p.introduced_params,
                &p.assumed_dom_facts,
                position.before,
                id,
                actual,
            )? {
                return Ok(Some(reference));
            }
            let head = parameter_count(&p.fact.typed_parameters.groups) + p.assumed_dom_facts.len();
            for then in p
                .proved_then_facts
                .iter()
                .take(position.before.saturating_sub(head))
            {
                if then.store_and_infer.primary_fact_id() == id {
                    check_store_subject(&then.store_and_infer, actual)?;
                    return Ok(Some(format!("h_{}", id.value())));
                }
            }
            Ok(None)
        }
        SourceOwner::ForallWD(fact, p) => header_reference(
            &fact.typed_parameters.groups,
            &p.introduced_params,
            &p.assumed_dom_facts,
            position.before,
            id,
            actual,
        ),
        SourceOwner::KnownForall(p) => header_reference(
            &p.fact.typed_parameters.groups,
            &p.well_defined.introduced_params,
            &p.well_defined.assumed_dom_facts,
            position.before,
            id,
            actual,
        ),
        SourceOwner::Named(p) => {
            let (steps, head) = match (&p.statement.fact, &p.body) {
                (Fact::ForallFact(fact), ExecDefThmBodyProof::Forall(body)) => {
                    if let Some(reference) = header_reference(
                        &fact.typed_parameters.groups,
                        &body.introduced_params,
                        &body.assumed_dom_facts,
                        position.before,
                        id,
                        actual,
                    )? {
                        return Ok(Some(reference));
                    }
                    (
                        &body.proof_steps,
                        parameter_count(&fact.typed_parameters.groups)
                            + body.assumed_dom_facts.len(),
                    )
                }
                (_, ExecDefThmBodyProof::NonForall(body)) => (&body.proof_steps, 0),
                _ => return Ok(None),
            };
            for statement in steps
                .iter()
                .take(position.before.saturating_sub(head))
                .rev()
            {
                if let Some(reference) =
                    statement_reference(statement, id, actual, None, usize::MAX)?
                {
                    return Ok(Some(reference));
                }
            }
            Ok(None)
        }
        SourceOwner::Call(p) => {
            for proof in p
                .type_proofs
                .iter()
                .chain(&p.dom_proofs)
                .take(position.before)
            {
                if let Some(subject) = verified_subject(proof) {
                    if subject.fact_id() == id {
                        check_subject(&subject, actual)?;
                        return Ok(Some(format!("h_{}", id.value())));
                    }
                }
            }
            let head = p.type_proofs.len() + p.dom_proofs.len() + p.conclusions_wd.len();
            for store in p
                .returned_conclusions
                .iter()
                .take(position.before.saturating_sub(head))
            {
                if store.primary_fact_id() == id {
                    check_store_subject(store, actual)?;
                    return Ok(Some(format!("h_{}", id.value())));
                }
            }
            Ok(None)
        }
        SourceOwner::SetBuilder(_, p) => {
            for store in p
                .defined_params
                .store_and_infer_results
                .iter()
                .take(position.before.saturating_sub(1))
            {
                if store.primary_fact_id() == id || infer_has_fact(store, id, actual)? {
                    if store.primary_fact_id() == id {
                        check_store_subject(store, actual)?;
                    }
                    return Ok(Some(format!("h_{}", id.value())));
                }
            }
            for assumed in p
                .assumed_facts
                .iter()
                .take(position.before.saturating_sub(2))
            {
                let store = &assumed.store_and_infer;
                if store.primary_fact_id() == id || infer_has_fact(store, id, actual)? {
                    if store.primary_fact_id() == id {
                        check_store_subject(store, actual)?;
                    }
                    return Ok(Some(format!("h_{}", id.value())));
                }
            }
            Ok(None)
        }
        SourceOwner::PropDefinition(p) => {
            let stores = &p.defined_params.store_and_infer_results;
            for store in stores.iter().take(position.before) {
                if store.primary_fact_id() == id {
                    check_store_subject(store, actual)?;
                    return Ok(Some(format!("h_{}", id.value())));
                }
                if infer_has_fact(store, id, actual)? {
                    return Ok(Some(format!("h_{}", id.value())));
                }
            }
            for assumption in p
                .assumed_iff_facts
                .iter()
                .take(position.before.saturating_sub(stores.len()))
            {
                let store = &assumption.store_and_infer;
                if store.primary_fact_id() == id {
                    check_store_subject(store, actual)?;
                    return Ok(Some(format!("h_{}", id.value())));
                }
                if infer_has_fact(store, id, actual)? {
                    return Ok(Some(format!("h_{}", id.value())));
                }
            }
            Ok(None)
        }
        SourceOwner::PropInference(store) => {
            for derived in prop_inference_stages(store)
                .into_iter()
                .take(position.before)
            {
                let store = &derived.store_and_infer;
                if store.primary_fact_id() == id {
                    check_store_subject(store, actual)?;
                    return Ok(Some(format!("h_{}", id.value())));
                }
                if infer_has_fact(store, id, actual)? {
                    return Ok(Some(format!("h_{}", id.value())));
                }
            }
            Ok(None)
        }
        SourceOwner::WD(proof) => {
            if let Some((_, carriers, parameters, domains, _)) = function_binder(proof) {
                for store in parameters
                    .store_and_infer_results
                    .iter()
                    .take(position.before.saturating_sub(carriers.len()))
                {
                    if store.primary_fact_id() == id {
                        check_store_subject(store, actual)?;
                        return Ok(Some(format!("h_{}", id.value())));
                    }
                    if infer_has_fact(store, id, actual)? {
                        return Ok(Some(format!("h_{}", id.value())));
                    }
                }
                let head = carriers.len() + parameters.store_and_infer_results.len();
                for domain in domains.iter().take(position.before.saturating_sub(head)) {
                    let store = &domain.store_and_infer;
                    if store.primary_fact_id() == id {
                        check_store_subject(store, actual)?;
                        return Ok(Some(format!("h_{}", id.value())));
                    }
                    if infer_has_fact(store, id, actual)? {
                        return Ok(Some(format!("h_{}", id.value())));
                    }
                }
            }
            Ok(None)
        }
        // Formation children can supply construction evidence, never a truth producer.
        SourceOwner::Verify(_)
        | SourceOwner::AtomicWD(_)
        | SourceOwner::FactWD(_)
        | SourceOwner::HaveEqualType(_)
        | SourceOwner::HaveGroup(_, _)
        | SourceOwner::ParamTypeWD(_)
        | SourceOwner::ByDef(_)
        | SourceOwner::PropRequirements(_) => Ok(None),
        SourceOwner::FunctionNormalization(_)
        | SourceOwner::FunctionExpansion(_)
        | SourceOwner::FunctionDefinitionRewrite(_) => Ok(None),
    }
}

fn named_steps(proof: &ExecDefThmStmtSuccess) -> (&[ExecStmtResult], usize) {
    match (&proof.statement.fact, &proof.body) {
        (Fact::ForallFact(fact), ExecDefThmBodyProof::Forall(body)) => (
            &body.proof_steps,
            parameter_count(&fact.typed_parameters.groups) + body.assumed_dom_facts.len(),
        ),
        (_, ExecDefThmBodyProof::NonForall(body)) => (&body.proof_steps, 0),
        _ => (&[], 0),
    }
}

fn alias_in_statement<T>(
    statement: &ExecStmtResult,
    object: &Obj,
    before: usize,
    parent: &SourcePosition<'_>,
    callback: &mut impl FnMut(
        &BoundName,
        &Obj,
        &VerifyObjWellDefinedResult,
        &SourcePosition<'_>,
    ) -> Result<T, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    let Obj::Identifier(IdentifierObj::Plain { id, .. }) = object else {
        return Ok(None);
    };
    match statement {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(p)),
        )) if before > 0 && p.statement.name.id == *id => {
            let position = SourcePosition::new(Some(parent), SourceOwner::Statement(statement), 0);
            callback(
                &p.statement.name,
                &p.statement.value,
                &p.value_well_defined,
                &position,
            )
            .map(Some)
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(p)),
        )) => {
            let count = p.statement.objs_equal_to.len();
            for (index, parameter) in p
                .statement
                .param_def
                .groups
                .iter()
                .flat_map(|group| &group.params)
                .enumerate()
            {
                if parameter.id == *id && before > 2 * count + index {
                    if let (Some(value), Some(wd)) = (
                        p.statement.objs_equal_to.get(index),
                        p.equal_to_well_defined.get(index),
                    ) {
                        let position = SourcePosition::new(
                            Some(parent),
                            SourceOwner::Statement(statement),
                            index,
                        );
                        return callback(parameter, value, wd, &position).map(Some);
                    }
                }
            }
            Ok(None)
        }
        _ => Ok(None),
    }
}

fn store_has_natural_zero(store: &StoreFactAndInferResult) -> bool {
    let source = match &store.store {
        StoreFactResult::AtomicFact(p) => match &p.fact {
            AtomicFact::InFact(f) if f.set == Obj::StandardSet(StandardSet::N) => f,
            _ => return false,
        },
        _ => return false,
    };
    if let InferFactResult::AtomicFact(InferAtomicFactResult::ExceptEquality(rules)) = &store.infer
    {
        for rule in rules {
            if let InferAtomicExceptEqualityResult::InFactSignedStandardSetSign(p) = rule {
                if p.derived.len() != 1 {
                    return false;
                }
                if let StoreFactResult::AtomicFact(derived) = &p.derived[0].store {
                    if let AtomicFact::LessEqualFact(bound) = &derived.fact {
                        return matches!(&bound.left, Obj::Literal(Literal::Number(n)) if n.normalized_value == "0")
                            && bound.right.ir() == source.element.ir();
                    }
                }
            }
        }
    }
    false
}

fn have_has_natural_zero(proof: &ExecHaveObjInNonemptySetStmtSuccessResult, before: usize) -> bool {
    proof
        .store_and_infer_result
        .store_and_infer_results
        .iter()
        .take(before)
        .any(|store| store_has_natural_zero(store))
}

fn introduction_has_natural_zero(proof: &IntroduceTypedParametersResult, before: usize) -> bool {
    proof
        .defined_params
        .store_and_infer_results
        .iter()
        .take(before)
        .any(|store| store_has_natural_zero(store))
}

fn visit_visible<T>(
    start: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        &ObjWellDefinedProof,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    let mut position = Some(start);
    while let Some(current) = position {
        if let Some(value) = visit_owner(current, wd, verify)? {
            return Ok(Some(value));
        }
        position = current.parent;
    }
    Ok(None)
}

fn visit_function_formation<T>(
    proof: &ObjWellDefinedProof,
    position: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        &ObjWellDefinedProof,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    let Some((_, carriers, parameters, domains, _)) = function_binder(proof) else {
        return Ok(None);
    };
    let head = carriers.len() + parameters.store_and_infer_results.len();
    let end = head + domains.len();
    let ret = match proof {
        ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(
                    FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(p),
                ),
            ..
        } => {
            if position.before > end + 2 {
                if let AnonymousFnBodyInReturnSetProof::CheckedMembership(member) =
                    &p.body_in_ret_set
                {
                    let prior = SourcePosition {
                        before: end + 2,
                        ..*position
                    };
                    if let Some(value) = visit_complete_verify(member, &prior, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
            }
            if position.before > end + 1 {
                let prior = SourcePosition {
                    before: end + 1,
                    ..*position
                };
                if let Some(value) = visit_complete_wd(&p.body_well_defined, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            &p.ret_set_well_defined
        }
        ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::FnSet(p)),
            ..
        } => &p.ret_set_well_defined,
        _ => return Ok(None),
    };
    if position.before > end {
        let prior = SourcePosition {
            before: end,
            ..*position
        };
        if let Some(value) = visit_complete_wd(ret, &prior, wd, verify)? {
            return Ok(Some(value));
        }
    }
    for (index, domain) in domains
        .iter()
        .take(position.before.saturating_sub(head))
        .enumerate()
        .rev()
    {
        let prior = SourcePosition {
            before: head + index,
            ..*position
        };
        let inferred = SourcePosition::new(
            Some(&prior),
            SourceOwner::PropInference(&domain.store_and_infer),
            usize::MAX,
        );
        if let Some(value) = visit_owner(&inferred, wd, verify)? {
            return Ok(Some(value));
        }
        let formation = SourcePosition::new(
            Some(&prior),
            SourceOwner::FactWD(&domain.well_defined),
            usize::MAX,
        );
        if let Some(value) =
            visit_fact_formation(&domain.well_defined, usize::MAX, &formation, wd, verify)?
        {
            return Ok(Some(value));
        }
    }
    for (index, carrier) in carriers.iter().take(position.before).enumerate().rev() {
        let prior = SourcePosition {
            before: index,
            ..*position
        };
        if let Some(value) = visit_complete_wd(carrier, &prior, wd, verify)? {
            return Ok(Some(value));
        }
    }
    Ok(None)
}

fn visit_owner<T>(
    position: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        &ObjWellDefinedProof,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    match position.owner {
        SourceOwner::Run(run) => {
            for (index, statement) in run
                .statement_results
                .iter()
                .take(position.before)
                .enumerate()
                .rev()
            {
                let prior = SourcePosition::new(None, SourceOwner::Run(run), index);
                if let Some(value) = visit_statement(statement, usize::MAX, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::Statement(statement) => {
            if let Some(parent) = position.parent {
                return visit_statement(statement, position.before, parent, wd, verify);
            }
        }
        SourceOwner::Verify(proof) => {
            return visit_verify_formation(proof, position.before, position, wd, verify)
        }
        SourceOwner::WD(proof) => {
            if let Some(value) = visit_function_formation(proof, position, wd, verify)? {
                return Ok(Some(value));
            }
            if let ObjWellDefinedProof::ByDef {
                obj: Obj::SetFormer(SetFormer::SetBuilder(set)),
                proof:
                    ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::SetBuilder(
                        captured,
                    )),
            } = proof
            {
                let scope = SourcePosition::new(
                    Some(position),
                    SourceOwner::SetBuilder(set, captured),
                    position.before,
                );
                let mut closed = |proof: &ObjWellDefinedProof, position: &SourcePosition<'_>| {
                    if closed_leaf(proof.obj()) {
                        wd(proof, position)
                    } else {
                        Ok(None)
                    }
                };
                if let Some(value) = visit_owner(&scope, &mut closed, &mut |_, _| Ok(None))? {
                    return Ok(Some(value));
                }
            }
            if let Some((children, requirements)) = arithmetic_stages(proof) {
                for (index, requirement) in requirements
                    .iter()
                    .take(position.before.saturating_sub(children.len()))
                    .enumerate()
                    .rev()
                {
                    let prior = SourcePosition {
                        before: children.len() + index,
                        ..*position
                    };
                    if let Some(value) = visit_complete_verify(requirement, &prior, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
                for (index, child) in children.iter().take(position.before).enumerate().rev() {
                    let prior = SourcePosition {
                        before: index,
                        ..*position
                    };
                    if let Some(value) = visit_complete_wd(child, &prior, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
            }
        }
        SourceOwner::AtomicWD(proof) => {
            return visit_atomic_formation(proof, position.before, position, wd, verify)
        }
        SourceOwner::FactWD(proof) => {
            return visit_fact_formation(proof, position.before, position, wd, verify)
        }
        SourceOwner::EmptyForall(proof) => {
            if position.before > 0 {
                let prior = SourcePosition {
                    before: 0,
                    ..*position
                };
                if let Some(value) =
                    visit_complete_verify(&proof.empty_carrier_proof, &prior, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::Forall(proof) => {
            let head = parameter_count(&proof.fact.typed_parameters.groups)
                + proof.assumed_dom_facts.len();
            for (index, then) in proof
                .proved_then_facts
                .iter()
                .take(position.before.saturating_sub(head))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: head + index,
                    ..*position
                };
                if let Some(value) = visit_complete_verify(&then.verify_result, &prior, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
            return visit_header(
                &proof.fact,
                &proof.introduced_params,
                &proof.assumed_dom_facts,
                position,
                wd,
                verify,
            );
        }
        SourceOwner::ForallWD(fact, proof) => {
            let head =
                parameter_count(&fact.typed_parameters.groups) + proof.assumed_dom_facts.len();
            for (index, then) in proof
                .then
                .iter()
                .take(position.before.saturating_sub(head))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: head + index,
                    ..*position
                };
                let formation =
                    SourcePosition::new(Some(&prior), SourceOwner::FactWD(then), usize::MAX);
                if let Some(value) = visit_fact_formation(then, usize::MAX, &formation, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
            return visit_header(
                fact,
                &proof.introduced_params,
                &proof.assumed_dom_facts,
                position,
                wd,
                verify,
            );
        }
        SourceOwner::KnownForall(proof) => {
            let head = parameter_count(&proof.fact.typed_parameters.groups)
                + proof.well_defined.assumed_dom_facts.len();
            for (index, then) in proof
                .well_defined
                .then
                .iter()
                .take(position.before.saturating_sub(head))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: head + index,
                    ..*position
                };
                let formation =
                    SourcePosition::new(Some(&prior), SourceOwner::FactWD(then), usize::MAX);
                if let Some(value) = visit_fact_formation(then, usize::MAX, &formation, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
            return visit_header(
                &proof.fact,
                &proof.well_defined.introduced_params,
                &proof.well_defined.assumed_dom_facts,
                position,
                wd,
                verify,
            );
        }
        SourceOwner::Named(proof) => {
            let (steps, head) = named_steps(proof);
            for (index, statement) in steps
                .iter()
                .take(position.before.saturating_sub(head))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: head + index,
                    ..*position
                };
                if let Some(value) = visit_statement(statement, usize::MAX, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            if let (Fact::ForallFact(fact), ExecDefThmBodyProof::Forall(body)) =
                (&proof.statement.fact, &proof.body)
            {
                return visit_header(
                    fact,
                    &body.introduced_params,
                    &body.assumed_dom_facts,
                    position,
                    wd,
                    verify,
                );
            }
        }
        SourceOwner::Call(proof) => {
            let head = proof.type_proofs.len() + proof.dom_proofs.len();
            for (index, conclusion) in proof
                .conclusions_wd
                .iter()
                .take(position.before.saturating_sub(head))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: head + index,
                    ..*position
                };
                let formation =
                    SourcePosition::new(Some(&prior), SourceOwner::FactWD(conclusion), usize::MAX);
                if let Some(value) =
                    visit_fact_formation(conclusion, usize::MAX, &formation, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
            let completed = position
                .before
                .min(proof.type_proofs.len() + proof.dom_proofs.len());
            for index in (0..completed).rev() {
                let proof = if index < proof.type_proofs.len() {
                    &proof.type_proofs[index]
                } else {
                    &proof.dom_proofs[index - proof.type_proofs.len()]
                };
                let prior = SourcePosition {
                    before: index,
                    ..*position
                };
                if let Some(value) = visit_complete_verify(proof, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::HaveEqualType(_) => {}
        SourceOwner::HaveGroup(carrier, nonempty) => {
            if position.before > 1 {
                if let ParamTypeFactCheckResult::Obj(proof) = nonempty {
                    let prior = SourcePosition {
                        before: 1,
                        ..*position
                    };
                    if let Some(value) = visit_complete_verify(proof, &prior, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
            }
            if position.before > 0 {
                if let ParamTypeWellDefinedProof::Obj(VerifyObjWellDefinedResult::Success(proof)) =
                    carrier
                {
                    let prior = SourcePosition {
                        before: 0,
                        ..*position
                    };
                    if let Some(value) = visit_complete_wd(proof, &prior, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
            }
        }
        SourceOwner::ParamTypeWD(carrier) => {
            if position.before > 0 {
                if let ParamTypeWellDefinedProof::Obj(VerifyObjWellDefinedResult::Success(proof)) =
                    carrier
                {
                    let prior = SourcePosition {
                        before: 0,
                        ..*position
                    };
                    if let Some(value) = visit_complete_wd(proof, &prior, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
            }
        }
        SourceOwner::SetBuilder(_, proof) => {
            for (i, assumed) in proof
                .assumed_facts
                .iter()
                .take(position.before.saturating_sub(2))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: 2 + i,
                    ..*position
                };
                let inferred = SourcePosition::new(
                    Some(&prior),
                    SourceOwner::PropInference(&assumed.store_and_infer),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&inferred, wd, verify)? {
                    return Ok(Some(value));
                }
                let formation = SourcePosition::new(
                    Some(&prior),
                    SourceOwner::FactWD(&assumed.well_defined),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&formation, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            if position.before > 0 {
                let prior = SourcePosition {
                    before: 0,
                    ..*position
                };
                if let Some(value) =
                    visit_complete_wd(&proof.param_set_well_defined, &prior, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::PropDefinition(proof) => {
            let count = parameter_count(&proof.statement.typed_parameters.groups);
            for (index, assumed) in proof
                .assumed_iff_facts
                .iter()
                .take(position.before.saturating_sub(count))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: count + index,
                    ..*position
                };
                let inference = SourcePosition::new(
                    Some(&prior),
                    SourceOwner::PropInference(&assumed.store_and_infer),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&inference, wd, verify)? {
                    return Ok(Some(value));
                }
                let formation = SourcePosition::new(
                    Some(&prior),
                    SourceOwner::FactWD(&assumed.well_defined),
                    usize::MAX,
                );
                if let Some(value) =
                    visit_fact_formation(&assumed.well_defined, usize::MAX, &formation, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
            let mut offset = 0;
            for (group, carrier) in proof
                .statement
                .typed_parameters
                .groups
                .iter()
                .zip(&proof.param_type_well_defined)
            {
                if offset < position.before {
                    if let ParamTypeWellDefinedProof::Obj(VerifyObjWellDefinedResult::Success(
                        carrier,
                    )) = carrier
                    {
                        let prior = SourcePosition {
                            before: offset,
                            ..*position
                        };
                        if let Some(value) = visit_complete_wd(carrier, &prior, wd, verify)? {
                            return Ok(Some(value));
                        }
                    }
                }
                offset += group.params.len();
            }
        }
        SourceOwner::ByDef(proof) => {
            if position.before > 1 {
                let prior = SourcePosition {
                    before: 1,
                    ..*position
                };
                if let Some(value) = visit_complete_verify(&proof.proof, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            if position.before > 0 {
                if let VerifyFactWellDefinedResult::Success(goal) = &proof.goal_wd {
                    let prior = SourcePosition {
                        before: 0,
                        ..*position
                    };
                    let formation =
                        SourcePosition::new(Some(&prior), SourceOwner::FactWD(goal), usize::MAX);
                    return visit_fact_formation(goal, usize::MAX, &formation, wd, verify);
                }
            }
        }
        SourceOwner::PropRequirements(proof) => {
            for (index, child) in proof
                .proof_of_requirement_facts
                .iter()
                .take(position.before)
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: index,
                    ..*position
                };
                if let Some(value) = visit_complete_verify(child, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::PropInference(store) => {
            for (index, derived) in prop_inference_stages(store)
                .into_iter()
                .take(position.before)
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: index,
                    ..*position
                };
                let nested = SourcePosition::new(
                    Some(&prior),
                    SourceOwner::PropInference(&derived.store_and_infer),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&nested, wd, verify)? {
                    return Ok(Some(value));
                }
                let formation = SourcePosition::new(
                    Some(&prior),
                    SourceOwner::FactWD(&derived.well_defined),
                    usize::MAX,
                );
                if let Some(value) =
                    visit_fact_formation(&derived.well_defined, usize::MAX, &formation, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::FunctionNormalization(proof) => {
            for (index, step) in proof
                .expansions
                .iter()
                .take(position.before)
                .enumerate()
                .rev()
            {
                if let FunctionBodyExpansionProof::Anonymous(step) = step {
                    let prior = SourcePosition {
                        before: index,
                        ..*position
                    };
                    let expansion = SourcePosition::new(
                        Some(&prior),
                        SourceOwner::FunctionExpansion(step),
                        usize::MAX,
                    );
                    if let Some(value) = visit_owner(&expansion, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
            }
        }
        SourceOwner::FunctionDefinitionRewrite(steps) => {
            for (index, step) in steps.iter().take(position.before).enumerate().rev() {
                let prior = SourcePosition {
                    before: index,
                    ..*position
                };
                let expansion = SourcePosition::new(
                    Some(&prior),
                    SourceOwner::FunctionExpansion(step),
                    usize::MAX,
                );
                if let Some(value) = visit_owner(&expansion, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        SourceOwner::FunctionExpansion(proof) => {
            if position.before > 2 {
                let prior = SourcePosition {
                    before: 2,
                    ..*position
                };
                if let Some(value) =
                    visit_complete_wd(&proof.body_application_well_defined, &prior, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
            if position.before > 0 {
                let prior = SourcePosition {
                    before: 0,
                    ..*position
                };
                if let Some(value) =
                    visit_complete_wd(&proof.application_well_defined, &prior, wd, verify)?
                {
                    return Ok(Some(value));
                }
            }
        }
    }
    Ok(None)
}

fn visit_header<T>(
    fact: &ForallFact,
    introduced: &IntroduceTypedParametersResult,
    doms: &[AssumeDomFactResult],
    position: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        &ObjWellDefinedProof,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    let count = parameter_count(&fact.typed_parameters.groups);
    for (index, dom) in doms
        .iter()
        .take(position.before.saturating_sub(count))
        .enumerate()
        .rev()
    {
        let prior = SourcePosition {
            before: count + index,
            ..*position
        };
        let inference = SourcePosition::new(
            Some(&prior),
            SourceOwner::PropInference(&dom.store_and_infer),
            usize::MAX,
        );
        if let Some(value) = visit_owner(&inference, wd, verify)? {
            return Ok(Some(value));
        }
        let formation = SourcePosition::new(
            Some(&prior),
            SourceOwner::FactWD(&dom.well_defined),
            usize::MAX,
        );
        if let Some(value) =
            visit_fact_formation(&dom.well_defined, usize::MAX, &formation, wd, verify)?
        {
            return Ok(Some(value));
        }
    }
    let mut offset = 0;
    for (group, proof) in fact
        .typed_parameters
        .groups
        .iter()
        .zip(&introduced.param_type_well_defined)
    {
        let end = offset + group.params.len();
        if offset < position.before {
            if let ParamTypeWellDefinedProof::Obj(VerifyObjWellDefinedResult::Success(proof)) =
                proof
            {
                let prior = SourcePosition {
                    before: offset,
                    ..*position
                };
                if let Some(value) = visit_complete_wd(proof, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        offset = end;
    }
    Ok(None)
}

fn visit_statement<T>(
    statement: &ExecStmtResult,
    before: usize,
    parent: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        &ObjWellDefinedProof,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    let position = SourcePosition::new(Some(parent), SourceOwner::Statement(statement), 0);
    match statement {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
            ExecHaveFnEqualStmtResult::Success(proof),
        )) if before > 0 => {
            if before > 1 {
                let prior = SourcePosition {
                    before: 1,
                    ..position
                };
                if let VerifyObjWellDefinedResult::Success(proof) = &proof.fn_set_well_defined {
                    if let Some(value) = visit_complete_wd(proof, &prior, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
            }
            if let VerifyObjWellDefinedResult::Success(proof) = &proof.anonymous_fn_well_defined {
                return visit_complete_wd(proof, &position, wd, verify);
            }
            Ok(None)
        }
        ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) if before > 0 => {
            let seed = SourcePosition {
                before: 1,
                ..position
            };
            let inference = SourcePosition::new(
                Some(&seed),
                SourceOwner::PropInference(&proof.store_and_infer_result),
                usize::MAX,
            );
            if let Some(value) = visit_owner(&inference, wd, verify)? {
                return Ok(Some(value));
            }
            visit_complete_verify(&proof.verify_result, &position, wd, verify)
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
            ExecDefPropStmtResult::Success(proof),
        )) if before > 0 => {
            let mut closed = |proof: &ObjWellDefinedProof, position: &SourcePosition<'_>| {
                if closed_leaf(proof.obj()) {
                    wd(proof, position)
                } else {
                    Ok(None)
                }
            };
            let scope = SourcePosition::new(
                Some(&position),
                SourceOwner::PropDefinition(proof),
                usize::MAX,
            );
            visit_owner(&scope, &mut closed, &mut |_, _| Ok(None))
        }
        ExecStmtResult::By(ExecByStmtResult::Def(ExecByDefStmtResult::Success(proof)))
            if before > 0 =>
        {
            let seed = SourcePosition {
                before: 1,
                ..position
            };
            let inference = SourcePosition::new(
                Some(&seed),
                SourceOwner::PropInference(&proof.stored),
                usize::MAX,
            );
            if let Some(value) = visit_owner(&inference, wd, verify)? {
                return Ok(Some(value));
            }
            let mut closed = |proof: &ObjWellDefinedProof, position: &SourcePosition<'_>| {
                if closed_leaf(proof.obj()) {
                    wd(proof, position)
                } else {
                    Ok(None)
                }
            };
            let scope = SourcePosition::new(Some(&position), SourceOwner::ByDef(proof), usize::MAX);
            visit_owner(&scope, &mut closed, &mut |_, _| Ok(None))
        }
        // A completed theorem or call exports only its selected whole statement,
        // never its closed binder/call-local construction records.
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(proof),
        )) if before > 0 => {
            let mut closed = |proof: &ObjWellDefinedProof, position: &SourcePosition<'_>| {
                if closed_leaf(proof.obj()) {
                    wd(proof, position)
                } else {
                    Ok(None)
                }
            };
            let scope = SourcePosition::new(Some(&position), SourceOwner::Named(proof), usize::MAX);
            if let Some(value) = visit_owner(&scope, &mut closed, &mut |_, _| Ok(None))? {
                return Ok(Some(value));
            }
            if let VerifyFactWellDefinedResult::Success(goal) = &proof.goal_wd {
                if let (Fact::ForallFact(fact), FactWellDefinedProof::ForallFact(goal)) =
                    (&proof.statement.fact, goal)
                {
                    let scope = SourcePosition::new(
                        Some(&position),
                        SourceOwner::ForallWD(fact, goal),
                        usize::MAX,
                    );
                    visit_owner(&scope, &mut closed, &mut |_, _| Ok(None))
                } else {
                    let scope =
                        SourcePosition::new(Some(&position), SourceOwner::FactWD(goal), usize::MAX);
                    visit_owner(&scope, &mut closed, &mut |_, _| Ok(None))
                }
            } else {
                Ok(None)
            }
        }
        ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(proof)))
            if before > 0 =>
        {
            let mut closed = |proof: &ObjWellDefinedProof, position: &SourcePosition<'_>| {
                if closed_leaf(proof.obj()) {
                    wd(proof, position)
                } else {
                    Ok(None)
                }
            };
            let scope = SourcePosition::new(Some(&position), SourceOwner::Call(proof), usize::MAX);
            if let Some(value) = visit_owner(&scope, &mut closed, &mut |_, _| Ok(None))? {
                return Ok(Some(value));
            }
            visit_complete_verify(&proof.selected_proof, &scope, &mut closed, &mut |_, _| {
                Ok(None)
            })
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(_)) | ExecStmtResult::By(_) => {
            Ok(None)
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(proof)),
        )) if before > 0 => {
            if let VerifyObjWellDefinedResult::Success(proof) = &proof.value_well_defined {
                visit_complete_wd(proof, &position, wd, verify)
            } else {
                Ok(None)
            }
        }
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(proof)),
        )) => {
            let count = proof.equal_to_well_defined.len();
            for (index, proof) in proof
                .membership_checks
                .iter()
                .take(before.saturating_sub(count))
                .enumerate()
                .rev()
            {
                let prior = SourcePosition {
                    before: count + index,
                    ..position
                };
                if let Some(value) = visit_complete_verify(proof, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
            for (index, proof) in proof
                .equal_to_well_defined
                .iter()
                .take(before)
                .enumerate()
                .rev()
            {
                if let VerifyObjWellDefinedResult::Success(proof) = proof {
                    let prior = SourcePosition {
                        before: index,
                        ..position
                    };
                    if let Some(value) = visit_complete_wd(proof, &prior, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
            }
            Ok(None)
        }
        _ => {
            if let Some(proof) = ordinary_have(statement) {
                let mut offset = 0;
                for (group, captured) in proof.statement.param_def.groups.iter().zip(&proof.groups)
                {
                    if offset < before {
                        let prior = SourcePosition {
                            before: offset,
                            ..position
                        };
                        let group_position = SourcePosition::new(
                            Some(&prior),
                            SourceOwner::HaveGroup(
                                &captured.param_type_well_defined,
                                &captured.nonempty_check,
                            ),
                            2,
                        );
                        if let Some(value) = visit_owner(&group_position, wd, verify)? {
                            return Ok(Some(value));
                        }
                    }
                    offset += group.params.len();
                }
            }
            Ok(None)
        }
    }
}

fn visit_complete_wd<T>(
    proof: &ObjWellDefinedProof,
    parent: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        &ObjWellDefinedProof,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    if let Some(value) = wd(proof, parent)? {
        return Ok(Some(value));
    }
    let position = SourcePosition::new(Some(parent), SourceOwner::WD(proof), usize::MAX);
    visit_owner(&position, wd, verify)
}

fn visit_complete_verify<T>(
    proof: &VerifyFactResult,
    parent: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        &ObjWellDefinedProof,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    if let Some(value) = verify(proof, parent)? {
        return Ok(Some(value));
    }
    let position = SourcePosition::new(Some(parent), SourceOwner::Verify(proof), usize::MAX);
    if let VerifyFactResult::ForallFact(proof) = proof {
        if let VerifyForallFactResult::Success(proof) = proof.as_ref() {
            let owner = match proof {
                VerifyForallFactProof::ByLocalIntroduction(p) => Some(SourceOwner::Forall(p)),
                VerifyForallFactProof::ByKnownForallFact(p) => Some(SourceOwner::KnownForall(p)),
                _ => None,
            };
            if let Some(owner) = owner {
                let mut closed = |proof: &ObjWellDefinedProof, position: &SourcePosition<'_>| {
                    if closed_leaf(proof.obj()) {
                        wd(proof, position)
                    } else {
                        Ok(None)
                    }
                };
                let scope = SourcePosition::new(Some(&position), owner, usize::MAX);
                return visit_owner(&scope, &mut closed, &mut |_, _| Ok(None));
            }
        }
    }
    visit_verify_formation(proof, usize::MAX, &position, wd, verify)
}

fn closed_leaf(object: &Obj) -> bool {
    matches!(
        object,
        Obj::Literal(Literal::Number(_)) | Obj::StandardSet(_)
    )
}

fn visit_verify_formation<T>(
    proof: &VerifyFactResult,
    before: usize,
    position: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        &ObjWellDefinedProof,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    match proof {
        VerifyFactResult::Equality(proof) => match proof.as_ref() {
            VerifyEqualityResult::Success(proof) => {
                let children = [
                    &proof.well_defined_proof.left,
                    &proof.well_defined_proof.right,
                ];
                for (index, child) in children.iter().take(before).enumerate().rev() {
                    let prior = SourcePosition {
                        before: index,
                        ..*position
                    };
                    if let Some(value) = visit_complete_wd(child, &prior, wd, verify)? {
                        return Ok(Some(value));
                    }
                }
            }
            _ => {}
        },
        VerifyFactResult::AtomicExceptEquality(proof) => {
            if let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_ref() {
                return visit_atomic_formation(
                    &proof.well_defined_proof,
                    before,
                    position,
                    wd,
                    verify,
                );
            }
        }
        // Completed quantified proofs cannot reopen their closed source scope.
        _ => {}
    }
    Ok(None)
}

fn visit_atomic_formation<T>(
    proof: &AtomicFactWellDefinedProof,
    before: usize,
    position: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        &ObjWellDefinedProof,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    let children = &proof.well_defined_of_each_parameter;
    if let PredicateDomainProof::ByRequirements(requirements) = &proof.predicate_domain {
        for (index, requirement) in requirements
            .iter()
            .take(before.saturating_sub(children.len()))
            .enumerate()
            .rev()
        {
            let prior = SourcePosition {
                before: children.len() + index,
                ..*position
            };
            if let Some(value) = visit_complete_verify(&requirement.result, &prior, wd, verify)? {
                return Ok(Some(value));
            }
        }
    }
    for (index, child) in children.iter().take(before).enumerate().rev() {
        let prior = SourcePosition {
            before: index,
            ..*position
        };
        if let Some(value) = visit_complete_wd(child, &prior, wd, verify)? {
            return Ok(Some(value));
        }
    }
    Ok(None)
}

fn visit_fact_formation<T>(
    proof: &FactWellDefinedProof,
    before: usize,
    position: &SourcePosition<'_>,
    wd: &mut dyn FnMut(
        &ObjWellDefinedProof,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
    verify: &mut dyn FnMut(
        &VerifyFactResult,
        &SourcePosition<'_>,
    ) -> Result<Option<T>, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    match proof {
        FactWellDefinedProof::Equality(proof) => {
            let children = [&proof.left, &proof.right];
            for (index, child) in children.iter().take(before).enumerate().rev() {
                let prior = SourcePosition {
                    before: index,
                    ..*position
                };
                if let Some(value) = visit_complete_wd(child, &prior, wd, verify)? {
                    return Ok(Some(value));
                }
            }
        }
        FactWellDefinedProof::AtomicExceptEquality(proof) => {
            return visit_atomic_formation(proof, before, position, wd, verify)
        }
        _ => {}
    }
    Ok(None)
}

fn arithmetic_stages(
    proof: &ObjWellDefinedProof,
) -> Option<(&[Box<ObjWellDefinedProof>], &[VerifyFactResult])> {
    if let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(proof),
        ..
    } = proof
    {
        return Some((
            &proof.child_obj_well_defined,
            &proof.requirement_fact_verified,
        ));
    }
    if let ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::ListSet(proof)),
        ..
    } = proof
    {
        return Some((
            &proof.child_obj_well_defined,
            &proof.requirement_fact_verified,
        ));
    }
    let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::ArithmeticOperator(proof),
        ..
    } = proof
    else {
        return None;
    };
    match proof {
        ArithmeticOperatorObjWellDefinedProofByDef::Add(p) => {
            Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
        }
        ArithmeticOperatorObjWellDefinedProofByDef::Sub(p) => {
            Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
        }
        ArithmeticOperatorObjWellDefinedProofByDef::Mul(p) => {
            Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
        }
        ArithmeticOperatorObjWellDefinedProofByDef::Div(p) => {
            Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
        }
        ArithmeticOperatorObjWellDefinedProofByDef::Neg(p) => {
            Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
        }
        ArithmeticOperatorObjWellDefinedProofByDef::Pow(p) => {
            Some((&p.child_obj_well_defined, &p.requirement_fact_verified))
        }
        _ => None,
    }
}
