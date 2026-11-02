use super::helper::{
    ensure_object, instantiated_fact_matches, instantiated_object_matches, set_kind_predicate,
    source_subject,
};
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TemplateDefEnum;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::InstantiatedTemplateObjObjWellDefinedProof;
use crate::execute::{
    ExecDefTemplateStmtResult, ExecDefTemplateStmtSuccessResult,
    ExecHaveFnByForallExistUniqueStmtResult, ExecHaveFnByInducStmtResult,
    ExecHaveFnEqualCaseByCaseStmtResult, ExecHaveFnEqualStmtResult,
    ExecHaveObjByExistFactsStmtResult, ExecObtainObjFromAtomicFactStmtResult,
    ExecObtainObjFromExistFactStmtResult,
};
use crate::prelude::*;
use std::collections::HashMap;

pub(super) fn alias_body(
    p: &ExecDefTemplateStmtSuccessResult,
) -> Result<&ExecHaveObjEqualStmtSuccessResult, LeanCompileError> {
    match p.body.as_ref() {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(body)),
        )) => Ok(body),
        _ => Err(LeanCompileError::unsupported("Template/Body")),
    }
}

// Borrow the original declaration and publication IDs; the body itself still
// goes through ordinary statement compilation.
pub(super) fn template_bindings(
    p: &ExecDefTemplateStmtSuccessResult,
) -> Result<(Vec<&BoundName>, &[FactId]), LeanCompileError> {
    match (&p.statement.template_def_stmt, p.body.as_ref()) {
        (
            TemplateDefEnum::HaveObjInNonemptySetStmt(source),
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::HaveObjInNonemptySet(
                    ExecHaveObjInNonemptySetStmtResult::Success(body),
                ),
            )),
        ) if source == &body.statement => Ok((
            p.statement.template_def_stmt.defined_bindings(),
            &body.store_and_infer_result.stored_fact_ids,
        )),
        (
            TemplateDefEnum::HaveObjByExistFactsStmt(source),
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::HaveObjByExistFacts(
                    ExecHaveObjByExistFactsStmtResult::Success(body),
                ),
            )),
        ) if source == &body.statement => Ok((
            p.statement.template_def_stmt.defined_bindings(),
            &body.store_and_infer_result.stored_fact_ids,
        )),
        (
            TemplateDefEnum::HaveObjEqualStmt(source),
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(body)),
            )),
        ) if source == &body.statement => Ok((
            p.statement.template_def_stmt.defined_bindings(),
            &body.store_and_infer_result.stored_fact_ids,
        )),
        (
            TemplateDefEnum::HaveFnEqualStmt(source),
            ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
                ExecHaveFnEqualStmtResult::Success(body),
            )),
        ) if source == &body.statement => Ok((
            p.statement.template_def_stmt.defined_bindings(),
            &body.store_and_infer_result.stored_fact_ids,
        )),
        (
            TemplateDefEnum::HaveByReplacementAxiomStmt(source),
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::HaveByReplacementAxiom(
                    crate::execute::ExecHaveByReplacementAxiomStmtResult::Success(body),
                ),
            )),
        ) if source == &body.statement => Ok((
            p.statement.template_def_stmt.defined_bindings(),
            &body.stored_fact_ids,
        )),
        (
            TemplateDefEnum::HaveFnEqualCaseByCaseStmt(source),
            ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqualCaseByCase(
                ExecHaveFnEqualCaseByCaseStmtResult::Success(body),
            )),
        ) if source == &body.statement => Ok((
            p.statement.template_def_stmt.defined_bindings(),
            &body.store_and_infer_result.stored_fact_ids,
        )),
        (
            TemplateDefEnum::ObtainObjFromExistFact(source),
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::ObtainObjFromExistFact(
                    ExecObtainObjFromExistFactStmtResult::Success(body),
                ),
            )),
        ) if source == &body.statement => Ok((
            p.statement.template_def_stmt.defined_bindings(),
            &body.store_and_infer_result.stored_fact_ids,
        )),
        (
            TemplateDefEnum::ObtainObjFromAtomicFact(source),
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::ObtainObjFromAtomicFact(
                    ExecObtainObjFromAtomicFactStmtResult::Success(body),
                ),
            )),
        ) if source == &body.statement => Ok((
            p.statement.template_def_stmt.defined_bindings(),
            &body.store_and_infer_result.stored_fact_ids,
        )),
        (
            TemplateDefEnum::HaveFnByForallExistUniqueStmt(source),
            ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByForallExistUnique(
                ExecHaveFnByForallExistUniqueStmtResult::Success(body),
            )),
        ) if source == &body.statement => Ok((
            p.statement.template_def_stmt.defined_bindings(),
            &body.stored_fact_ids,
        )),
        (
            TemplateDefEnum::HaveFnByInducStmt(source),
            ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
                ExecHaveFnByInducStmtResult::Success(body),
            )),
        ) if source == &body.statement => Ok((
            p.statement.template_def_stmt.defined_bindings(),
            &body.store_and_infer_result.stored_fact_ids,
        )),
        _ => Err(LeanCompileError::unsupported("Template/BodyCapture")),
    }
}

/// A selected output retains its source identity; the result still has one body.
pub(super) fn template_output<'a>(
    p: &'a ExecDefTemplateStmtSuccessResult,
    name: &str,
) -> Result<(&'a BoundName, &'a [FactId]), LeanCompileError> {
    let (bindings, ids) = template_bindings(p)?;
    let binding = bindings
        .into_iter()
        .find(|p| p.name == name)
        .ok_or_else(|| LeanCompileError::unsupported("Template/OutputName"))?;
    Ok((binding, ids))
}

pub(super) fn template_binding(
    p: &ExecDefTemplateStmtSuccessResult,
) -> Result<(&BoundName, &[FactId]), LeanCompileError> {
    template_output(p, &p.statement.template_name)
}

/// Membership comes from the selected declaration's primary store, not an
/// inferred fact or a later membership of the same object.
pub(super) fn template_output_member_id(
    p: &ExecDefTemplateStmtSuccessResult,
    name: &str,
) -> Result<FactId, LeanCompileError> {
    let (bindings, sources) = template_bindings(p)?;
    let index = bindings
        .iter()
        .position(|p| p.name == name)
        .ok_or_else(|| LeanCompileError::unsupported("Template/OutputName"))?;
    let stores = match p.body.as_ref() {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(body)) => match body {
            ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(p)) => {
                &p.store_and_infer_result
            }
            ExecDefineObjStmtResult::HaveObjInNonemptySet(
                ExecHaveObjInNonemptySetStmtResult::Success(p),
            ) => &p.store_and_infer_result,
            ExecDefineObjStmtResult::HaveObjByExistFacts(
                ExecHaveObjByExistFactsStmtResult::Success(p),
            ) => &p.store_and_infer_result,
            ExecDefineObjStmtResult::ObtainObjFromExistFact(
                ExecObtainObjFromExistFactStmtResult::Success(p),
            ) => &p.store_and_infer_result,
            ExecDefineObjStmtResult::ObtainObjFromAtomicFact(
                ExecObtainObjFromAtomicFactStmtResult::Success(p),
            ) => &p.store_and_infer_result,
            _ => {
                return sources
                    .first()
                    .copied()
                    .ok_or_else(|| LeanCompileError::unsupported("Template/DefinitionMembership"))
            }
        },
        _ => {
            return sources
                .first()
                .copied()
                .ok_or_else(|| LeanCompileError::unsupported("Template/DefinitionMembership"))
        }
    };
    stores
        .store_and_infer_results
        .get(index)
        .map(|s| s.primary_fact_id())
        .ok_or_else(|| LeanCompileError::unsupported("Template/DefinitionMembership"))
}

pub(super) fn template_alias_rhs<'a>(
    p: &'a ExecDefTemplateStmtSuccessResult,
    name: &str,
) -> Result<&'a Obj, LeanCompileError> {
    let body = alias_body(p)?;
    let binding = template_output(p, name)?.0;
    let ids = body.statement.param_def.ordered_param_ids();
    if ids.len() != body.statement.objs_equal_to.len() {
        return Err(LeanCompileError::unsupported("Template/AliasArity"));
    }
    let index = ids
        .iter()
        .position(|id| *id == binding.id)
        .ok_or_else(|| LeanCompileError::unsupported("Template/OutputName"))?;
    Ok(&body.statement.objs_equal_to[index])
}

/// Simultaneously instantiate the header and every output in the same body.
pub(super) fn template_substitution(
    p: &ExecDefTemplateStmtSuccessResult,
    instance: &InstantiatedTemplateObj,
) -> Result<HashMap<IdentifierId, Obj>, LeanCompileError> {
    template_output(p, instance.template_name.local_name())?;
    let ids = p.statement.template_arg_def.ordered_param_ids();
    if ids.len() != instance.args.len() {
        return Err(LeanCompileError::unsupported("Template/FunctionArguments"));
    }
    let mut substitution: HashMap<_, _> =
        ids.into_iter().zip(instance.args.iter().cloned()).collect();
    for binding in template_bindings(p)?.0 {
        let mut sibling = instance.clone();
        match &mut sibling.template_name {
            AtomicName::Plain { name }
            | AtomicName::WithExportFileId { name, .. }
            | AtomicName::WithModAndExportFileId { name, .. } => *name = binding.name.clone(),
        }
        substitution.insert(binding.id, Obj::InstantiatedTemplateObj(sibling));
    }
    Ok(substitution)
}

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn validate_template_function(
        &self,
        instance: &InstantiatedTemplateObj,
        signature: &FnSet,
        function: Option<&AnonymousFn>,
        position: &SourcePosition<'_>,
    ) -> Result<(), LeanCompileError> {
        let (p, _, _) = position.visible_template(&instance.template_name)?;
        let original = self.template_function_signature(instance, position)?;
        let ids = p.statement.template_arg_def.ordered_param_ids();
        if ids.len() != instance.args.len() {
            return Err(LeanCompileError::unsupported("Template/FunctionArguments"));
        }
        let substitution = template_substitution(p, instance)?;
        if !instantiated_object_matches(
            &Obj::FunctionSpace(FunctionSpace::FnSet(original)),
            &Obj::FunctionSpace(FunctionSpace::FnSet(signature.clone())),
            &substitution,
        ) {
            return Err(LeanCompileError::unsupported(
                "Template/FunctionSubstitution",
            ));
        }
        if let Some(function) = function {
            let TemplateDefEnum::HaveFnEqualStmt(source) = &p.statement.template_def_stmt else {
                return Err(LeanCompileError::unsupported("Template/FormulaDeclaration"));
            };
            if !instantiated_object_matches(
                &Obj::FunctionSpace(FunctionSpace::AnonymousFn(
                    source.equal_to_anonymous_fn.clone(),
                )),
                &Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.clone())),
                &substitution,
            ) {
                return Err(LeanCompileError::unsupported(
                    "Template/FunctionSubstitution",
                ));
            }
        }
        Ok(())
    }

    pub(in crate::compile_to_lean) fn compile_template_raw_value(
        &self,
        instance: &InstantiatedTemplateObj,
        position: &SourcePosition<'_>,
        bindings: &HashMap<IdentifierId, String>,
    ) -> Result<String, LeanCompileError> {
        let (p, producer, _) = position.visible_template(&instance.template_name)?;
        let (binding, _) = template_output(p, instance.template_name.local_name())?;
        let output_index = template_bindings(p)?
            .0
            .iter()
            .position(|p| p.id == binding.id)
            .unwrap();
        let ids = p.statement.template_arg_def.ordered_param_ids();
        if ids.len() != instance.args.len() {
            return Err(LeanCompileError::unsupported("Template/FunctionArguments"));
        }
        let mut captured = HashMap::new();
        for (id, argument) in ids.into_iter().zip(&instance.args) {
            captured.insert(
                id,
                self.compile_function_raw_expression_bound(argument, position, bindings)?,
            );
        }
        let scope = SourcePosition::new(Some(&producer), SourceOwner::Template(p), usize::MAX);
        match &p.statement.template_def_stmt {
            TemplateDefEnum::HaveObjInNonemptySetStmt(body) => {
                let mut values = Vec::new();
                for (parameter, kind) in body
                    .param_def
                    .groups
                    .iter()
                    .flat_map(|g| g.params.iter().map(|p| (p, &g.param_type)))
                    .take(output_index + 1)
                {
                    let value = match kind {
                        ParamType::Obj(carrier) => {
                            let carrier = self.compile_function_raw_expression_bound(carrier, &scope, &captured)?;
                            format!("(Litex.obtainedValue (M := M) (fun (_member : Litex.Obj (M := M) M.Value) => M.mem (Litex.denote _member) {carrier}))")
                        }
                        ParamType::Set(_) => "(M.standard Litex.StandardSetValue.complex)".into(),
                        kind @ (ParamType::NonemptySet(_) | ParamType::FiniteSet(_)) =>
                            format!("(Litex.obtainedValue (M := M) (fun (_member : Litex.Obj (M := M) M.Value) => {} _member))", set_kind_predicate(kind).unwrap()),
                    };
                    if output_index == 0 {
                        return Ok(value);
                    }
                    let name = format!("_template_value_i{}", parameter.id.value());
                    values.push(format!("let {name} := {value}"));
                    captured.insert(parameter.id, name);
                }
                Ok(format!(
                    "({}; {})",
                    values.join("; "),
                    captured[&binding.id]
                ))
            }
            TemplateDefEnum::HaveFnEqualStmt(body) => {
                self.compile_function_literal_value(&body.equal_to_anonymous_fn, &scope, &captured)
            }
            TemplateDefEnum::HaveObjEqualStmt(_) => self.compile_function_raw_expression_bound(
                template_alias_rhs(p, &binding.name)?,
                &scope,
                &captured,
            ),
            TemplateDefEnum::HaveFnEqualCaseByCaseStmt(body) => {
                self.compile_template_piecewise_value(body, &scope, &captured)
            }
            TemplateDefEnum::HaveByReplacementAxiomStmt(_) => {
                let body = super::compile_replacement_result::replacement_statement(&p.body)
                    .ok_or_else(|| LeanCompileError::unsupported("Template/BodyCapture"))?;
                self.compile_replacement_raw_value(body, &scope, &captured)
            }
            TemplateDefEnum::HaveFnByInducStmt(_) => {
                let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
                    ExecHaveFnByInducStmtResult::Success(body),
                )) = p.body.as_ref()
                else {
                    return Err(LeanCompileError::unsupported("Template/BodyCapture"));
                };
                self.compile_recursive_raw_value(body, &scope, &captured)
            }
            TemplateDefEnum::HaveFnByForallExistUniqueStmt(_) => {
                let ExecStmtResult::Definition(
                    ExecDefinitionStmtResult::HaveFnByForallExistUnique(
                        ExecHaveFnByForallExistUniqueStmtResult::Success(body),
                    ),
                ) = p.body.as_ref()
                else {
                    return Err(LeanCompileError::unsupported("Template/BodyCapture"));
                };
                self.compile_selected_function_raw_value(body, &scope, &captured)
            }
            TemplateDefEnum::ObtainObjFromExistFact(_)
            | TemplateDefEnum::ObtainObjFromAtomicFact(_)
            | TemplateDefEnum::HaveObjByExistFactsStmt(_) => {
                let object = Obj::InstantiatedTemplateObj(instance.clone());
                let mut free = std::collections::HashSet::new();
                crate::instantiate::collect_free_plain_ids(
                    &object,
                    &std::collections::HashSet::new(),
                    &mut free,
                );
                if free.iter().any(|id| bindings.contains_key(id)) {
                    return self.compile_template_obtain_raw_value(
                        &p.body,
                        output_index,
                        &scope,
                        &captured,
                    );
                }
                Ok(format!(
                    "(Litex.denote {})",
                    self.compile_object_reference(&object, position)?
                ))
            }
            _ => Err(LeanCompileError::unsupported("Template/RawBody")),
        }
    }

    pub(in crate::compile_to_lean) fn compile_template_search_reference(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        let Some((source, expansions, producer)) = position.template_search_conversion(object)
        else {
            return Ok(None);
        };
        self.validate_template_membership_expansions(source, expansions, &producer)?;
        Ok(Some(self.compile_object_reference(&source.set, &producer)?))
    }

    pub(in crate::compile_to_lean) fn compile_template_inferred_reference(
        &self,
        object: &Obj,
        store: &StoreFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        let Some((conversion, index, producer)) = position.template_inference_conversion(store)
        else {
            return Ok(None);
        };
        let expansion = conversion
            .expansions
            .get(index)
            .ok_or_else(|| LeanCompileError::unsupported("TemplateInference/Stores"))?;
        if object.ir() != expansion.set.ir() {
            return Ok(None);
        }
        self.validate_store(
            store,
            &Fact::AtomicFact(AtomicFact::InFact(expansion.clone())),
        )?;
        let source = self.resolve_fact(conversion.source_fact_id, &producer)?;
        let Fact::AtomicFact(AtomicFact::InFact(source)) = &source else {
            return Err(LeanCompileError::unsupported("TemplateInference/Seed"));
        };
        self.validate_template_membership_expansions(source, &conversion.expansions, &producer)?;
        Ok(Some(self.compile_object_reference(&source.set, &producer)?))
    }

    fn validate_template_membership_expansions(
        &self,
        member: &InFact,
        expansions: &[InFact],
        position: &SourcePosition<'_>,
    ) -> Result<(), LeanCompileError> {
        if expansions.is_empty() {
            return Err(LeanCompileError::unsupported(
                "TemplateMembership/Expansions",
            ));
        }
        let mut carrier = &member.set;
        let mut seen = std::collections::HashSet::new();
        let mut ids = std::collections::HashSet::from([member.fact_id]);
        for expansion in expansions {
            let Obj::InstantiatedTemplateObj(instance) = carrier else {
                return Err(LeanCompileError::unsupported("TemplateMembership/Carrier"));
            };
            if !seen.insert(carrier.ir()) || !ids.insert(expansion.fact_id) {
                return Err(LeanCompileError::unsupported(
                    "TemplateMembership/RepeatedStage",
                ));
            }
            let (template, _, _) = position.visible_template(&instance.template_name)?;
            let rhs = template_alias_rhs(template, instance.template_name.local_name())?;
            let substitution = template_substitution(template, instance)?;
            if expansion.element != member.element
                || !instantiated_object_matches(rhs, &expansion.set, &substitution)
            {
                return Err(LeanCompileError::unsupported(
                    "TemplateMembership/ExpandedSubject",
                ));
            }
            carrier = &expansion.set;
        }
        Ok(())
    }

    pub(in crate::compile_to_lean) fn compile_template_membership_inference(
        &self,
        proof: &crate::store_fact_and_infer::InferTemplateMembershipResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let Fact::AtomicFact(AtomicFact::InFact(member)) = seed else {
            return Err(LeanCompileError::unsupported("TemplateInference/Seed"));
        };
        if member.fact_id != proof.source_fact_id || proof.stores.len() != proof.expansions.len() {
            return Err(LeanCompileError::unsupported("TemplateInference/Stores"));
        }
        self.validate_template_membership_expansions(member, &proof.expansions, position)?;
        if proof.native_rules.iter().any(|rule| {
            matches!(
                rule,
                crate::store_fact_and_infer::InferInFactResult::Template(_)
            )
        }) {
            return Err(LeanCompileError::unsupported(
                "TemplateInference/RecursivePass",
            ));
        }
        let scope = SourcePosition::new(Some(position), SourceOwner::TemplateInference(proof), 0);
        let mut declarations = Vec::new();
        let mut current = compiled.clone();
        for (index, (expansion, captured)) in proof.expansions.iter().zip(&proof.stores).enumerate()
        {
            let fact = Fact::AtomicFact(AtomicFact::InFact(expansion.clone()));
            self.validate_store(&captured.store, &fact)?;
            let prior = SourcePosition {
                before: index,
                ..scope
            };
            let formed = SourcePosition::new(
                Some(&prior),
                SourceOwner::InferredStore(&captured.store),
                usize::MAX,
            );
            let proposition = self.fact_proposition(&fact, &formed)?;
            let term = format!("(show {proposition} from {})", current.1);
            declarations.push(self.emit_internal_fact(
                &fact,
                &(proposition.clone(), term),
                &formed,
            )?);
            let name = format!("h_{}", expansion.fact_id.value());
            let reference = if prior.is_local() {
                name
            } else {
                self.context_application(&name, &prior)
            };
            current = (proposition, reference);
        }
        let native = Fact::AtomicFact(AtomicFact::InFact(proof.expansions.last().unwrap().clone()));
        let complete = SourcePosition {
            before: proof.stores.len(),
            ..scope
        };
        declarations.extend(self.compile_membership_inference_rules(
            &proof.native_rules,
            &native,
            &current,
            &complete,
        )?);
        Ok(declarations)
    }

    pub(in crate::compile_to_lean) fn compile_template_membership(
        &self,
        goal: &AtomicFact,
        proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::TemplateMembershipProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::InFact(member) = goal else {
            return Err(LeanCompileError::unsupported("TemplateMembership/Family"));
        };
        self.validate_template_membership_expansions(member, &proof.expansions, position)?;
        let prior = position.atomic_search_prior(0)?;
        let residual_position = SourcePosition::new(
            Some(&prior),
            SourceOwner::AtomicSearch(&proof.residual),
            usize::MAX,
        );
        let residual = AtomicFact::InFact(proof.expansions.last().unwrap().clone());
        let compiled = self.compile_atomic_searched_proof(
            &residual,
            &proof.residual,
            None,
            &residual_position,
        )?;
        Ok(format!(
            "(show {} from {compiled})",
            self.atomic_proposition(goal, position)?
        ))
    }

    pub(super) fn compile_template_equality(
        &self,
        fact: &EqualFact,
        proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_template::result::EqualitySearchProofByTemplateObjectDefinition,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_template::result::EqualitySearchProofByTemplateObjectDefinition;
        if let EqualitySearchProofByTemplateObjectDefinition::HaveFnEqualApplication(p) = proof {
            return self.compile_normalized_function_equality(
                fact,
                &p.normalization,
                &p.residual_equal,
                position,
            );
        }
        if matches!(
            proof,
            EqualitySearchProofByTemplateObjectDefinition::HaveFnEqualCaseByCaseApplication(_)
                | EqualitySearchProofByTemplateObjectDefinition::HaveFnByInducApplication(_)
        ) {
            return self.compile_template_case_unfold(fact, proof, position);
        }
        let EqualitySearchProofByTemplateObjectDefinition::HaveObjEqual(p) = proof else {
            return Err(LeanCompileError::unsupported("Template/FunctionUnfold"));
        };
        let Fact::AtomicFact(AtomicFact::EqualFact(residual)) = source_subject(&p.residual_equal)?
        else {
            return Err(LeanCompileError::unsupported("Template/Residual"));
        };
        let (instance, reversed) = match (&fact.left, &fact.right) {
            (Obj::InstantiatedTemplateObj(i), other) if other.ir() == residual.right.ir() => {
                (i, false)
            }
            (other, Obj::InstantiatedTemplateObj(i)) if other.ir() == residual.right.ir() => {
                (i, true)
            }
            _ => return Err(LeanCompileError::unsupported("Template/UnfoldSubject")),
        };
        let (template, _, _) = position.visible_template(&instance.template_name)?;
        let rhs = template_alias_rhs(template, instance.template_name.local_name())?;
        let subst = template_substitution(template, instance)?;
        if p.expanded_rhs.ir() != residual.left.ir()
            || !instantiated_object_matches(rhs, &p.expanded_rhs, &subst)
        {
            return Err(LeanCompileError::unsupported("Template/ExpandedSubject"));
        }
        let (_, residual) = self.compile_verify(&p.residual_equal, position)?;
        Ok(format!(
            "(show {} = {} from {})",
            self.compile_normalization_value(&fact.left, position)?,
            self.compile_normalization_value(&fact.right, position)?,
            if reversed {
                format!("({residual}).symm")
            } else {
                residual
            }
        ))
    }

    pub(super) fn compile_template_statement(
        &self,
        result: &ExecDefTemplateStmtResult,
        position: &SourcePosition<'_>,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        if local {
            return Err(LeanCompileError::unsupported("Template/LocalDeclaration"));
        }
        let ExecDefTemplateStmtResult::Success(p) = result else {
            return Err(LeanCompileError::unsupported("Template/Failed"));
        };
        let (bindings, source_ids) = template_bindings(p)?;
        let scope = SourcePosition::new(Some(position), SourceOwner::Template(p), 0);
        let domains = p
            .statement
            .template_arg_dom
            .iter()
            .cloned()
            .map(crate::instantiate::quantifier_free_fact_to_fact)
            .collect::<Vec<_>>();
        let (binders, introductions, mut definitions) = self.compile_quantified_head(
            &p.statement.template_arg_def,
            &domains,
            &p.introduced_params,
            &p.assumed_dom_facts,
            &scope,
        )?;
        let head = p.statement.template_arg_def.ordered_param_ids().len() + domains.len();
        let prior = SourcePosition {
            before: head,
            ..scope
        };
        definitions.push(self.compile_statement_in_scope(&p.body, &prior, 1, true)?);
        let complete = SourcePosition {
            before: head + 1,
            ..scope
        };
        let context = self.context_header(position)?;
        let mut declarations = Vec::new();
        for binding in &bindings {
            let value = self.compile_object_reference(
                &Obj::Identifier(IdentifierObj::from_bound_name(binding)),
                &complete,
            )?;
            let object_name = format!("_template_i{}", binding.id.value());
            let (carrier, result) = match p.statement.template_def_stmt {
                TemplateDefEnum::HaveFnEqualStmt(_) => ("(Litex.FormulaFn M)", value),
                TemplateDefEnum::HaveFnByInducStmt(_) => {
                    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
                        ExecHaveFnByInducStmtResult::Success(body),
                    )) = p.body.as_ref()
                    else {
                        return Err(LeanCompileError::unsupported("Template/BodyCapture"));
                    };
                    let carrier = if self.recursive_uses_nat_representation(body, &complete)? {
                        "(Litex.RecursiveNatFn M)"
                    } else {
                        "(Litex.RecursiveFn M)"
                    };
                    (carrier, value)
                }
                TemplateDefEnum::HaveFnEqualCaseByCaseStmt(_) => ("(Litex.PiecewiseFn M)", value),
                TemplateDefEnum::HaveFnByForallExistUniqueStmt(_) => {
                    ("(Litex.SelectedFn M)", value)
                }
                _ => (
                    "M.Value",
                    format!("Litex.semanticObject (Litex.denote {value}) (Litex.isSet {value})"),
                ),
            };
            // Body results can include universal facts with their own host levels,
            // such as uniqueness or case equations. Every result is compiled above;
            // retain its proof here only when this particular declaration uses it.
            // Each publication below closes its own original lexical dependencies.
            let value_body = self.scope_proposition(result, &definitions);
            declarations.push(format!("noncomputable def {object_name}{context} {} : Litex.Obj (M := M) {carrier} := {value_body}", binders.join(" ")));
        }
        if p.definition_facts.len() != source_ids.len()
            || p.definition_facts
                .iter()
                .zip(source_ids)
                .any(|(p, id)| p.source_fact_id != *id)
        {
            return Err(LeanCompileError::unsupported("Template/PublicationCapture"));
        }
        let instance = InstantiatedTemplateObj {
            template_name: AtomicName::Plain {
                name: p.statement.template_name.clone(),
            },
            args: p
                .statement
                .template_arg_def
                .groups
                .iter()
                .flat_map(|g| &g.params)
                .map(|a| Obj::Identifier(IdentifierObj::from_bound_name(a)))
                .collect(),
        };
        if matches!(
            p.statement.template_def_stmt,
            TemplateDefEnum::ObtainObjFromExistFact(_)
                | TemplateDefEnum::ObtainObjFromAtomicFact(_)
                | TemplateDefEnum::HaveObjInNonemptySetStmt(_)
                | TemplateDefEnum::HaveObjByExistFactsStmt(_)
        ) {
            for binding in &bindings {
                let member =
                    self.resolve_fact(template_output_member_id(p, &binding.name)?, &complete)?;
                if matches!(
                    member,
                    Fact::AtomicFact(AtomicFact::InFact(InFact {
                        set: Obj::FunctionSpace(FunctionSpace::FnSet(_)),
                        ..
                    }))
                ) {
                    let signature =
                        self.template_body_function_signature(p, &binding.name, &complete)?;
                    let term = self.compile_fn_signature(&signature, &complete)?;
                    declarations.push(format!("noncomputable def _template_signature_i{}{context} {} : Litex.FunctionSignature M := by\n  {}\n  exact {term}", binding.id.value(), binders.join(" "), definitions.join("\n").replace('\n', "\n  ")));
                }
            }
        }
        let substitution = template_substitution(p, &instance)?;
        for published in &p.definition_facts {
            let source = self.resolve_fact(published.source_fact_id, &complete)?;
            let StoreFactResult::ForallFact(stored) = &published.store_and_infer.store else {
                return Err(LeanCompileError::unsupported("Template/PublicationShape"));
            };
            let fact = &stored.fact;
            let parameter_binders = binders.len() - domains.len();
            let parameter_introductions = introductions.len() - domains.len();
            let (body_proposition, body_arguments) = if let Fact::ForallFact(source) = &source {
                self.compile_template_forall_publication(
                    p,
                    source,
                    fact,
                    &substitution,
                    &binders[parameter_binders..],
                    &complete,
                )?
            } else {
                if fact.typed_parameters != p.statement.template_arg_def
                    || fact.dom_facts != domains
                    || fact.then_facts.len() != 1
                {
                    return Err(LeanCompileError::unsupported("Template/PublicationHeader"));
                }
                let conclusion: Fact = fact.then_facts[0].clone().into();
                if !instantiated_fact_matches(&source, &conclusion, &substitution) {
                    return Err(LeanCompileError::unsupported("Template/PublicationSubject"));
                }
                let mut inferred_source = false;
                if let Fact::AtomicFact(atomic) = &source {
                    for object in atomic_fact_args_ref(atomic) {
                        if complete
                            .with_visible_inferred_subject_filter(object, &mut |store, _| {
                                Ok((store.primary_fact_id() == published.source_fact_id)
                                    .then_some(true))
                            })?
                            .is_some()
                        {
                            inferred_source = true;
                            break;
                        }
                    }
                }
                let proposition = if bindings.len() > 1 || inferred_source {
                    // The body already checked constructors involving sibling
                    // outputs. Render that meaning with all output projections;
                    // the substituted publication has no second WD tree.
                    let values = self.template_publication_values(p, &substitution, &complete)?;
                    self.compile_function_raw_predicate(&source, &complete, &values)?
                } else {
                    self.fact_proposition(&conclusion, &complete)?
                };
                (proposition, Vec::new())
            };
            self.validate_store(
                &published.store_and_infer.store,
                &Fact::ForallFact(fact.clone()),
            )?;
            let proposition = self.scope_proposition(body_proposition, &definitions);
            let universal = matches!(source, Fact::ForallFact(_));
            let outer_binders = if universal {
                &binders[..parameter_binders]
            } else {
                &binders[..]
            };
            let proposition = if outer_binders.is_empty() {
                proposition
            } else {
                format!("∀ {}, {proposition}", outer_binders.join(" "))
            };
            let mut proof = Vec::new();
            let mut proof_introductions = introductions[..parameter_introductions].to_vec();
            proof_introductions.extend(body_arguments.clone());
            proof_introductions.extend_from_slice(&introductions[parameter_introductions..]);
            if !proof_introductions.is_empty() {
                proof.push(format!("intro {}", proof_introductions.join(" ")));
            }
            let source_reference = complete
                .visible_fact(published.source_fact_id, &self.runtime)?
                .1;
            let reference = self.compile_local_recursive_equation_citation(
                &source,
                source_reference.clone(),
                &complete,
            )?;
            // Preserve the body's polymorphic parameters when returning a
            // universal proof, rather than inserting unresolved implicit hosts.
            let reference = if universal && reference != source_reference {
                format!(
                    "(let _published_source := {reference}; @_published_source {})",
                    body_arguments.join(" ")
                )
            } else if universal {
                format!("(@{reference} {})", body_arguments.join(" "))
            } else {
                reference
            };
            proof.push(format!(
                "exact {}",
                self.scope_proposition(reference, &definitions)
            ));
            let name = format!("h_{}", fact.fact_id.value());
            declarations.push(format!(
                "theorem {name}{context} : {proposition} := by\n  {}",
                proof.join("\n").replace('\n', "\n  ")
            ));
            // Publication inference remains checked even when it emits no new facts.
            let published_position = SourcePosition {
                before: p.definition_facts.len(),
                ..*position
            };
            declarations.extend(self.compile_stored_inferences(
                &published.store_and_infer,
                &Fact::ForallFact(fact.clone()),
                &(proposition, self.context_application(&name, position)),
                &published_position,
            )?);
        }
        Ok(declarations.join("\n\n"))
    }

    pub(super) fn template_self_reference(
        &self,
        instance: &InstantiatedTemplateObj,
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        let mut cursor = Some(position);
        while let Some(scope) = cursor {
            if let SourceOwner::Template(p) = scope.owner {
                let parameters = p
                    .statement
                    .template_arg_def
                    .groups
                    .iter()
                    .flat_map(|g| &g.params)
                    .collect::<Vec<_>>();
                if p.statement
                    .template_def_stmt
                    .defined_bindings()
                    .iter()
                    .any(|p| p.name == instance.template_name.local_name())
                    && parameters.len() == instance.args.len()
                    && parameters.iter().zip(&instance.args).all(|(p, a)| {
                        a.ir() == Obj::Identifier(IdentifierObj::from_bound_name(p)).ir()
                    })
                {
                    let binding = template_output(p, instance.template_name.local_name())?
                        .0
                        .id;
                    let base = self
                        .context_application(&format!("_template_i{}", binding.value()), position);
                    let mut args = parameters
                        .iter()
                        .zip(&p.introduced_params.defined_params.store_and_infer_results)
                        .flat_map(|(p, s)| {
                            [
                                format!("_value_i{}", p.id.value()),
                                format!("h_{}", s.primary_fact_id().value()),
                            ]
                        })
                        .collect::<Vec<_>>();
                    args.extend(
                        p.assumed_dom_facts
                            .iter()
                            .map(|d| format!("h_{}", d.store_and_infer.primary_fact_id().value())),
                    );
                    return Ok(Some(format!("({base} {})", args.join(" "))));
                }
            }
            cursor = scope.parent;
        }
        Ok(None)
    }

    pub(super) fn compile_template_wd(
        &self,
        instance: &InstantiatedTemplateObj,
        evidence: &InstantiatedTemplateObjObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (p, producer, _) = position.visible_template(&instance.template_name)?;
        let (binding, _) = template_output(p, instance.template_name.local_name())?;
        let args = self.compile_template_arguments(instance, evidence, position)?;
        let base =
            self.context_application(&format!("_template_i{}", binding.id.value()), &producer);
        Ok(format!("({base} {})", args.join(" ")))
    }

    /// Borrow the same ordered instance arguments for its object and published facts.
    pub(super) fn compile_template_arguments(
        &self,
        instance: &InstantiatedTemplateObj,
        evidence: &InstantiatedTemplateObjObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (p, producer, _) = position.visible_template(&instance.template_name)?;
        template_output(p, instance.template_name.local_name())?;
        let ids = p.statement.template_arg_def.ordered_param_ids();
        let n = ids.len();
        if instance.args.len() != n
            || evidence.child_obj_well_defined.len() != n
            || evidence.requirement_fact_verified.len() != n + p.assumed_dom_facts.len()
        {
            return Err(LeanCompileError::unsupported("Template/InstanceStages"));
        }
        let subst = ids
            .into_iter()
            .zip(instance.args.iter().cloned())
            .collect::<HashMap<_, _>>();
        let mut values = Vec::new();
        for (index, (arg, wd)) in instance
            .args
            .iter()
            .zip(&evidence.child_obj_well_defined)
            .enumerate()
        {
            ensure_object(arg, wd)?;
            values.push(self.compile_wd(
                wd,
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?);
        }
        let header_scope =
            SourcePosition::new(Some(&producer), SourceOwner::Template(p), usize::MAX);
        let source_ids = p
            .introduced_params
            .defined_params
            .store_and_infer_results
            .iter()
            .map(|s| s.primary_fact_id())
            .chain(
                p.assumed_dom_facts
                    .iter()
                    .map(|s| s.store_and_infer.primary_fact_id()),
            );
        let mut checks = Vec::new();
        for (index, (id, checked)) in source_ids
            .zip(&evidence.requirement_fact_verified)
            .enumerate()
        {
            let source = self.resolve_fact(id, &header_scope)?;
            if !instantiated_fact_matches(&source, &source_subject(checked)?, &subst) {
                return Err(LeanCompileError::unsupported("Template/RequirementSubject"));
            }
            checks.push(
                self.compile_verify(
                    checked,
                    &SourcePosition {
                        before: n + index,
                        ..*position
                    },
                )?
                .1,
            );
        }
        let mut args = values
            .iter()
            .zip(&checks)
            .flat_map(|(v, h)| [v.clone(), h.clone()])
            .collect::<Vec<_>>();
        args.extend(checks.into_iter().skip(n));
        Ok(args)
    }
}
