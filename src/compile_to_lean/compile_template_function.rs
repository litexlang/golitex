use super::compile_template_stmt_result::{
    template_bindings, template_output, template_output_member_id,
};
use super::helper::{instantiated_fact_matches, set_kind_predicate};
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TemplateDefEnum;
use crate::prelude::*;
use std::collections::HashMap;

pub(super) fn validate_template_forall_shape(
    declaration: &crate::execute::ExecDefTemplateStmtSuccessResult,
    source: &ForallFact,
    published: &ForallFact,
    substitution: &HashMap<IdentifierId, Obj>,
) -> Result<(), LeanCompileError> {
    let header = &declaration.statement.template_arg_def.groups;
    let domains = declaration
        .statement
        .template_arg_dom
        .iter()
        .cloned()
        .map(crate::instantiate::quantifier_free_fact_to_fact)
        .collect::<Vec<_>>();
    if !published.typed_parameters.groups.starts_with(header)
        || !published.dom_facts.starts_with(&domains)
    {
        return Err(LeanCompileError::unsupported(
            "Template/UniversalPublicationHeader",
        ));
    }
    let mut residual = published.clone();
    residual.typed_parameters.groups.drain(..header.len());
    residual.dom_facts.drain(..domains.len());
    if !instantiated_fact_matches(
        &Fact::ForallFact(source.clone()),
        &Fact::ForallFact(residual),
        substitution,
    ) {
        return Err(LeanCompileError::unsupported(
            "Template/UniversalPublicationSubject",
        ));
    }
    Ok(())
}

impl LitexToLeanCompiler {
    pub(super) fn compile_template_piecewise_value(
        &self,
        source: &crate::ast::stmt::HaveFnEqualCaseByCaseStmt,
        position: &SourcePosition<'_>,
        outer: &HashMap<IdentifierId, String>,
    ) -> Result<String, LeanCompileError> {
        let signature = FnSet {
            set_bound_parameters: source.fn_set_clause.set_bound_parameters.clone(),
            dom_facts: source.fn_set_clause.dom_facts.clone(),
            ret_set: Box::new(source.fn_set_clause.ret_set.clone()),
        };
        let (domain, output, _) =
            self.compile_function_signature_value_parts(&signature, position, outer)?;
        let values = self.compile_function_packed_values(&signature, "_template_input")?;
        let mut bindings = outer.clone();
        for (parameter, value) in signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|group| &group.params)
            .zip(values)
        {
            if bindings.insert(parameter.id, value).is_some() {
                return Err(LeanCompileError::unsupported("Template/CaseBinderIdentity"));
            }
        }
        let branches = source.cases.iter().zip(&source.equal_tos).map(|(guard, body)| {
            Ok(format!("(⟨(fun (_template_input : M.Value) => {}), (fun (_template_input : M.Value) => {})⟩ : Litex.FunctionBranch M)",
                self.compile_function_raw_predicate(&crate::ast::fact::and_chain_as_fact(guard), position, &bindings)?,
                self.compile_function_raw_expression_bound(body, position, &bindings)?))
        }).collect::<Result<Vec<_>, LeanCompileError>>()?;
        Ok(format!("(Litex.FunctionSemantics.graphValue (M := M) {domain} {output} (Litex.piecewiseValue [{}]))", branches.join(", ")))
    }

    /// Read the function carrier actually published by the checked body.
    pub(super) fn template_function_signature(
        &self,
        instance: &InstantiatedTemplateObj,
        position: &SourcePosition<'_>,
    ) -> Result<FnSet, LeanCompileError> {
        let (declaration, producer, _) = position.visible_template(&instance.template_name)?;
        let complete = SourcePosition::new(
            Some(&producer),
            SourceOwner::Template(declaration),
            usize::MAX,
        );
        self.template_body_function_signature(
            declaration,
            instance.template_name.local_name(),
            &complete,
        )
    }

    pub(super) fn template_body_function_signature(
        &self,
        declaration: &crate::execute::ExecDefTemplateStmtSuccessResult,
        name: &str,
        complete: &SourcePosition<'_>,
    ) -> Result<FnSet, LeanCompileError> {
        let binding = template_output(declaration, name)?.0;
        let primary = template_output_member_id(declaration, name)?;
        let Fact::AtomicFact(AtomicFact::InFact(member)) = self.resolve_fact(primary, complete)?
        else {
            return Err(LeanCompileError::unsupported("Template/FunctionMembership"));
        };
        if member.element != Obj::Identifier(IdentifierObj::from_bound_name(binding)) {
            return Err(LeanCompileError::unsupported(
                "Template/FunctionMemberSubject",
            ));
        }
        let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = member.set else {
            return Err(LeanCompileError::unsupported("Template/FunctionCarrier"));
        };
        Ok(signature)
    }

    pub(super) fn template_call_interface(
        &self,
        instance: &InstantiatedTemplateObj,
        term: &str,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let (declaration, producer, _) = position.visible_template(&instance.template_name)?;
        let binding = template_output(declaration, instance.template_name.local_name())?.0;
        let member_id = template_output_member_id(declaration, &binding.name)?;
        let theorem = match declaration.statement.template_def_stmt {
            TemplateDefEnum::HaveFnEqualStmt(_) => Some("Litex.formulaFnInFnSet"),
            TemplateDefEnum::HaveFnByInducStmt(_) => {
                let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
                    crate::execute::ExecHaveFnByInducStmtResult::Success(body),
                )) = declaration.body.as_ref()
                else {
                    return Err(LeanCompileError::unsupported("Template/RecursiveBody"));
                };
                let head = declaration
                    .statement
                    .template_arg_def
                    .ordered_param_ids()
                    .len()
                    + declaration.statement.template_arg_dom.len();
                let ready =
                    SourcePosition::new(Some(&producer), SourceOwner::Template(declaration), head);
                Some(if self.recursive_uses_nat_representation(body, &ready)? {
                    "Litex.recursiveNatFnInFnSet"
                } else {
                    "Litex.recursiveFnInFnSet"
                })
            }
            TemplateDefEnum::HaveFnEqualCaseByCaseStmt(_) => Some("Litex.piecewiseFnInFnSet"),
            TemplateDefEnum::HaveFnByForallExistUniqueStmt(_) => Some("Litex.selectedFnInFnSet"),
            _ => None,
        };
        if let Some(theorem) = theorem {
            return Ok((
                format!("({term}).val.signature"),
                format!("({theorem} {term})"),
            ));
        }
        self.template_function_signature(instance, position)?;
        let publication = declaration
            .definition_facts
            .iter()
            .find(|p| p.source_fact_id == member_id)
            .ok_or_else(|| LeanCompileError::unsupported("Template/FunctionMemberPublication"))?;
        let (_, member) =
            position.visible_fact(publication.store_and_infer.primary_fact_id(), &self.runtime)?;
        let object = Obj::InstantiatedTemplateObj(instance.clone());
        position
            .with_visible_wd(&object, &mut |wd, site| {
                let DetailedObjWellDefinedProof::ByDef {
                    proof: ObjWellDefinedProofByDef::InstantiatedTemplateObj(evidence),
                    ..
                } = wd.detailed_ref()
                else {
                    return Err(LeanCompileError::unsupported("Template/FunctionInstanceWD"));
                };
                let scope = SourcePosition::new(Some(site), SourceOwner::WD(wd), 0);
                let args = self
                    .compile_template_arguments(instance, evidence, &scope)?
                    .join(" ");
                let signature = self.context_application(
                    &format!("_template_signature_i{}", binding.id.value()),
                    &producer,
                );
                Ok((
                    format!("({signature} {args})"),
                    format!("({member} {args})"),
                ))
            })?
            .ok_or_else(|| LeanCompileError::unsupported("Template/FunctionInstanceWD"))
    }

    pub(super) fn template_publication_values(
        &self,
        declaration: &crate::execute::ExecDefTemplateStmtSuccessResult,
        substitution: &HashMap<IdentifierId, Obj>,
        position: &SourcePosition<'_>,
    ) -> Result<HashMap<IdentifierId, String>, LeanCompileError> {
        let mut raw = HashMap::new();
        for binding in template_bindings(declaration)?.0 {
            let Obj::InstantiatedTemplateObj(instance) = &substitution[&binding.id] else {
                return Err(LeanCompileError::unsupported(
                    "Template/PublicationInstance",
                ));
            };
            let object = self
                .template_self_reference(instance, position)?
                .ok_or_else(|| LeanCompileError::unsupported("Template/PublicationInstance"))?;
            // Replacement elimination binds a member of the output before the
            // template guards. Its value is fixed independently of those proofs.
            let value = if let Some(body) =
                super::compile_replacement_result::replacement_statement(&declaration.body)
            {
                self.compile_replacement_raw_value(body, position, &HashMap::new())?
            } else {
                format!("(Litex.denote {object})")
            };
            raw.insert(binding.id, value);
        }
        Ok(raw)
    }

    /// The Runtime prepends the template header to a body's universal store.
    /// Validate that flattening, then render the original binder types and body.
    pub(super) fn compile_template_forall_publication(
        &self,
        declaration: &crate::execute::ExecDefTemplateStmtSuccessResult,
        source: &ForallFact,
        published: &ForallFact,
        substitution: &HashMap<IdentifierId, Obj>,
        template_guards: &[String],
        position: &SourcePosition<'_>,
    ) -> Result<(String, Vec<String>), LeanCompileError> {
        validate_template_forall_shape(declaration, source, published, substitution)?;
        let mut raw = self.template_publication_values(declaration, substitution, position)?;
        let mut prefix = Vec::new();
        let mut arguments = Vec::new();
        for group in &source.typed_parameters.groups {
            for parameter in &group.params {
                let id = parameter.id.value();
                let name = format!("_value_i{id}");
                let value = format!("(Litex.denote {name})");
                let member = match &group.param_type {
                    ParamType::Obj(carrier) => format!(
                        "M.mem {value} {}",
                        self.compile_function_raw_expression_bound(carrier, position, &raw)?
                    ),
                    ParamType::Set(_) => format!("M.isSet {value}"),
                    kind @ (ParamType::NonemptySet(_) | ParamType::FiniteSet(_)) => {
                        format!("{} {name}", set_kind_predicate(kind).unwrap())
                    }
                };
                prefix.push(format!("∀ {{_Host_i{id} : Type v{id}}} [_rep_i{id} : Litex.Representation M _Host_i{id}] ({name} : Litex.Obj (M := M) _Host_i{id}), {member} → "));
                arguments.extend([
                    format!("_Host_i{id}"),
                    format!("_rep_i{id}"),
                    name.clone(),
                    format!("_membership_i{id}"),
                ]);
                raw.insert(parameter.id, value);
            }
        }
        // The stored forall has all parameter groups before all domains.
        // The template's guards therefore follow the body's parameters too.
        if !template_guards.is_empty() {
            prefix.push(format!("∀ {}, ", template_guards.join(" ")));
        }
        for premise in &source.dom_facts {
            prefix.push(format!(
                "({}) → ",
                self.compile_function_raw_predicate(premise, position, &raw)?
            ));
        }
        if let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
            crate::execute::ExecHaveFnByInducStmtResult::Success(body),
        )) = declaration.body.as_ref()
        {
            if let Some(conclusion) =
                self.compile_recursive_published_conclusion(body, source, position, &raw)?
            {
                return Ok((format!("({}{conclusion})", prefix.join("")), arguments));
            }
        }
        let conclusions = source
            .then_facts
            .iter()
            .map(|fact| self.compile_function_raw_predicate(&fact.clone().into(), position, &raw))
            .collect::<Result<Vec<_>, _>>()?;
        let body = super::helper::conjunction_proposition(conclusions)?;
        Ok((format!("({}{body})", prefix.join("")), arguments))
    }
}
