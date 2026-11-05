use super::compile_template_stmt_result::{
    alias_body, template_alias_rhs, template_output, template_output_member_id,
    template_substitution,
};
use super::helper::{ensure_object, instantiated_object_matches};
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TemplateDefEnum;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    FieldAccessObjWellDefinedProof, FnObjDomainFnSetEvidence, StructishObjWellDefinedProofByDef,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_template_record_call_input(
        &self,
        application: &FnObj,
        instance: &InstantiatedTemplateObj,
        field: &FieldAccessObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let object = Obj::FnObj(application.clone());
        let ready = SourcePosition {
            before: 1,
            ..*position
        };
        ready
            .with_visible_wd(&object, &mut |wd, _| {
                ensure_object(&object, wd)?;
                let DetailedObjWellDefinedProof::ByDef {
                    proof: ObjWellDefinedProofByDef::FnObj(call),
                    ..
                } = wd.detailed_ref()
                else {
                    return Err(LeanCompileError::unsupported("TemplateRecord/CallWD"));
                };
                let Some(FnObjDomainFnSetEvidence::TemplateDefinition { fn_set, .. }) =
                    &call.domain_fn_set
                else {
                    return Err(LeanCompileError::unsupported(
                        "TemplateRecord/CallSignature",
                    ));
                };
                self.validate_template_function(instance, fn_set, None, &ready)?;
                let head = self.compile_object_reference(
                    &Obj::InstantiatedTemplateObj(instance.clone()),
                    &ready,
                )?;
                self.compile_struct_declared_input(
                    application,
                    field,
                    fn_set,
                    &format!("({head}).val.signature"),
                    position,
                )
            })?
            .ok_or_else(|| LeanCompileError::unsupported("TemplateRecord/CallWD"))
    }

    /// Close the original record constructor's arguments over the template
    /// header, then apply this instance's checked arguments. No instantiated
    /// constructor or WD proof is synthesized.
    pub(super) fn compile_template_record_arguments(
        &self,
        instance: &InstantiatedTemplateObj,
        carrier: &StructObj,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (template, producer, _) =
            position.visible_template(&instance.template_name, &self.runtime)?;
        let original = match &template.statement.template_def_stmt {
            TemplateDefEnum::HaveObjEqualStmt(_) => {
                let body = alias_body(template)?;
                let binding = template_output(template, instance.template_name.local_name())?.0;
                let group = body
                    .statement
                    .param_def
                    .groups
                    .iter()
                    .find(|g| g.params.iter().any(|p| p.id == binding.id))
                    .ok_or_else(|| LeanCompileError::unsupported("TemplateRecord/OutputName"))?;
                let ParamType::Obj(object) = &group.param_type else {
                    return Err(LeanCompileError::unsupported(
                        "TemplateRecord/DeclaredCarrier",
                    ));
                };
                object
            }
            TemplateDefEnum::HaveFnEqualStmt(body) => {
                body.equal_to_anonymous_fn.body.ret_set.as_ref()
            }
            _ => return Err(LeanCompileError::unsupported("TemplateRecord/Declaration")),
        };
        let ids = template.statement.template_arg_def.ordered_param_ids();
        let substitution = template_substitution(template, instance)?;
        let Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(original_carrier)) =
            original
        else {
            return Err(LeanCompileError::unsupported(
                "TemplateRecord/DeclaredCarrier",
            ));
        };
        if ids.len() != instance.args.len()
            || !instantiated_object_matches(
                original,
                &Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(carrier.clone())),
                &substitution,
            )
        {
            return Err(LeanCompileError::unsupported(
                "TemplateRecord/CarrierSubstitution",
            ));
        }
        let header = SourcePosition::new(Some(&producer), SourceOwner::Template(template), 0);
        let domains = template
            .statement
            .template_arg_dom
            .iter()
            .cloned()
            .map(crate::instantiate::quantifier_free_fact_to_fact)
            .collect::<Vec<_>>();
        let (mut binders, _, definitions) = self.compile_quantified_head(
            &template.statement.template_arg_def,
            &domains,
            &template.introduced_params,
            &template.assumed_dom_facts,
            &header,
        )?;
        for id in &ids {
            let universe = format!("Type v{}}}", id.value());
            for binder in &mut binders {
                *binder = binder.replace(&universe, "Type _}");
            }
        }
        let body = SourcePosition {
            before: ids.len() + domains.len() + 1,
            ..header
        };
        let terms = body
            .with_visible_wd(original, &mut |wd, site| {
                ensure_object(original, wd)?;
                let DetailedObjWellDefinedProof::ByDef {
                    proof:
                        ObjWellDefinedProofByDef::Structish(
                            StructishObjWellDefinedProofByDef::StructObj(p),
                        ),
                    ..
                } = wd.detailed_ref()
                else {
                    return Err(LeanCompileError::unsupported("TemplateRecord/CarrierWD"));
                };
                let ctor = SourcePosition::new(Some(site), SourceOwner::WD(wd), 0);
                self.compile_struct_arguments(original_carrier, p, &ctor)
            })?
            .ok_or_else(|| LeanCompileError::unsupported("TemplateRecord/CarrierWD"))?;
        let object = Obj::InstantiatedTemplateObj(instance.clone());
        let arguments = position
            .with_visible_wd(&object, &mut |wd, site| {
                let DetailedObjWellDefinedProof::ByDef {
                    proof: ObjWellDefinedProofByDef::InstantiatedTemplateObj(p),
                    ..
                } = wd.detailed_ref()
                else {
                    return Err(LeanCompileError::unsupported("TemplateRecord/InstanceWD"));
                };
                let ctor = SourcePosition::new(Some(site), SourceOwner::WD(wd), 0);
                self.compile_template_arguments(instance, p, &ctor)
            })?
            .ok_or_else(|| LeanCompileError::unsupported("TemplateRecord/InstanceWD"))?;
        Ok(terms
            .into_iter()
            .map(|term| {
                let body = self.scope_proposition(term, &definitions);
                if binders.is_empty() {
                    body
                } else {
                    format!(
                        "((fun {} => {body}) {})",
                        binders.join(" "),
                        arguments.join(" ")
                    )
                }
            })
            .collect())
    }

    /// Instantiate the alias declaration's own membership publication. Later
    /// memberships never select a template's default structure view.
    pub(super) fn compile_template_record_member(
        &self,
        instance: &InstantiatedTemplateObj,
        carrier: &StructObj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (template, producer, _) =
            position.visible_template(&instance.template_name, &self.runtime)?;
        let body = alias_body(template)?;
        let binding = template_output(template, instance.template_name.local_name())?.0;
        let group = body
            .statement
            .param_def
            .groups
            .iter()
            .find(|g| g.params.iter().any(|p| p.id == binding.id))
            .ok_or_else(|| LeanCompileError::unsupported("TemplateRecord/OutputName"))?;
        let ParamType::Obj(original) = &group.param_type else {
            return Err(LeanCompileError::unsupported(
                "TemplateRecord/DeclaredCarrier",
            ));
        };
        let ids = template.statement.template_arg_def.ordered_param_ids();
        if ids.len() != instance.args.len() {
            return Err(LeanCompileError::unsupported("TemplateRecord/Arguments"));
        }
        let substitution = template_substitution(template, instance)?;
        if !matches!(
            original,
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(_))
        ) || !instantiated_object_matches(
            original,
            &Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(carrier.clone())),
            &substitution,
        ) {
            return Err(LeanCompileError::unsupported(
                "TemplateRecord/DeclaredCarrier",
            ));
        }
        let source_id = template_output_member_id(template, &binding.name)?;
        let published = template
            .definition_facts
            .iter()
            .find(|p| p.source_fact_id == source_id)
            .ok_or_else(|| LeanCompileError::unsupported("TemplateRecord/MembershipPublication"))?;
        // This template invocation owns the exact generated publication; it
        // does not make the exporting file's unrelated facts visible.
        let reference = position.declaration_reference(
            &format!("h_{}", published.store_and_infer.primary_fact_id().value()),
            &producer,
        )?;
        let object = Obj::InstantiatedTemplateObj(instance.clone());
        position
            .with_visible_wd(&object, &mut |wd, producer| {
                ensure_object(&object, wd)?;
                let DetailedObjWellDefinedProof::ByDef {
                    proof: ObjWellDefinedProofByDef::InstantiatedTemplateObj(evidence),
                    ..
                } = wd.detailed_ref()
                else {
                    return Err(LeanCompileError::unsupported("TemplateRecord/InstanceWD"));
                };
                let scope = SourcePosition::new(Some(producer), SourceOwner::WD(wd), 0);
                let arguments = self.compile_template_arguments(instance, evidence, &scope)?;
                Ok(format!("({reference} {})", arguments.join(" ")))
            })?
            .ok_or_else(|| LeanCompileError::unsupported("TemplateRecord/InstanceWD"))
    }

    /// This result records declaration unfolding, not a new tuple constructor.
    pub(super) fn compile_template_record_value(
        &self,
        instance: &InstantiatedTemplateObj,
        value: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (template, _, _) = position.visible_template(&instance.template_name, &self.runtime)?;
        let rhs = template_alias_rhs(template, instance.template_name.local_name())?;
        let substitution = template_substitution(template, instance)?;
        if !instantiated_object_matches(rhs, value, &substitution) {
            return Err(LeanCompileError::unsupported(
                "TemplateRecord/ValueSubstitution",
            ));
        }
        let source = self.compile_normalization_value(
            &Obj::InstantiatedTemplateObj(instance.clone()),
            position,
        )?;
        let target = self.compile_normalization_value(value, position)?;
        Ok(format!("(show {source} = {target} from rfl)"))
    }
}
