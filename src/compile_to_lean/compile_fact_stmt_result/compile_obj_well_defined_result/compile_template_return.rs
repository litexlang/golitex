use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::known_template_standard_return::TemplateApplicationInStandardSupersetProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::TemplateApplicationInDeclaredCodomainProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
use crate::execute::execute_fact_stmt::fn_sets_alpha_equal;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_template_declared_return(
        &self,
        goal: &InFact,
        proof: &TemplateApplicationInDeclaredCodomainProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::FnObj(application) = &goal.element else {
            return Err(LeanCompileError::unsupported("TemplateReturn/Subject"));
        };
        let head = template_return_head(application)?;
        let head_term = self.compile_object_reference(&head, position)?;
        let instance = Obj::InstantiatedTemplateObj(proof.instance.clone());
        let template = self.compile_object_reference(&instance, position)?;
        self.validate_template_function(
            &proof.instance,
            &proof.declared_signature,
            None,
            position,
        )?;
        if Self::fixed_function_call_output(application, &proof.declared_signature)?
            != &proof.applied_return_set
        {
            return Err(LeanCompileError::unsupported(
                "TemplateReturn/DeclaredOutput",
            ));
        }
        let path = self.compile_equality_path(&head, &instance, &proof.function_equal, position)?;
        let equality = self.compile_fn_return_set_match(
            &proof.applied_return_set,
            &goal.set,
            &proof.return_set_match,
            position,
        )?;
        let source = self.compile_object_reference(&proof.applied_return_set, position)?;
        let target = self.compile_object_reference(&goal.set, position)?;
        let mut lines = vec![format!(
            "have _template_head : Litex.Same {head_term} {template} := {path}"
        )];
        let mut templates = std::collections::HashSet::new();
        for (index, entry) in proof
            .alternative_template_signature_matches
            .iter()
            .enumerate()
        {
            let object = Obj::InstantiatedTemplateObj(entry.instance.clone());
            if !templates.insert(object.ir()) {
                return Err(LeanCompileError::unsupported(
                    "TemplateReturn/DuplicateTemplate",
                ));
            }
            // This payload has no instantiated alternative signature. Accept
            // the captured signature only when the original declaration proves
            // that exact substitution; other signatures remain unsupported.
            self.validate_template_function(
                &entry.instance,
                &proof.declared_signature,
                None,
                position,
            )?;
            let term = self.compile_object_reference(&object, position)?;
            let path =
                self.compile_equality_path(&head, &object, &entry.function_equal, position)?;
            let same = self.compile_fn_return_set_match(
                &proof.applied_return_set,
                &goal.set,
                &entry.return_set_match,
                position,
            )?;
            lines.push(format!(
                "have _template_peer_{index} : Litex.Same {head_term} {term} := {path}"
            ));
            lines.push(format!(
                "have _template_output_{index} : Litex.Same {source} {target} := {same}"
            ));
        }
        if !templates.contains(&instance.ir()) {
            return Err(LeanCompileError::unsupported("TemplateReturn/MainTemplate"));
        }
        let mut citations = std::collections::HashSet::new();
        for (index, entry) in proof.alternative_signature_matches.iter().enumerate() {
            if !citations.insert(entry.cite_signature_fact_id) {
                return Err(LeanCompileError::unsupported(
                    "TemplateReturn/DuplicateSignature",
                ));
            }
            let (signature, member) = self.compile_fn_return_citation(
                entry.cite_signature_fact_id,
                &head,
                &head_term,
                None,
                position,
            )?;
            let output = Self::fixed_function_call_output(application, signature)?;
            let same = self.compile_fn_return_set_match(
                output,
                &goal.set,
                &entry.return_set_match,
                position,
            )?;
            let output = self.compile_object_reference(output, position)?;
            lines.push(format!("have _template_signature_{index} := {member}"));
            lines.push(format!(
                "have _template_signature_output_{index} : Litex.Same {output} {target} := {same}"
            ));
        }
        let result = position.with_visible_wd(&goal.element, &mut |wd, producer| {
            ensure_object(&goal.element, wd)?;
            let DetailedObjWellDefinedProof::ByDef { proof: ObjWellDefinedProofByDef::FnObj(evidence), .. } = wd.detailed_ref() else {
                return Err(LeanCompileError::unsupported("TemplateReturn/CallWD"));
            };
            let Some(FnObjDomainFnSetEvidence::TemplateDefinition { fn_set, .. }) = &evidence.domain_fn_set else {
                return Err(LeanCompileError::unsupported("TemplateReturn/SelectedSignature"));
            };
            let template_wd = evidence.child_obj_well_defined.first().ok_or_else(|| LeanCompileError::unsupported("TemplateReturn/TemplateWD"))?;
            // Instantiating a template may assign fresh IDs to its guards.
            // Those IDs identify evidence, not different function signatures.
            if !fn_sets_alpha_equal(fn_set, &proof.declared_signature) || !templates.contains(&template_wd.obj().ir()) {
                return Err(LeanCompileError::unsupported("TemplateReturn/SelectedSignature"));
            }
            let ctor = SourcePosition::new(Some(producer), SourceOwner::WD(wd), 0);
            let call = match position.bound_wd_child(wd).or_else(|| producer.bound_wd_child(wd)) {
                Some(call) => call,
                None => self.compile_fn_obj_wd(application, evidence, &ctor)?,
            };
            let member = self.compile_call_output_proof(application, evidence, &call, &ctor)?;
            Ok(format!("(Litex.inOfSame {call} {call} {source} {target} (Litex.sameRefl {call}) {equality} {member})"))
        })?.ok_or_else(|| LeanCompileError::unsupported("TemplateReturn/Producer"))?;
        lines.push(format!("exact {result}"));
        Ok(format!(
            "(by\n  {})",
            lines.join("\n").replace('\n', "\n  ")
        ))
    }

    pub(super) fn compile_template_standard_return(
        &self,
        goal: &InFact,
        proof: &TemplateApplicationInStandardSupersetProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (Obj::FnObj(application), Obj::StandardSet(target)) = (&goal.element, &goal.set) else {
            return Err(LeanCompileError::unsupported("TemplateReturn/Subject"));
        };
        if &proof.target_set != target || proof.declared_returns.is_empty() {
            return Err(LeanCompileError::unsupported("TemplateReturn/Target"));
        }
        let head = match application.head.as_ref() {
            FnObjHead::Identifier(id) => Obj::Identifier(id.clone()),
            FnObjHead::InstantiatedTemplateObj(instance) => {
                Obj::InstantiatedTemplateObj(instance.clone())
            }
            FnObjHead::FieldAccess(field) => {
                Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(field.clone()))
            }
            FnObjHead::Object(object) => object.as_ref().clone(),
            _ => return Err(LeanCompileError::unsupported("TemplateReturn/Head")),
        };
        let head_term = self.compile_object_reference(&head, position)?;
        let mut lines = Vec::new();
        let mut has_template = false;
        let mut strict = false;
        for (index, entry) in proof.declared_returns.iter().enumerate() {
            let function = self.compile_object_reference(&entry.function, position)?;
            let member = match &entry.function {
                Obj::InstantiatedTemplateObj(instance) => {
                    self.validate_template_function(
                        instance,
                        &entry.declared_signature,
                        None,
                        position,
                    )?;
                    has_template = true;
                    self.template_call_interface(instance, &function, position)?
                        .1
                }
                Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(field)) => self
                    .compile_struct_function_membership(
                    field,
                    &entry.declared_signature,
                    position,
                )?,
                Obj::FunctionSpace(FunctionSpace::AnonymousFn(literal))
                    if literal.body == entry.declared_signature =>
                {
                    format!("(Litex.formulaFnInFnSet {function})")
                }
                _ => return Err(LeanCompileError::unsupported("TemplateReturn/Declaration")),
            };
            let output = Self::fixed_function_call_output(application, &entry.declared_signature)?;
            if output != &Obj::StandardSet(entry.source_set.clone()) {
                return Err(LeanCompileError::unsupported(
                    "TemplateReturn/DeclaredOutput",
                ));
            }
            standard_inclusion_term(&entry.source_set, target, "_", "_")?;
            strict |= &entry.source_set != target;
            let path = self.compile_equality_path(
                &head,
                &entry.function,
                &entry.function_equal,
                position,
            )?;
            let signature = self.compile_fn_signature(&entry.declared_signature, position)?;
            lines.push(format!("have _declared_return_{index} : Litex.In {function} (Litex.fnSet {signature}) := {member}"));
            lines.push(format!(
                "have _declared_return_equal_{index} : Litex.Same {head_term} {function} := {path}"
            ));
        }
        let mut seen = std::collections::HashSet::new();
        for (index, entry) in proof.signature_returns.iter().enumerate() {
            if !seen.insert(entry.cite_signature_fact_id)
                || &entry.applied.application != application
                || entry.applied.layers.len() != application.body.len()
            {
                return Err(LeanCompileError::unsupported(
                    "TemplateReturn/SignatureStages",
                ));
            }
            let (signature, member) = self.compile_fn_return_citation(
                entry.cite_signature_fact_id,
                &head,
                &head_term,
                Some(&entry.function_equal),
                position,
            )?;
            if entry.applied.layers.first() != Some(signature) {
                return Err(LeanCompileError::unsupported(
                    "TemplateReturn/SignatureSource",
                ));
            }
            for layers in entry.applied.layers.windows(2) {
                self.validate_function_carrier_signature(&layers[0].ret_set, &layers[1])?;
            }
            let output = Self::fixed_function_call_output(application, signature)?;
            if output != &entry.applied.return_set
                || output != &Obj::StandardSet(entry.source_set.clone())
            {
                return Err(LeanCompileError::unsupported(
                    "TemplateReturn/SignatureOutput",
                ));
            }
            standard_inclusion_term(&entry.source_set, target, "_", "_")?;
            strict |= &entry.source_set != target;
            lines.push(format!("have _cited_return_{index} := {member}"));
        }
        if !has_template || !strict {
            return Err(LeanCompileError::unsupported(
                "TemplateReturn/StrictInclusion",
            ));
        }
        let result = position
            .with_visible_wd(&goal.element, &mut |wd, producer| {
                ensure_object(&goal.element, wd)?;
                let DetailedObjWellDefinedProof::ByDef {
                    proof: ObjWellDefinedProofByDef::FnObj(evidence),
                    ..
                } = wd.detailed_ref()
                else {
                    return Err(LeanCompileError::unsupported("TemplateReturn/CallWD"));
                };
                let anchored = match &evidence.domain_fn_set {
                    Some(FnObjDomainFnSetEvidence::TemplateDefinition { fn_set, .. }) => {
                        let template =
                            evidence.child_obj_well_defined.first().ok_or_else(|| {
                                LeanCompileError::unsupported("TemplateReturn/TemplateWD")
                            })?;
                        proof.declared_returns.iter().any(|entry| {
                            entry.function.ir() == template.obj().ir()
                                && fn_sets_alpha_equal(&entry.declared_signature, fn_set)
                        })
                    }
                    Some(FnObjDomainFnSetEvidence::InFunctionSet {
                        fact_id, fn_set, ..
                    }) => proof.signature_returns.iter().any(|entry| {
                        entry.cite_signature_fact_id == *fact_id
                            && entry
                                .applied
                                .layers
                                .first()
                                .is_some_and(|source| fn_sets_alpha_equal(source, fn_set))
                    }),
                    Some(FnObjDomainFnSetEvidence::AnonymousLiteral { fn_set }) => {
                        proof.declared_returns.iter().any(|entry| {
                            entry.function.ir() == head.ir()
                                && fn_sets_alpha_equal(&entry.declared_signature, fn_set)
                        })
                    }
                    _ => false,
                };
                if !anchored {
                    return Err(LeanCompileError::unsupported(
                        "TemplateReturn/SelectedSignature",
                    ));
                }
                let ctor = SourcePosition::new(Some(producer), SourceOwner::WD(wd), 0);
                let call = self.compile_fn_obj_wd(application, evidence, &ctor)?;
                let (output, member) =
                    self.compile_fn_output_membership(application, evidence, &ctor)?;
                standard_inclusion_term(&output, target, &call, &member)
            })?
            .ok_or_else(|| LeanCompileError::unsupported("TemplateReturn/Producer"))?;
        lines.push(format!("exact {result}"));
        Ok(format!(
            "(by\n  {})",
            lines.join("\n").replace('\n', "\n  ")
        ))
    }
}

fn template_return_head(application: &FnObj) -> Result<Obj, LeanCompileError> {
    match application.head.as_ref() {
        FnObjHead::Identifier(id) => Ok(Obj::Identifier(id.clone())),
        FnObjHead::InstantiatedTemplateObj(instance) => {
            Ok(Obj::InstantiatedTemplateObj(instance.clone()))
        }
        FnObjHead::FieldAccess(field) => Ok(Obj::StructAndFieldAccessObj(
            StructAndFieldAccessObj::FieldAccess(field.clone()),
        )),
        FnObjHead::Object(object) => Ok(object.as_ref().clone()),
        _ => Err(LeanCompileError::unsupported("TemplateReturn/Head")),
    }
}
