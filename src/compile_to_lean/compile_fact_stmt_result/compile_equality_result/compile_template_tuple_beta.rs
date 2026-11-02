use super::compile_function_definition::function_head_object;
use crate::ast::stmt::TemplateDefEnum;
use crate::compile_to_lean::compile_returned_function::function_carrier_signatures_alpha_equal;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::known_tuple::{
    KnownFunctionTupleApplicability, KnownFunctionTupleValueProof,
};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
use crate::prelude::*;
use std::collections::{HashMap, HashSet};

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_template_tuple_beta(
        &self,
        application: &Obj,
        checked_application: &Obj,
        proof: &KnownFunctionTupleValueProof,
        value: &Obj,
        wd: &ObjWellDefinedProof,
        site: &SourcePosition<'_>,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let KnownFunctionTupleApplicability::TemplateDefinition {
            instance,
            signature,
            alternative_signatures,
            alternative_template_signatures,
        } = &proof.applicability
        else {
            return Err(LeanCompileError::unsupported("TemplateTuple/Applicability"));
        };
        let Obj::FnObj(call) = application else {
            return Err(LeanCompileError::unsupported("TemplateTuple/Application"));
        };
        if application.ir() != checked_application.ir()
            || call.body.len() != 1
            || value != &Obj::ProductShape(ProductShape::Tuple(proof.value.clone()))
        {
            return Err(LeanCompileError::unsupported("TemplateTuple/Subject"));
        }
        self.validate_template_function(instance, signature, None, position)?;
        let (declaration, producer, _) = position.visible_template(&instance.template_name)?;
        let TemplateDefEnum::HaveFnEqualStmt(source) = &declaration.statement.template_def_stmt
        else {
            return Err(LeanCompileError::unsupported("TemplateTuple/Declaration"));
        };
        let function = &source.equal_to_anonymous_fn;
        let ids = declaration.statement.template_arg_def.ordered_param_ids();
        let parameters = function
            .body
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(|p| p.id))
            .collect::<Vec<_>>();
        if ids.len() != instance.args.len()
            || parameters.len() != call.body[0].len()
            || parameters.is_empty()
        {
            return Err(LeanCompileError::unsupported("TemplateTuple/Arguments"));
        }
        let mut substitution: HashMap<_, _> = ids
            .iter()
            .copied()
            .zip(instance.args.iter().cloned())
            .collect();
        for (id, argument) in parameters.iter().zip(&call.body[0]) {
            if substitution
                .insert(*id, argument.as_ref().clone())
                .is_some()
            {
                return Err(LeanCompileError::unsupported(
                    "TemplateTuple/BinderIdentity",
                ));
            }
        }
        if !instantiated_object_matches(&function.equal_to, value, &substitution) {
            return Err(LeanCompileError::unsupported(
                "TemplateTuple/ValueSubstitution",
            ));
        }
        let head = function_head_object(call.head.as_ref())?;
        let template = Obj::InstantiatedTemplateObj(instance.clone());
        let formula = self.compile_object_reference(&template, position)?;
        let head_equal =
            self.compile_equality_path(&head, &template, &proof.function_equal, position)?;
        let head_term = self.compile_object_reference(&head, position)?;
        let target = Obj::FunctionSpace(FunctionSpace::FnSet(signature.clone()));
        let mut checks = Vec::new();
        let mut citations = HashSet::new();
        for entry in alternative_signatures {
            if !citations.insert(entry.cite_signature_fact_id) {
                return Err(LeanCompileError::unsupported(
                    "TemplateTuple/DuplicateSignature",
                ));
            }
            let (original, member) = self.compile_fn_return_citation(
                entry.cite_signature_fact_id,
                &head,
                &head_term,
                None,
                position,
            )?;
            let equality = self.compile_known_tuple_match(
                &Obj::FunctionSpace(FunctionSpace::FnSet(original.clone())),
                &target,
                &entry.signature_match,
                position,
            )?;
            let source = self.compile_fn_signature(original, position)?;
            checks.push(format!("have _template_signature_{} := {member}\nhave _template_signature_match_{} : Litex.Same (Litex.fnSet {source}) (Litex.fnSet _template_formula.val.signature) := {equality}", entry.cite_signature_fact_id.value(), entry.cite_signature_fact_id.value()));
        }
        let mut peers = HashSet::new();
        for (index, entry) in alternative_template_signatures.iter().enumerate() {
            let peer = Obj::InstantiatedTemplateObj(entry.instance.clone());
            if !peers.insert(peer.ir()) {
                return Err(LeanCompileError::unsupported(
                    "TemplateTuple/DuplicateTemplate",
                ));
            }
            self.validate_template_function(&entry.instance, signature, None, position)?;
            let object = self.compile_object_reference(&peer, position)?;
            let equal =
                self.compile_equality_path(&head, &peer, &entry.function_equal, position)?;
            let matched =
                self.compile_known_tuple_match(&target, &target, &entry.signature_match, position)?;
            checks.push(format!("have _template_peer_{index} : Litex.Same {head_term} {object} := {equal}\nhave _template_peer_signature_{index} : Litex.Same (Litex.fnSet ({object}).val.signature) (Litex.fnSet _template_formula.val.signature) := {matched}"));
        }
        if !peers.contains(&template.ir()) {
            return Err(LeanCompileError::unsupported("TemplateTuple/MainTemplate"));
        }
        let scope = SourcePosition::new(
            Some(&producer),
            SourceOwner::Template(declaration),
            usize::MAX,
        );
        let mut raw = HashMap::new();
        for (id, argument) in ids.iter().zip(&instance.args) {
            raw.insert(*id, self.compile_normalization_value(argument, position)?);
        }
        for id in &parameters {
            raw.insert(*id, format!("_raw_i{}", id.value()));
        }
        let body = self.compile_function_raw_expression_bound(&function.equal_to, &scope, &raw)?;
        let binders = parameters
            .iter()
            .map(|id| format!("(_raw_i{} : M.Value)", id.value()))
            .collect::<Vec<_>>();
        let body = format!("(fun {} => {body})", binders.join(" "));
        let values = call.body[0]
            .iter()
            .map(|a| self.compile_normalization_value(a, position))
            .collect::<Result<Vec<_>, _>>()?;
        let body_equal = self.compile_function_packed_application_equality(&body, &values)?;
        let endpoint = self.compile_normalization_value(value, position)?;
        let input = self.compile_normalization_value(application, position)?;
        ensure_object(checked_application, wd)?;
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(evidence),
            ..
        } = wd.detailed_ref()
        else {
            return Err(LeanCompileError::unsupported("TemplateTuple/CallWD"));
        };
        let Some(FnObjDomainFnSetEvidence::TemplateDefinition { fn_set, .. }) =
            &evidence.domain_fn_set
        else {
            return Err(LeanCompileError::unsupported(
                "TemplateTuple/SelectedSignature",
            ));
        };
        if !function_carrier_signatures_alpha_equal(fn_set, signature)
            || evidence.child_obj_well_defined.first().map(|p| p.obj()) != Some(&template)
        {
            return Err(LeanCompileError::unsupported(
                "TemplateTuple/SelectedSignature",
            ));
        }
        let actual = self.compile_wd(wd, site)?;
        Ok(format!("(show {input} = {endpoint} from by\n  let _template_original := {actual}\n  let _template_formula := {formula}\n  {}\n  have _template_head : Litex.Same _template_original.val.function _template_formula := {head_equal}\n  have _template_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _template_original.val.argument)) _template_head\n  have _template_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _template_formula.wd (Litex.denote _template_original.val.argument) _template_original.wd.2\n  have _template_body : _template_formula.val.bodyValue (Litex.denote _template_original.val.argument) = {endpoint} := {body_equal}\n  exact _template_call.trans (_template_beta.trans _template_body)\n)", checks.join("\n").replace('\n', "\n  ")))
    }
}
