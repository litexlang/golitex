use super::compile_general_recursive_result::general_error;
use super::compile_real_set_bounds::contains_parameter;
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef;
use crate::execute::ExecHaveFnByInducStmtSuccessResult;
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(super) fn compile_recursive_application_congruence(
        &self,
        object: &Obj,
        call: &FnObj,
        declaration: &ExecHaveFnByInducStmtSuccessResult,
        site: &SourcePosition<'_>,
        bindings: &HashMap<IdentifierId, String>,
    ) -> Result<String, LeanCompileError> {
        if call.body.is_empty() || call.body.iter().any(Vec::is_empty) {
            return Err(general_error("CallArity"));
        }
        let head = match call.head.as_ref() {
            FnObjHead::Identifier(id) => Obj::Identifier(id.clone()),
            FnObjHead::Object(obj) => obj.as_ref().clone(),
            FnObjHead::AnonymousFnLiteral(f) => {
                Obj::FunctionSpace(FunctionSpace::AnonymousFn(f.as_ref().clone()))
            }
            FnObjHead::InstantiatedTemplateObj(t) => Obj::InstantiatedTemplateObj(t.clone()),
            FnObjHead::FieldAccess(f) => {
                Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(f.clone()))
            }
        };
        let recursive = matches!(&head, Obj::Identifier(IdentifierObj::Plain {id, ..}) if *id == declaration.statement.name.id);
        let mut equality = if recursive {
            String::new()
        } else {
            self.compile_general_recursive_congruence(&head, declaration, site, bindings)?
        };
        for (index, arguments) in call.body.iter().enumerate() {
            let children = arguments
                .iter()
                .map(|arg| {
                    self.compile_general_recursive_congruence(arg, declaration, site, bindings)
                })
                .collect::<Result<Vec<_>, _>>()?;
            let packed = if children.len() == 1 {
                children[0].clone()
            } else {
                format!(
                    "(congrArg (Litex.FiniteFunction.tupleValue (M := M)) (funext {}))",
                    finite_vector_proof(&children)
                )
            };
            equality = if recursive && index == 0 {
                let domain = site
                    .with_visible_wd(object, &mut |wd, owner| {
                        let restricted = self.recursive_restricted_signature(declaration, owner)?;
                        let (terms, proofs) = self.compile_recursive_call_prefix_arguments(
                            object,
                            declaration,
                            wd,
                            owner,
                        )?;
                        self.compile_general_recursive_domain_member(
                            &restricted,
                            &terms,
                            &proofs,
                            owner,
                        )
                    })?
                    .ok_or_else(|| general_error("CallProducer"))?;
                format!("((_agree {} {}).trans (congrArg (Litex.FunctionSemantics.callValue (M := M) _other_prefix) {packed}))", domain.0, domain.1)
            } else {
                format!(
                    "(congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) {equality} {packed})"
                )
            };
        }
        Ok(equality)
    }

    pub(super) fn compile_recursive_literal_congruence(
        &self,
        object: &Obj,
        function: &AnonymousFn,
        declaration: &ExecHaveFnByInducStmtSuccessResult,
        site: &SourcePosition<'_>,
        bindings: &HashMap<IdentifierId, String>,
    ) -> Result<String, LeanCompileError> {
        let signature = &function.body;
        if contains_parameter(
            &Obj::FunctionSpace(FunctionSpace::FnSet(signature.clone())),
            declaration.statement.name.id,
        ) {
            return Err(general_error("LiteralSelfDependentSignature"));
        }
        site.with_visible_wd(object, &mut |wd, owner| {
            let DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(proof)), ..
            } = wd.detailed_ref() else { return Err(general_error("LiteralWD")); };
            ensure_object(object, wd)?;
            let scope = SourcePosition::new(Some(owner), SourceOwner::WD(wd), 0);
            let completed = SourcePosition { before: self.function_header_stages(signature) + 2, ..scope };
            let head = self.compile_function_binder_head(signature, &proof.param_type_well_defined, &proof.defined_params, &proof.assumed_dom_facts, &scope)?;
            let (domain, output, inner) = self.compile_function_signature_value_parts(signature, &completed, bindings)?;
            let mut other = inner.clone();
            other.insert(declaration.statement.name.id, "_other_prefix".into());
            let left = self.compile_function_raw_expression_bound(&function.equal_to, &completed, &inner)?;
            let right = self.compile_function_raw_expression_bound(&function.equal_to, &completed, &other)?;
            let equality = self.compile_general_recursive_congruence(&function.equal_to, declaration, &completed, &inner)?;
            let quantified = self.compile_function_raw_quantified(signature, &format!("{left} = {right}"), &completed)?;
            let values = self.compile_function_packed_values(signature, "_literal_input")?;
            let members = if values.len() == 1 { "_literal_members".into() } else {
                (0..values.len()).map(|index| format!("(by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _literal_members ({index} : Fin {}))", values.len())).collect::<Vec<_>>().join(" ")
            };
            let constructor = self.compile_wd(wd, owner)?;
            let (_, _, left_body) = self.compile_function_literal_parts(function, &completed, bindings)?;
            let mut outer_other = bindings.clone();
            outer_other.insert(declaration.statement.name.id, "_other_prefix".into());
            let (_, _, right_body) = self.compile_function_literal_parts(function, &completed, &outer_other)?;
            Ok(format!("(by\n  let _literal := {constructor}\n  have _literal_body_equal : {quantified} := by\n    {}\n    exact {equality}\n  apply Litex.functionGraphValueCongr {domain} {output} {left_body} {right_body} _literal.wd\n  intro _literal_input _literal_domain\n  obtain ⟨_literal_members, _literal_guards⟩ := (Litex.SetSemantics.sep_members (M := M) _ _ _).mp _literal_domain\n  exact _literal_body_equal {} {members} _literal_guards)", head.replace('\n', "\n    "), values.join(" ")))
        })?.ok_or_else(|| general_error("LiteralProducer"))
    }
}
