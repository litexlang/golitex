use super::compile_general_recursive_result::general_error;
use super::compile_real_set_bounds::contains_parameter;
use super::helper::*;
use super::source_position::{visit_complete_wd, SourceConstructor, SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef;
use crate::execute::ExecHaveFnByInducStmtSuccessResult;
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(super) fn recursive_identifier_is_self(
        &self,
        identifier: &IdentifierObj,
        declaration: &ExecHaveFnByInducStmtSuccessResult,
        site: &SourcePosition<'_>,
    ) -> Result<bool, LeanCompileError> {
        let id = match identifier {
            IdentifierObj::Plain { id, .. } => *id,
            _ => match site.preflight_parameter(identifier, &self.runtime)? {
                Some(parameter) => parameter.id,
                None => {
                    site.qualified_identifier_scope(identifier, &self.runtime)?
                        .0
                        .id
                }
            },
        };
        Ok(id == declaration.statement.name.id)
    }

    /// Traverse the checked constructor tree, including qualified identifiers.
    /// Cached children resolve to their preceding original WD, never a new proof.
    /// Requirements may conservatively add a dependency; they cannot hide one.
    pub(super) fn recursive_body_uses_self(
        &self,
        object: &Obj,
        declaration: &ExecHaveFnByInducStmtSuccessResult,
        site: &SourcePosition<'_>,
    ) -> Result<bool, LeanCompileError> {
        match object {
            Obj::Identifier(identifier) => {
                return self.recursive_identifier_is_self(identifier, declaration, site);
            }
            Obj::Literal(_) | Obj::StandardSet(_) => return Ok(false),
            _ => {}
        }
        // Ordinary local binders retain the existing capture-aware fast path.
        if contains_parameter(object, declaration.statement.name.id) {
            return Ok(true);
        }
        if let Some((_, children)) = arithmetic_constructor_pairs(object, object) {
            for (child, _) in children {
                if self.recursive_body_uses_self(child, declaration, site)? {
                    return Ok(true);
                }
            }
            return Ok(false);
        }
        if let Obj::FnObj(call) = object {
            // The function head can be certified by membership rather than a
            // separate Identifier WD child; inspect its typed identity directly.
            if let FnObjHead::Identifier(identifier) = call.head.as_ref() {
                if self.recursive_identifier_is_self(identifier, declaration, site)? {
                    return Ok(true);
                }
            }
        }
        site.with_visible_wd(object, &mut |proof, owner| {
            Ok(visit_complete_wd(
                proof,
                owner,
                &mut |constructor, producer| {
                    let SourceConstructor::Checked(child) = constructor else {
                        return Ok(None);
                    };
                    if let Obj::Identifier(identifier) = child.obj() {
                        if self.recursive_identifier_is_self(identifier, declaration, producer)? {
                            return Ok(Some(()));
                        }
                    } else if let Obj::FnObj(call) = child.obj() {
                        if let FnObjHead::Identifier(identifier) = call.head.as_ref() {
                            if self.recursive_identifier_is_self(
                                identifier,
                                declaration,
                                producer,
                            )? {
                                return Ok(Some(()));
                            }
                        }
                        if matches!(
                            child.detailed_ref(),
                            DetailedObjWellDefinedProof::ByKnown { .. }
                        ) && self.recursive_body_uses_self(child.obj(), declaration, producer)?
                        {
                            return Ok(Some(()));
                        }
                    } else if matches!(
                        child.detailed_ref(),
                        DetailedObjWellDefinedProof::ByKnown { .. }
                    ) && self.recursive_body_uses_self(
                        child.obj(),
                        declaration,
                        producer,
                    )? {
                        return Ok(Some(()));
                    }
                    Ok(None)
                },
                &mut |_, _| Ok(None),
            )?
            .is_some())
        })?
        .ok_or_else(|| general_error("DependencyWD"))
    }

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
        let recursive = match &head {
            Obj::Identifier(identifier) => {
                self.recursive_identifier_is_self(identifier, declaration, site)?
            }
            _ => false,
        };
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
