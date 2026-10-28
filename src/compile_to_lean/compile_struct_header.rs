use super::compile_def_struct_stmt_result::validate_struct;
use super::helper::{ensure_object, instantiated_object_matches, source_subject};
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::DefStructStmt;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    StructObjObjWellDefinedProof, StructishObjWellDefinedProofByDef,
};
use crate::execute::ExecDefStructStmtSuccessResult;
use crate::prelude::*;
use std::collections::HashMap;

pub(super) fn header_substitution(
    definition: &DefStructStmt,
    carrier: &StructObj,
) -> Result<HashMap<IdentifierId, Obj>, LeanCompileError> {
    let parameters = definition
        .param_def_with_dom
        .as_ref()
        .map(|(p, _)| p.ordered_param_ids())
        .unwrap_or_default();
    if parameters.len() != carrier.params.len() {
        return Err(LeanCompileError::unsupported("Struct/Arguments"));
    }
    Ok(parameters
        .into_iter()
        .zip(carrier.params.iter().cloned())
        .collect())
}

impl LitexToLeanCompiler {
    pub(super) fn compile_struct_header(
        &self,
        proof: &ExecDefStructStmtSuccessResult,
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, Vec<String>, Vec<String>), LeanCompileError> {
        let Some((parameters, domains)) = &proof.statement.param_def_with_dom else {
            if proof.introduced_params.is_some() || !proof.structure_domains.is_empty() {
                return Err(LeanCompileError::unsupported("Struct/HeaderStages"));
            }
            return Ok((Vec::new(), Vec::new(), Vec::new()));
        };
        let introduced = proof
            .introduced_params
            .as_ref()
            .ok_or_else(|| LeanCompileError::unsupported("Struct/HeaderStages"))?;
        if domains.len() != proof.structure_domains.len() {
            return Err(LeanCompileError::unsupported("Struct/HeaderDomains"));
        }
        if !domains.is_empty() {
            return Err(LeanCompileError::unsupported("Struct/HeaderDomains"));
        }
        self.compile_quantified_head(parameters, &[], introduced, &[], position)
    }

    pub(super) fn struct_self_application(
        &self,
        name: &str,
        proof: &ExecDefStructStmtSuccessResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let base = self.context_application(name, position);
        let Some((parameters, _)) = &proof.statement.param_def_with_dom else {
            return Ok(base);
        };
        let introduced = proof
            .introduced_params
            .as_ref()
            .ok_or_else(|| LeanCompileError::unsupported("Struct/HeaderStages"))?;
        let args = parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .zip(&introduced.defined_params.store_and_infer_results)
            .flat_map(|(p, store)| {
                [
                    format!("_value_i{}", p.id.value()),
                    format!("h_{}", store.primary_fact_id().value()),
                ]
            })
            .collect::<Vec<_>>();
        Ok(if args.is_empty() {
            base
        } else {
            format!("({base} {})", args.join(" "))
        })
    }

    pub(super) fn compile_struct_arguments(
        &self,
        object: &StructObj,
        proof: &StructObjObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (declaration, _, _) = position.visible_struct(&object.name)?;
        validate_struct(declaration)?;
        let subst = header_substitution(&declaration.statement, object)?;
        let params = declaration
            .statement
            .param_def_with_dom
            .as_ref()
            .map(|(p, _)| {
                p.groups
                    .iter()
                    .flat_map(|g| g.params.iter().map(move |p| (p, &g.param_type)))
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        if proof.child_obj_well_defined.len() != params.len()
            || proof.requirement_fact_verified.len() != params.len()
        {
            return Err(LeanCompileError::unsupported("Struct/ArgumentStages"));
        }
        let mut values = Vec::new();
        for (index, (argument, wd)) in object
            .params
            .iter()
            .zip(&proof.child_obj_well_defined)
            .enumerate()
        {
            ensure_object(argument, wd)?;
            values.push(self.compile_wd(
                wd,
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?);
        }
        let mut result = Vec::new();
        for (index, ((_, kind), evidence)) in params
            .iter()
            .zip(&proof.requirement_fact_verified)
            .enumerate()
        {
            let fact = source_subject(evidence)?;
            let arg = &object.params[index];
            let valid = match (kind, &fact) {
                (ParamType::Set(_), Fact::AtomicFact(AtomicFact::IsSetFact(f))) => {
                    f.set.ir() == arg.ir()
                }
                (ParamType::NonemptySet(_), Fact::AtomicFact(AtomicFact::IsNonemptySetFact(f))) => {
                    f.set.ir() == arg.ir()
                }
                (ParamType::Obj(set), Fact::AtomicFact(AtomicFact::InFact(f))) => {
                    f.element.ir() == arg.ir() && instantiated_object_matches(set, &f.set, &subst)
                }
                _ => false,
            };
            if !valid {
                return Err(LeanCompileError::unsupported("Struct/ArgumentTypeSubject"));
            }
            let prior = SourcePosition {
                before: params.len() + index,
                ..*position
            };
            result.push(values[index].clone());
            result.push(self.compile_wd_requirement(evidence, &prior)?);
        }
        Ok(result)
    }

    pub(super) fn compile_struct_family_reference(
        &self,
        object: &StructObj,
        family: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (declaration, producer, index) = position.visible_struct(&object.name)?;
        validate_struct(declaration)?;
        header_substitution(&declaration.statement, object)?;
        let name = self.context_application(&format!("{family}_{}", index + 1), &producer);
        if declaration.statement.param_def_with_dom.is_none() {
            return Ok(name);
        }
        let source =
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(object.clone()));
        let arguments = position
            .with_visible_wd(&source, &mut |wd, producer| {
                let DetailedObjWellDefinedProof::ByDef {
                    proof:
                        ObjWellDefinedProofByDef::Structish(
                            StructishObjWellDefinedProofByDef::StructObj(p),
                        ),
                    ..
                } = (wd).detailed_ref()
                else {
                    return Err(LeanCompileError::unsupported("Struct/ArgumentConstructor"));
                };
                let cursor = SourcePosition::new(Some(producer), SourceOwner::WD(wd), 0);
                self.compile_struct_arguments(object, p, &cursor)
            })?
            .ok_or_else(|| LeanCompileError::unsupported("Struct/ArgumentProducer"))?;
        Ok(format!("({name} {})", arguments.join(" ")))
    }

    pub(super) fn struct_header_raw_bindings(
        &self,
        definition: &DefStructStmt,
        carrier: &StructObj,
        position: &SourcePosition<'_>,
    ) -> Result<HashMap<IdentifierId, String>, LeanCompileError> {
        header_substitution(definition, carrier)?
            .into_iter()
            .map(|(id, obj)| {
                Ok((
                    id,
                    format!(
                        "(Litex.denote {})",
                        self.compile_object_reference(&obj, position)?
                    ),
                ))
            })
            .collect()
    }
}
