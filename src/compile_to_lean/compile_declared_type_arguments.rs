//! Specialize declaration-owned type proofs without exporting local facts.
use super::helper::{ensure_object, parameter_type_fact_matches};
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_declared_struct_arguments(
        &self,
        carrier: &StructObj,
        position: &SourcePosition<'_>,
    ) -> Result<Option<Vec<String>>, LeanCompileError> {
        let object =
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(carrier.clone()));
        self.compile_declared_type_terms(&object, position, &mut |wd, prefix| {
            let DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::Structish(
                    crate::execute::execute_fact_stmt::well_defined_results::verify_obj::StructishObjWellDefinedProofByDef::StructObj(arguments),
                ), ..
            } = wd.detailed_ref() else {
                return Err(LeanCompileError::unsupported("HaveEqual/TypeWDConstructor"));
            };
            let Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(formal_carrier)) = wd.obj() else {
                return Err(LeanCompileError::unsupported("HaveEqual/TypeWDConstructor"));
            };
            let formed = SourcePosition::new(Some(prefix), SourceOwner::WD(wd), 0);
            self.compile_struct_arguments(formal_carrier, arguments, &formed)
        })
    }

    pub(super) fn compile_declared_type_object(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        let terms = self.compile_declared_type_terms(object, position, &mut |wd, prefix| {
            Ok(vec![self.compile_wd(wd, prefix)?])
        })?;
        Ok(terms.and_then(|mut terms| terms.pop()))
    }

    fn compile_declared_type_terms(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
        compile: &mut impl FnMut(
            &ObjWellDefinedProof,
            &SourcePosition<'_>,
        ) -> Result<Vec<String>, LeanCompileError>,
    ) -> Result<Option<Vec<String>>, LeanCompileError> {
        position.with_visible_declared_type(object, &self.runtime, &mut |proof, group, producer| {
            position.validate_declaration_context(producer)?;
            let parameters = &proof.statement.param_def;
            let prefix_count = parameters.groups[..group]
                .iter()
                .map(|g| g.params.len())
                .sum();
            let prefix = SourcePosition::new(
                Some(producer),
                SourceOwner::HaveEqualType(proof),
                prefix_count,
            );
            let (binders, _, definitions) =
                self.compile_parameter_prefix(parameters, &proof.type_preflight, group, &prefix)?;
            let Some(ParamTypeWellDefinedProof::Obj(wd)) =
                proof.type_preflight.param_type_well_defined.get(group)
            else {
                return Err(LeanCompileError::unsupported("HaveEqual/TypeWD"));
            };
            let ParamType::Obj(formal) = &parameters.groups[group].param_type else {
                return Err(LeanCompileError::unsupported("HaveEqual/TypeWD"));
            };
            ensure_object(formal, wd)?;
            let terms = compile(wd, &prefix)?;
            let stores = &proof.store_and_infer_result.store_and_infer_results;
            let mut actual = Vec::new();
            let mut publication = std::collections::HashMap::new();
            for p in parameters.groups.iter().flat_map(|g| &g.params) {
                publication.insert(
                    p.id,
                    Obj::Identifier(producer.defining_identifier(p, &self.runtime)?),
                );
            }
            for (index, (parameter, kind)) in parameters.groups[..group]
                .iter()
                .flat_map(|g| g.params.iter().map(move |p| (p, &g.param_type)))
                .enumerate()
            {
                let source =
                    Obj::Identifier(producer.defining_identifier(parameter, &self.runtime)?);
                let store = stores
                    .get(index)
                    .ok_or_else(|| LeanCompileError::unsupported("HaveEqual/TypePrefixStore"))?;
                let (fact, _) = producer.visible_fact(store.primary_fact_id(), &self.runtime)?;
                if !parameter_type_fact_matches(kind, &source, fact, &publication) {
                    return Err(LeanCompileError::unsupported("HaveEqual/TypePrefixSubject"));
                }
                self.validate_store(&store.store, fact)?;
                actual.push(self.compile_object_reference(&source, producer)?);
                actual.push(position.declaration_reference(
                    &format!("h_{}", store.primary_fact_id().value()),
                    producer,
                )?);
            }
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
                            actual.join(" ")
                        )
                    }
                })
                .collect())
        })
    }
}
