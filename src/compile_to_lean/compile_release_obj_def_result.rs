use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_release_obj_def_stmt::{
    ExecReleaseObjDefStmtResult, ReleaseObjDefByKind,
};
use crate::execute::{ExecHaveFnEqualStmtResult, ExecHaveObjByExistFactsStmtResult};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_release_obj_definition(
        &self,
        result: &ExecReleaseObjDefStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let ExecReleaseObjDefStmtResult::Success(proof) = result else {
            return Err(LeanCompileError::unsupported("ReleaseObj/Failed"));
        };
        let (id, name, scope) = match &proof.statement.name {
            IdentifierObj::Plain { id, name } => (*id, name.as_str(), *position),
            identifier => {
                let (bound, scope, captured) =
                    position.qualified_identifier_scope(identifier, &self.runtime)?;
                if captured != &proof.looked_up {
                    return Err(LeanCompileError::unsupported(
                        "ReleaseObj/DeclarationCapture",
                    ));
                }
                (bound.id, bound.name.as_str(), scope)
            }
        };
        let (definition, declaration_site, _statement) =
            scope.visible_object_definition(|definition| {
                super::helper::captured_identifier_definition_matches(
                    &proof.looked_up,
                    definition,
                    name,
                )
            })?;
        let pairs = original_release_facts(definition, &proof.released, id, name)?;
        // A historical declaration is complete in its original enclosing
        // prefix; constructor visitors retain their pre-declaration ceiling.
        let declaration = SourcePosition {
            before: declaration_site.before + 1,
            ..declaration_site
        };
        position.validate_declaration_context(&declaration_site)?;
        if pairs.len() != proof.store_and_infer.len() {
            return Err(LeanCompileError::unsupported("ReleaseObj/StoreCount"));
        }
        let mut emitted = Vec::new();
        for (offset, ((released, original_id), store)) in
            pairs.iter().zip(&proof.store_and_infer).enumerate()
        {
            let prior = SourcePosition {
                before: offset,
                ..*position
            };
            // Explicit release authorizes this original declaration publication,
            // rather than making the exporting file's ordinary facts visible.
            // The original publication distinguishes a global theorem from
            // a free parameter's hypothesis. Only the former takes model and
            // source-context arguments; both retain their original namespace.
            let (original, reference) = declaration.visible_fact(*original_id, &self.runtime)?;
            if original.ir() != released.ir() {
                return Err(LeanCompileError::new(
                    "ReleaseObj/Subject",
                    "The released fact differs from its introducing declaration's fact.",
                ));
            }
            self.validate_store(&store.store, released)?;
            let proposition = self.fact_proposition(released, &declaration)?;
            emitted.push(self.emit_fact(
                released,
                (proposition.clone(), reference),
                index,
                local,
                &prior,
            )?);
            let published = SourcePosition {
                before: offset + 1,
                ..*position
            };
            let name = format!("h_{}", released.fact_id().value());
            let reference = if local {
                name
            } else {
                self.context_application(&name, &published)
            };
            emitted.extend(self.compile_stored_inferences(
                store,
                released,
                &(proposition, reference),
                &published,
            )?);
        }
        Ok(emitted.join("\n\n"))
    }
}

fn parameter_offset(
    parameters: &TypedParameterList,
    id: IdentifierId,
    name: &str,
) -> Result<(usize, usize), LeanCompileError> {
    let params: Vec<_> = parameters
        .groups
        .iter()
        .flat_map(|group| &group.params)
        .collect();
    let offset = params
        .iter()
        .position(|p| p.id == id && p.name == name)
        .ok_or_else(|| LeanCompileError::unsupported("ReleaseObj/Identifier"))?;
    Ok((offset, params.len()))
}

fn original_release_facts<'a>(
    source: &ExecDefinitionStmtResult,
    released: &'a ReleaseObjDefByKind,
    id: IdentifierId,
    name: &str,
) -> Result<Vec<(&'a Fact, FactId)>, LeanCompileError> {
    let wrong = || LeanCompileError::unsupported("ReleaseObj/DefinitionStores");
    match (source, released) {
        (
            ExecDefinitionStmtResult::DefineObj(ExecDefineObjStmtResult::LetObj(
                ExecLetObjStmtResult::Success(p),
            )),
            ReleaseObjDefByKind::LetObj { equal },
        ) => {
            if p.statement.name.id != id
                || p.statement.name.name != name
                || p.stored_fact_ids.len() != 1
            {
                return Err(wrong());
            }
            Ok(vec![(equal, p.stored_fact_ids[0])])
        }
        (
            ExecDefinitionStmtResult::DefineObj(ExecDefineObjStmtResult::HaveObjInNonemptySet(
                ExecHaveObjInNonemptySetStmtResult::Success(p),
            )),
            ReleaseObjDefByKind::HaveObjInNonemptySetOrParamType { type_fact },
        ) => {
            let (offset, count) = parameter_offset(&p.statement.param_def, id, name)?;
            let stores = &p.store_and_infer_result.store_and_infer_results;
            if stores.len() != count {
                return Err(wrong());
            }
            Ok(vec![(type_fact, stores[offset].primary_fact_id())])
        }
        (
            ExecDefinitionStmtResult::DefineObj(ExecDefineObjStmtResult::HaveObjEqual(
                ExecHaveObjEqualStmtResult::Success(p),
            )),
            ReleaseObjDefByKind::HaveObjEqual { type_fact, equal },
        ) => {
            let (offset, count) = parameter_offset(&p.statement.param_def, id, name)?;
            let stores = &p.store_and_infer_result.store_and_infer_results;
            if stores.len() != 2 * count {
                return Err(wrong());
            }
            Ok(vec![
                (type_fact, stores[offset].primary_fact_id()),
                (equal, stores[count + offset].primary_fact_id()),
            ])
        }
        (
            ExecDefinitionStmtResult::DefineObj(ExecDefineObjStmtResult::HaveObjByExistFacts(
                ExecHaveObjByExistFactsStmtResult::Success(p),
            )),
            ReleaseObjDefByKind::HaveObjByExistFacts {
                type_fact,
                body_facts,
            },
        ) => {
            let (offset, count) = parameter_offset(&p.statement.param_def, id, name)?;
            let stores = &p.store_and_infer_result.store_and_infer_results;
            if body_facts.len() != p.statement.facts.len()
                || stores.len() != count + body_facts.len()
            {
                return Err(wrong());
            }
            let mut pairs = vec![(type_fact, stores[offset].primary_fact_id())];
            pairs.extend(
                body_facts
                    .iter()
                    .zip(&stores[count..])
                    .map(|(fact, store)| (fact, store.primary_fact_id())),
            );
            Ok(pairs)
        }
        (
            ExecDefinitionStmtResult::HaveFnEqual(ExecHaveFnEqualStmtResult::Success(p)),
            ReleaseObjDefByKind::HaveFnEqual {
                membership,
                equal_to_anon,
            },
        ) => {
            if p.statement.name.id != id || p.statement.name.name != name {
                return Err(wrong());
            }
            Ok(vec![
                (
                    membership,
                    p.store_and_infer_result.membership.primary_fact_id(),
                ),
                (
                    equal_to_anon,
                    p.store_and_infer_result.defining_equal.primary_fact_id(),
                ),
            ])
        }
        _ => Err(LeanCompileError::unsupported("ReleaseObj/DefinitionFamily")),
    }
}
