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
            // Selected-function uniqueness rebuilds its bound candidate with
            // a fresh ID. Only bound renaming is allowed; free source identity,
            // ordered carriers, premises and conclusions remain exact.
            let fresh_selected_candidate = matches!(definition,
            ExecDefinitionStmtResult::HaveFnByForallExistUnique(
                crate::execute::ExecHaveFnByForallExistUniqueStmtResult::Success(p),
            ) if *original_id == p.uniqueness_forall_fact_id
                && super::helper::instantiated_fact_matches(
                    &original, released, &std::collections::HashMap::new(),
                ));
            if original.ir() != released.ir() && !fresh_selected_candidate {
                return Err(LeanCompileError::new(
                    "ReleaseObj/Subject",
                    "The released fact differs from its introducing declaration's fact.",
                ));
            }
            self.validate_store(&store.store, released)?;
            let (proposition, reference) = if let Fact::ForallFact(forall) = released {
                // The original declaration already checked and published this
                // header. Release specializes that theorem to the canonical
                // semantic objects; it has no second forall-WD verification.
                let proposition = match (definition, &original) {
                    (
                        ExecDefinitionStmtResult::HaveFnByInduc(
                            crate::execute::ExecHaveFnByInducStmtResult::Success(p),
                        ),
                        Fact::ForallFact(source),
                    ) => {
                        let (prefix, mut bindings) = self.compile_canonical_predicate_header(
                            forall,
                            &declaration,
                            &std::collections::HashMap::new(),
                        )?;
                        let object = self.compile_object_reference(
                            &Obj::Identifier(proof.statement.name.clone()),
                            &declaration,
                        )?;
                        bindings.insert(p.statement.name.id, format!("(Litex.denote {object})"));
                        // The original case owns any returned literal's WD.
                        // Render there, substituting the public graph for self;
                        // do not hoist that private constructor into the caller.
                        let conclusion = self
                            .compile_recursive_published_conclusion(
                                p,
                                source,
                                &declaration,
                                &bindings,
                            )?
                            .ok_or_else(|| {
                                LeanCompileError::unsupported("ReleaseObj/RecursivePublication")
                            })?;
                        format!("({prefix}{conclusion})")
                    }
                    _ => self.compile_canonical_predicate_value(
                        released,
                        &declaration,
                        &std::collections::HashMap::new(),
                    )?,
                };
                let (parameters, _) = self.compile_canonical_predicate_binders(
                    &forall.typed_parameters,
                    &declaration,
                    &std::collections::HashMap::new(),
                )?;
                let mut binders = Vec::new();
                let mut arguments = Vec::new();
                for (index, (value, carrier)) in parameters.iter().enumerate() {
                    let member = format!("_released_member_{index}");
                    binders.push(format!(
                        "({value} : Litex.Obj (M := M) M.Value) ({member} : {carrier})"
                    ));
                    arguments.extend([value.clone(), member]);
                }
                // Apply object arguments explicitly so the original theorem's
                // implicit host and Representation are determined before its
                // remaining domains/conclusion are checked.
                let reference = if binders.is_empty() {
                    reference
                } else {
                    format!(
                        "(fun {} => {reference} {})",
                        binders.join(" "),
                        arguments.join(" ")
                    )
                };
                (proposition, reference)
            } else {
                (self.fact_proposition(released, &declaration)?, reference)
            };
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
    let obtained = match source {
        ExecDefinitionStmtResult::DefineObj(ExecDefineObjStmtResult::ObtainObjFromExistFact(
            crate::execute::ExecObtainObjFromExistFactStmtResult::Success(p),
        )) => Some((
            p.statement.equal_tos.iter().collect::<Vec<_>>(),
            &p.store_and_infer_result,
        )),
        ExecDefinitionStmtResult::DefineObj(ExecDefineObjStmtResult::ObtainObjFromAtomicFact(
            crate::execute::ExecObtainObjFromAtomicFactStmtResult::Success(p),
        )) => Some((
            p.statement.equal_tos.iter().collect::<Vec<_>>(),
            &p.store_and_infer_result,
        )),
        ExecDefinitionStmtResult::DefineObj(ExecDefineObjStmtResult::HaveByFnPreimage(
            crate::execute::ExecHaveByFnPreimageStmtResult::Success(p),
        )) => Some((
            p.preimage_parameters
                .groups
                .iter()
                .flat_map(|group| &group.params)
                .collect::<Vec<_>>(),
            &p.store_and_infer_result,
        )),
        _ => None,
    };
    if let Some((names, stores)) = obtained {
        let ReleaseObjDefByKind::HaveObjByExistFacts {
            type_fact,
            body_facts,
        } = released
        else {
            return Err(wrong());
        };
        let offset = names
            .iter()
            .position(|p| p.id == id && p.name == name)
            .ok_or_else(wrong)?;
        let stores = &stores.store_and_infer_results;
        if stores.len() < names.len() + body_facts.len() {
            return Err(wrong());
        }
        let mut pairs = vec![(type_fact, stores[offset].primary_fact_id())];
        pairs.extend(
            body_facts
                .iter()
                .zip(&stores[names.len()..])
                .map(|(fact, store)| (fact, store.primary_fact_id())),
        );
        return Ok(pairs);
    }
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
        (
            ExecDefinitionStmtResult::HaveFnEqualCaseByCase(
                crate::execute::ExecHaveFnEqualCaseByCaseStmtResult::Success(p),
            ),
            ReleaseObjDefByKind::HaveFnEqualCaseByCase {
                membership,
                case_foralls,
            },
        ) => {
            let stores = &p.store_and_infer_result;
            if p.statement.name.id != id
                || p.statement.name.name != name
                || case_foralls.len() != stores.case_defining.len()
            {
                return Err(wrong());
            }
            Ok(
                std::iter::once((membership, stores.membership.primary_fact_id()))
                    .chain(
                        case_foralls
                            .iter()
                            .zip(&stores.case_defining)
                            .map(|(fact, store)| (fact, store.primary_fact_id())),
                    )
                    .collect(),
            )
        }
        (
            ExecDefinitionStmtResult::HaveFnByInduc(
                crate::execute::ExecHaveFnByInducStmtResult::Success(p),
            ),
            ReleaseObjDefByKind::HaveFnByInduc {
                membership,
                case_foralls,
            },
        ) => {
            let stores = &p.store_and_infer_result;
            if p.statement.name.id != id
                || p.statement.name.name != name
                || case_foralls.len() != stores.case_defining.len()
            {
                return Err(wrong());
            }
            Ok(
                std::iter::once((membership, stores.membership.primary_fact_id()))
                    .chain(
                        case_foralls
                            .iter()
                            .zip(&stores.case_defining)
                            .map(|(fact, store)| (fact, store.primary_fact_id())),
                    )
                    .collect(),
            )
        }
        (
            ExecDefinitionStmtResult::HaveFnByForallExistUnique(
                crate::execute::ExecHaveFnByForallExistUniqueStmtResult::Success(p),
            ),
            ReleaseObjDefByKind::HaveFnByForallExistUnique {
                membership,
                property_forall,
                uniqueness_forall,
            },
        ) => {
            if p.statement.name.id != id || p.statement.name.name != name {
                return Err(wrong());
            }
            Ok(vec![
                (membership, p.membership.primary_fact_id()),
                (property_forall, p.property.primary_fact_id()),
                (uniqueness_forall, p.uniqueness.primary_fact_id()),
            ])
        }
        _ => Err(LeanCompileError::unsupported("ReleaseObj/DefinitionFamily")),
    }
}
