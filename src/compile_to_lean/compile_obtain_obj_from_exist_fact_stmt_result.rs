use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::{ExecObtainObjFromExistFactStmtResult, ObtainExistVerifySuccess};
use crate::prelude::*;
use std::collections::{HashMap, HashSet};

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_obtain_exist_statement(
        &self,
        result: &ExecObtainObjFromExistFactStmtResult,
        position: &SourcePosition<'_>,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let ExecObtainObjFromExistFactStmtResult::Success(proof) = result else {
            return Err(LeanCompileError::unsupported("Obtain/Failed"));
        };
        let verified_position = SourcePosition {
            before: 0,
            ..*position
        };
        let (fact, formation, compiled, unique) = match &proof.verify_exist {
            ObtainExistVerifySuccess::Exist(p) => (
                &p.fact,
                &p.well_defined_proof,
                self.compile_verify_plain_exist_success(p, &verified_position)?,
                false,
            ),
            ObtainExistVerifySuccess::ExistUnique(p) => (
                &p.fact,
                &p.well_defined_proof,
                self.compile_verify_unique_success(p, &verified_position)?,
                true,
            ),
        };
        if *fact != proof.statement.fact {
            return Err(LeanCompileError::new(
                "Obtain/SourceSubject",
                "The retained verification proves another existential.",
            ));
        }
        let source = fact.plain();
        validate_obtain_output_names(source, &proof.statement.equal_tos)?;
        let evidence = format!("(show {} from {})", compiled.0, compiled.1);
        let tail = if unique {
            format!("({evidence}).1")
        } else {
            evidence.clone()
        };
        let uniqueness = unique.then(|| format!("({evidence}).2"));
        self.compile_obtain_elimination(
            source,
            formation,
            &proof.statement.equal_tos,
            &proof.store_and_infer_result,
            &HashMap::new(),
            tail,
            uniqueness.as_deref(),
            &verified_position,
            position,
            local,
        )
    }

    /// Eliminate the actual existential and replay its ordered output stores.
    /// Obtain renames its binders; have-by-existence retains their identities.
    pub(in crate::compile_to_lean) fn compile_obtain_elimination(
        &self,
        source: &PlainExistFact,
        formation: &crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactWellDefinedProof,
        outputs: &[BoundName],
        captured: &StoreHaveObjAndInferResult,
        outer_substitution: &HashMap<IdentifierId, Obj>,
        mut tail: String,
        uniqueness: Option<&str>,
        original_parent: &SourcePosition<'_>,
        position: &SourcePosition<'_>,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let parameters = source.typed_parameters.ordered_param_ids();
        let count = parameters.len();
        let stores = &captured.store_and_infer_results;
        let primary_count = count + source.facts.len();
        if count == 0
            || outputs.len() != count
            || stores.len() != primary_count + usize::from(uniqueness.is_some())
        {
            return Err(LeanCompileError::new(
                "Obtain/Stages",
                "Obtain needs each original renamed parameter and body store in order.",
            ));
        }
        let mut output_ids = HashSet::new();
        let renaming: HashMap<_, _> = parameters
            .iter()
            .copied()
            .zip(
                outputs
                    .iter()
                    .map(|name| Obj::Identifier(IdentifierObj::from_bound_name(name))),
            )
            .collect();
        let same_binders = outputs
            .iter()
            .zip(&parameters)
            .all(|(name, id)| name.id == *id);
        if renaming.len() != count
            || outputs.iter().any(|name| {
                !output_ids.insert(name.id) || (!same_binders && parameters.contains(&name.id))
            })
        {
            return Err(LeanCompileError::unsupported("Obtain/ParameterIdentity"));
        }
        let mut substitution = outer_substitution.clone();
        substitution.extend(renaming);
        self.validate_parameter_store_capture(captured)?;
        // Validate against the original formation, before giving any returned
        // fact a Lean name. No new verification is performed for the rename.
        let original = SourcePosition::new(
            Some(original_parent),
            SourceOwner::ExistWD(source, formation),
            usize::MAX,
        );
        for (index, store) in stores.iter().take(primary_count).enumerate() {
            let completed = SourcePosition {
                before: 2 + index,
                ..*position
            };
            let actual = self.resolve_fact(store.primary_fact_id(), &completed)?;
            let expected = if index < count {
                self.resolve_fact(
                    formation
                        .detailed_ref()
                        .introduced_params
                        .defined_params
                        .store_and_infer_results[index]
                        .primary_fact_id(),
                    &original,
                )?
            } else {
                crate::instantiate::quantifier_free_fact_to_fact(
                    source.facts[index - count].clone(),
                )
            };
            if !instantiated_fact_matches(&expected, &actual, &substitution) {
                return Err(LeanCompileError::new("Obtain/StoreSubject", "The returned store is not the original existential clause with its exact renamed binders."));
            }
            self.validate_store(&store.store, &actual)?;
        }

        let mut lines = Vec::new();
        if local {
            let mut names = Vec::new();
            for (parameter, store) in outputs.iter().zip(stores) {
                names.push(format!("_value_i{}", parameter.id.value()));
                names.push(format!("h_{}", store.primary_fact_id().value()));
            }
            names.extend(
                stores
                    .iter()
                    .take(primary_count)
                    .skip(count)
                    .map(|store| format!("h_{}", store.primary_fact_id().value())),
            );
            if source.facts.is_empty() {
                names.push("_".into());
            }
            lines.push(format!("rcases {tail} with ⟨{}⟩", names.join(", ")));
        }

        for (index, store) in stores.iter().take(primary_count).enumerate() {
            let completed = SourcePosition {
                before: 2 + index,
                ..*position
            };
            if !local && index < count {
                let name = format!("_value_i{}", outputs[index].id.value());
                lines.push(format!("noncomputable def {name}{} : Litex.Obj (M := M) M.Value :=\n  Classical.choose ({tail})", self.context_header(position)?));
                tail = format!("(Classical.choose_spec ({tail}))");
            }
            let fact = self.resolve_fact(store.primary_fact_id(), &completed)?;
            let proposition = self.fact_proposition(&fact, &completed)?;
            let name = format!("h_{}", fact.fact_id().value());
            if !local {
                let last = index + 1 == primary_count && index >= count;
                let evidence = if last {
                    tail.clone()
                } else {
                    format!("(Classical.choose ({tail}))")
                };
                lines.push(self.emit_internal_fact(
                    &fact,
                    &(proposition.clone(), evidence),
                    &completed,
                )?);
                if !last {
                    tail = format!("(Classical.choose_spec ({tail}))");
                }
            }
            let reference = if local {
                name
            } else {
                self.context_application(&name, position)
            };
            let compiled = (proposition, reference);
            lines.extend(if index < count {
                self.compile_parameter_inferences(store, &fact, &compiled, &completed)?
            } else {
                self.compile_stored_inferences(store, &fact, &compiled, &completed)?
            });
        }
        if let Some(unique) = uniqueness {
            let completed = SourcePosition {
                before: 2 + primary_count,
                ..*position
            };
            lines.push(self.compile_unique_forall_store(
                source,
                &stores[primary_count].store,
                unique,
                false,
                &completed,
            )?);
        }
        Ok(lines.join("\n\n"))
    }
}

#[cfg(test)]
#[path = "../../tests/unit/compile_to_lean/obtain/tests.rs"]
mod tests;
