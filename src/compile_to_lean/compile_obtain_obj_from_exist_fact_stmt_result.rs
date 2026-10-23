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
        let ObtainExistVerifySuccess::Exist(verified) = &proof.verify_exist else {
            return Err(LeanCompileError::unsupported("Obtain/Unique"));
        };
        let ExistShapedFact::Exist(source) = &proof.statement.fact else {
            return Err(LeanCompileError::unsupported("Obtain/SourceFamily"));
        };
        if verified.fact != proof.statement.fact {
            return Err(LeanCompileError::new(
                "Obtain/SourceSubject",
                "The retained verification proves another existential.",
            ));
        }
        validate_obtain_output_names(source, &proof.statement.equal_tos)?;
        let verified_position = SourcePosition {
            before: 0,
            ..*position
        };
        let (proposition, tail) =
            self.compile_verify_plain_exist_success(verified, &verified_position)?;
        let tail = format!("(show {proposition} from {tail})");
        self.compile_obtain_elimination(
            source,
            &verified.well_defined_proof,
            &proof.statement.equal_tos,
            &proof.store_and_infer_result,
            &HashMap::new(),
            tail,
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
        original_parent: &SourcePosition<'_>,
        position: &SourcePosition<'_>,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let parameters = source.typed_parameters.ordered_param_ids();
        let count = parameters.len();
        let stores = &captured.store_and_infer_results;
        if count == 0 || outputs.len() != count || stores.len() != count + source.facts.len() {
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
        for (index, store) in stores.iter().enumerate() {
            let completed = SourcePosition {
                before: 2 + index,
                ..*position
            };
            let actual = self.resolve_fact(store.primary_fact_id(), &completed)?;
            let expected = if index < count {
                self.resolve_fact(
                    formation
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
                    .skip(count)
                    .map(|store| format!("h_{}", store.primary_fact_id().value())),
            );
            if source.facts.is_empty() {
                names.push("_".into());
            }
            lines.push(format!("rcases {tail} with ⟨{}⟩", names.join(", ")));
        }

        for (index, store) in stores.iter().enumerate() {
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
                let last = index + 1 == stores.len() && index >= count;
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
        Ok(lines.join("\n\n"))
    }
}

#[cfg(test)]
#[path = "../../tests/unit/compile_to_lean/obtain/tests.rs"]
mod tests;
