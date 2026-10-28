use super::helper::exist_instance_matches;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::SearchProofByKnownForallFact;
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactWellDefinedProof;
use crate::prelude::*;
use std::collections::{HashMap, HashSet};

impl LitexToLeanCompiler {
    /// Apply the cited universal, keeping its free parameter substitution
    /// separate from alpha-renaming the existential witnesses.
    pub(super) fn compile_exist_known_forall(
        &self,
        goal_family: &ExistShapedFact,
        formation: &ExistShapedFactWellDefinedProof,
        proof: &SearchProofByKnownForallFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let registered = self.cited_fact_reference(proof.detailed_ref().cite.fact_id, position)?;
        let Fact::ForallFact(source) = registered.0 else {
            return Err(LeanCompileError::unsupported("Exist/KnownForallFamily"));
        };
        let ForallConclusionLocation::DirectThenFact(location) =
            &proof.detailed_ref().cite.location
        else {
            return Err(LeanCompileError::unsupported("Exist/KnownForallLocation"));
        };
        // Match Runtime's family rule: unique existence can also prove plain
        // existence, but no positive/negative or plain/unique reversal is valid.
        let selected = source.then_facts.get(location.then_fact_index);
        let (selected, source_unique) = match (selected, goal_family) {
            (Some(ExistOrAndChainAtomicFact::ExistFact(f)), ExistShapedFact::Exist(_)) => {
                (f, false)
            }
            (
                Some(ExistOrAndChainAtomicFact::ExistUniqueFact(f)),
                ExistShapedFact::Exist(_) | ExistShapedFact::ExistUnique(_),
            ) => (f, true),
            (Some(ExistOrAndChainAtomicFact::NotExistFact(f)), ExistShapedFact::NotExist(_)) => {
                (f, false)
            }
            _ => return Err(LeanCompileError::unsupported("Exist/KnownForallConclusion")),
        };
        let goal = goal_family.plain();
        let negative = matches!(goal_family, ExistShapedFact::NotExist(_));
        let unique = matches!(goal_family, ExistShapedFact::ExistUnique(_));
        let parameters = source.typed_parameters.ordered_param_ids();
        if parameters.len() != proof.detailed_ref().forall_parameters_match_what_args.len() {
            return Err(LeanCompileError::unsupported("Exist/KnownForallArity"));
        }
        let substitution: HashMap<_, _> = parameters
            .iter()
            .copied()
            .zip(
                proof
                    .detailed_ref()
                    .forall_parameters_match_what_args
                    .iter()
                    .cloned(),
            )
            .collect();
        if substitution.len() != parameters.len()
            || !exist_instance_matches(selected, goal, &substitution)
        {
            return Err(LeanCompileError::unsupported("Exist/KnownForallSubject"));
        }
        let renamed: HashMap<_, _> = selected
            .typed_parameters
            .ordered_param_ids()
            .into_iter()
            .zip(
                goal.typed_parameters
                    .groups
                    .iter()
                    .flat_map(|group| &group.params)
                    .map(|param| Obj::Identifier(IdentifierObj::from_bound_name(param))),
            )
            .collect();
        let source_args = crate::ast::fact::plain_exist_fact_free_args_ref(selected);
        let goal_args = crate::ast::fact::plain_exist_fact_free_args_ref(goal);
        if source_args.len() != goal_args.len()
            || goal_args.len() != proof.detailed_ref().arg_match_proofs.len()
        {
            return Err(LeanCompileError::unsupported("Exist/KnownForallMatchArity"));
        }
        let mut patterns = Vec::new();
        let mut bound = HashSet::new();
        for ((original, goal_arg), matched) in source_args
            .iter()
            .zip(&goal_args)
            .zip(&proof.detailed_ref().arg_match_proofs)
        {
            // The producer retained the pattern after aligning the inner
            // witnesses. Validate it against the cited original before replay.
            let pattern = match matched.detailed_ref() {
                DetailedForallConclusionArgMatchProof::BoundParam { pattern, .. }
                | DetailedForallConclusionArgMatchProof::ByStructure { pattern, .. }
                | DetailedForallConclusionArgMatchProof::NonParamEqual { pattern, .. } => pattern,
                DetailedForallConclusionArgMatchProof::ReboundParamEqual { .. } => original,
            };
            if !instantiated_object_matches(original, pattern, &renamed) {
                return Err(LeanCompileError::unsupported(
                    "Exist/KnownForallAlignedPattern",
                ));
            }
            self.compile_forall_argument_match(
                pattern,
                goal_arg,
                matched,
                &substitution,
                &mut bound,
                None,
            )?;
            patterns.push(pattern);
        }
        let current = SourcePosition::new(Some(position), SourceOwner::KnownApplication(proof), 0);
        let (mut lines, arguments) =
            self.compile_known_application_requirements(source, proof, &current)?;
        let application = if arguments.is_empty() {
            registered.1
        } else {
            format!("({} {})", registered.1, arguments.join(" "))
        };
        let application = conjunction_projection(
            &application,
            location.then_fact_index,
            source.then_facts.len(),
        );
        let names: Vec<_> = goal
            .typed_parameters
            .groups
            .iter()
            .flat_map(|group| &group.params)
            .zip(
                &formation
                    .detailed_ref()
                    .introduced_params
                    .defined_params
                    .store_and_infer_results,
            )
            .flat_map(|(parameter, store)| {
                [
                    format!("_value_i{}", parameter.id.value()),
                    format!("h_{}", store.primary_fact_id().value()),
                ]
            })
            .chain(goal.facts.iter().map(|fact| {
                format!(
                    "h_{}",
                    crate::instantiate::quantifier_free_fact_to_fact(fact.clone())
                        .fact_id()
                        .value()
                )
            }))
            .collect();
        let names = names.join(", ");
        let empty_body = if goal.facts.is_empty() { ", _" } else { "" };
        let existence = if negative {
            lines.push("intro _exist_candidate".to_string());
            "_exist_candidate".to_string()
        } else if unique {
            lines.push(format!(
                "rcases {application} with ⟨_known_exists, _known_unique⟩"
            ));
            "_known_exists".to_string()
        } else if source_unique {
            format!("({application}).1")
        } else {
            application.clone()
        };
        lines.push(format!("rcases {existence} with ⟨{names}{empty_body}⟩"));
        let (_, definitions) = self.compile_exist_constructor_prefix(
            goal,
            formation,
            goal.typed_parameters.ordered_param_ids().len(),
            goal.facts.len(),
            position,
        )?;
        lines.extend(definitions);
        let mut bound = HashSet::new();
        for (index, ((pattern, goal_arg), matched)) in patterns
            .iter()
            .zip(&goal_args)
            .zip(&proof.detailed_ref().arg_match_proofs)
            .enumerate()
        {
            let prior = SourcePosition {
                before: index,
                ..current
            };
            // The actual cited existential supplies these witnesses and guards.
            // Formation-local constructors are interpreted only under that scope.
            let witnesses = SourcePosition::new(
                Some(&prior),
                SourceOwner::ExistWD(goal, formation),
                usize::MAX,
            );
            let (old, equality) = self.compile_forall_argument_match(
                pattern,
                goal_arg,
                matched,
                &substitution,
                &mut bound,
                Some(&witnesses),
            )?;
            lines.push(format!(
                "have _exist_match_{index} : Litex.Same {} {} := {equality}",
                self.compile_object_reference(&old, &witnesses)?,
                self.compile_object_reference(goal_arg, &witnesses)?
            ));
        }
        let empty_body = if goal.facts.is_empty() {
            ", True.intro"
        } else {
            ""
        };
        lines.push(if negative {
            format!("exact ({application}) ⟨{names}{empty_body}⟩")
        } else if unique {
            format!("exact ⟨⟨{names}{empty_body}⟩, _known_unique⟩")
        } else {
            format!("exact ⟨{names}{empty_body}⟩")
        });
        Ok(format!(
            "(by\n  {}\n)",
            lines.join("\n").replace('\n', "\n  ")
        ))
    }
}
