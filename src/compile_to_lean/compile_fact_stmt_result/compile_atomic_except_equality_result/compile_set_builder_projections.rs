use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::InferSetBuilderMembershipProjectionResult;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_set_builder_projections(
        &self,
        proof: &InferSetBuilderMembershipProjectionResult,
        source_fact: &Fact,
        source: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let mut declarations = Vec::new();
        let mut offset = 0;
        for step in &proof.steps {
            if step.template_expansion {
                return Err(LeanCompileError::unsupported(
                    "SetBuilder/TemplateProjection",
                ));
            }
            if step.equality_path.len() > 1 {
                return Err(LeanCompileError::new(
                    "SetBuilder/ProjectionResolution",
                    "Exact-property resolution records at most one direct equality edge.",
                ));
            }
            let member_fact = Fact::AtomicFact(AtomicFact::InFact(step.source_membership.clone()));
            let parent_proof = if &member_fact == source_fact {
                source.1.clone()
            } else {
                let (actual, citation) =
                    self.cited_fact_reference(member_fact.fact_id(), position)?;
                if *actual != member_fact {
                    return Err(LeanCompileError::new(
                        "SetBuilder/ProjectionSource",
                        "Projection cites another input membership.",
                    ));
                }
                citation
            };
            let builder = Obj::SetFormer(SetFormer::SetBuilder(step.builder.clone()));
            let mut current = step.source_membership.set.clone();
            let mut equality = format!(
                "(Litex.sameRefl {})",
                self.compile_object_reference(&current, position)?
            );
            for (from, to, id) in &step.equality_path {
                if from.ir() != current.ir() || from.ir() == to.ir() {
                    return Err(LeanCompileError::new("SetBuilder/ProjectionPath", "Recorded builder resolution is discontinuous or does not change its subject."));
                }
                let edge = self.compile_registered_equality(*id, from, to, position)?;
                equality = format!("(({equality}).trans {edge})");
                current = to.clone();
            }
            if current.ir() != builder.ir() {
                return Err(LeanCompileError::new(
                    "SetBuilder/ProjectionEndpoint",
                    "Resolution does not end at the captured source builder.",
                ));
            }
            let a = self.compile_object_reference(&step.source_membership.element, position)?;
            let built = self.compile_object_reference(&builder, position)?;
            let member = if step.equality_path.is_empty() && step.source_membership.set == builder {
                parent_proof
            } else {
                format!("(Litex.inOfSame {a} {a} {} _litex_builder (Litex.sameRefl {a}) {equality} {parent_proof})", self.compile_object_reference(&step.source_membership.set, position)?)
            };
            let projected = format!("(let _litex_builder := {built}; (Litex.inSetBuilderObj_iff {a} _litex_builder).mp {member})");
            let substitution = HashMap::from([(
                step.builder.param_binding.id,
                step.source_membership.element.clone(),
            )]);
            let mut next = 0;
            for projection in &step.projections {
                let derived = projection.stored();
                let fact = match &derived.store {
                    StoreFactResult::AtomicFact(s) => Fact::AtomicFact(s.fact.clone()),
                    StoreFactResult::AndFact(s) => Fact::AndFact(s.fact.clone()),
                    StoreFactResult::ChainFact(s) => Fact::ChainFact(s.fact.clone()),
                    _ => {
                        return Err(LeanCompileError::unsupported(
                            "SetBuilder/CompoundProjection",
                        ))
                    }
                };
                let selected = match projection {
                    crate::store_fact_and_infer::InferSetBuilderProjectionResult::BaseMembership(_) => 0,
                    crate::store_fact_and_infer::InferSetBuilderProjectionResult::Condition { condition_index, .. } => condition_index.checked_add(1).ok_or_else(|| LeanCompileError::new("SetBuilder/ProjectionIndex", "Source condition index overflowed."))?,
                };
                if selected < next || selected > step.builder.facts.len() {
                    return Err(LeanCompileError::new("SetBuilder/ProjectionIndex", "Captured projections do not retain their original source order or condition range."));
                }
                let matches = if selected == 0 {
                    matches!(&fact, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == step.source_membership.element.ir() && f.set.ir() == step.builder.param_set.ir())
                } else {
                    instantiated_fact_matches(
                        &crate::instantiate::quantifier_free_fact_to_fact(
                            step.builder.facts[selected - 1].clone(),
                        ),
                        &fact,
                        &substitution,
                    )
                };
                if !matches {
                    return Err(LeanCompileError::new(
                        "SetBuilder/ProjectionSubject",
                        "Captured store differs from its selected source bound or condition.",
                    ));
                }
                next = selected + 1;
                let term = if selected == 0 {
                    format!("({projected}).choose")
                } else {
                    let mut cursor = format!("({projected}).choose_spec");
                    for _ in 1..selected {
                        cursor = format!("({cursor}).choose_spec");
                    }
                    if selected < step.builder.facts.len() {
                        format!("({cursor}).choose")
                    } else {
                        cursor
                    }
                };
                let prior = SourcePosition {
                    before: position.before + offset,
                    ..*position
                };
                self.validate_store(&derived.store, &fact)?;
                let formed = SourcePosition {
                    parent: Some(&prior),
                    owner: SourceOwner::InferredStore(&derived.store),
                    before: usize::MAX,
                };
                // The checked builder predicate already carries the clause's
                // formation. Project its semantic proposition without inventing
                // a second WD tree for the substituted function applications.
                let compiled = (
                    self.compile_function_raw_predicate(&fact, &formed, &HashMap::new())?,
                    term,
                );
                declarations.push(self.emit_internal_fact(&fact, &compiled, position)?);
                // Project the fact just emitted. Re-elaborating the builder
                // inside And.left/right loses the predicate's expected type
                // and duplicates its captured formation proofs.
                let name = format!("h_{}", fact.fact_id().value());
                let reference = if position.is_local() {
                    name
                } else {
                    self.context_application(&name, position)
                };
                let stored = (compiled.0, reference);
                declarations.extend(self.compile_stored_projections(
                    &derived.store,
                    &fact,
                    &stored,
                    &formed,
                )?);
                offset += 1;
            }
        }
        Ok(declarations)
    }
}
