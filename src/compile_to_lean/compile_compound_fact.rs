use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_and_fact::VerifyAndFactResult;
use crate::execute::execute_fact_stmt::verify_chain_fact::VerifyChainFactResult;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_verify_chain_result(
        &self,
        result: &VerifyChainFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let VerifyChainFactResult::Success(proof) = result else {
            return Err(LeanCompileError::unsupported("Chain/Failed"));
        };
        if let Some(known) = &proof.known_forall {
            if !proof.adjacent.is_empty() {
                return Err(LeanCompileError::unsupported("Chain/CompetingRoutes"));
            }
            return self.compile_known_application(
                &Fact::ChainFact(proof.fact.clone()),
                known,
                position,
            );
        }
        if proof.adjacent.len() != proof.fact.prop_names.len() || proof.adjacent.is_empty() {
            return Err(LeanCompileError::new(
                "Chain/AdjacentArity",
                "The chain omits an original adjacent verification.",
            ));
        }
        let mut checked = Vec::new();
        let mut bindings = Vec::new();
        for (index, child) in proof.adjacent.iter().enumerate() {
            let subject = source_subject(child)?;
            let expected = chain_edge(&proof.fact, index, subject.fact_id())?;
            if subject != Fact::AtomicFact(expected) {
                return Err(LeanCompileError::new("Chain/AdjacentSubject", "The ordered adjacent proof has different operands, direction or source identity."));
            }
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            // Each edge retains its own WD checks. Earlier emitted endpoints
            // can supply ByKnown references without rebuilding their constructors.
            if let VerifyFactResult::Equality(edge) = child {
                if let VerifyEqualityResult::Success(edge) = edge.as_ref() {
                    for (side, (object, wd)) in [
                        (
                            &edge.fact.left,
                            &edge.well_defined_proof.detailed_ref().left,
                        ),
                        (
                            &edge.fact.right,
                            &edge.well_defined_proof.detailed_ref().right,
                        ),
                    ]
                    .into_iter()
                    .enumerate()
                    {
                        ensure_object(object, wd)?;
                        let locals = SourcePosition::new(
                            Some(&prior),
                            SourceOwner::ChainObjects(result, index * 2 + side),
                            0,
                        );
                        let original =
                            SourcePosition::new(Some(&locals), SourceOwner::Verify(child), side);
                        let term = self.compile_wd(wd, &original)?;
                        if !matches!(
                            object,
                            Obj::Identifier(_) | Obj::Literal(_) | Obj::StandardSet(_)
                        ) {
                            bindings.push(format!(
                                "let _chain_wd_{}_{} := {term}",
                                proof.fact.fact_id.value(),
                                index * 2 + side
                            ));
                        }
                    }
                }
            }
            let locals = SourcePosition::new(
                Some(&prior),
                SourceOwner::ChainObjects(result, (index + 1) * 2),
                0,
            );
            checked.push(self.compile_verify(child, &locals)?);
        }
        let (proposition, proof) = compile_checked_components(checked)?;
        let wrap = |term: String| {
            if bindings.is_empty() {
                term
            } else {
                format!(
                    "(by\n  {}\n  exact {})",
                    bindings.join("\n").replace('\n', "\n  "),
                    term.replace('\n', "\n  ")
                )
            }
        };
        Ok((wrap(proposition), wrap(proof)))
    }

    pub(in crate::compile_to_lean) fn compile_verify_and_result(
        &self,
        result: &VerifyAndFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let VerifyAndFactResult::Success(proof) = result else {
            return Err(LeanCompileError::unsupported("And/Failed"));
        };
        if let Some(known) = &proof.known_forall {
            if !proof.components.is_empty() {
                return Err(LeanCompileError::unsupported("And/CompetingRoutes"));
            }
            return self.compile_known_application(
                &Fact::AndFact(proof.fact.clone()),
                known,
                position,
            );
        }
        if proof.components.len() != proof.fact.facts.len() || proof.components.is_empty() {
            return Err(LeanCompileError::new(
                "And/ComponentArity",
                "The conjunction omits an original component verification.",
            ));
        }
        let mut checked = Vec::new();
        for (index, (atomic, child)) in proof.fact.facts.iter().zip(&proof.components).enumerate() {
            if source_subject(child)? != Fact::AtomicFact(atomic.clone()) {
                return Err(LeanCompileError::new(
                    "And/ComponentSubject",
                    "The ordered component proof has a different source subject or identity.",
                ));
            }
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            checked.push(self.compile_verify(child, &prior)?);
        }
        compile_checked_components(checked)
    }
}

pub(super) fn chain_edge(
    chain: &ChainFact,
    index: usize,
    fact_id: FactId,
) -> Result<AtomicFact, LeanCompileError> {
    if chain.objs.len() != chain.prop_names.len() + 1 || index >= chain.prop_names.len() {
        return Err(LeanCompileError::new(
            "Chain/Shape",
            "The chain has another object or edge arity.",
        ));
    }
    let AtomicName::Plain { name } = &chain.prop_names[index] else {
        return Err(LeanCompileError::unsupported("Chain/QualifiedRelation"));
    };
    let left = chain.objs[index].clone();
    let right = chain.objs[index + 1].clone();
    let line_file = Some(crate::store_fact_and_infer::helper::chain_line_file(chain));
    Ok(match name.as_str() {
        "=" => EqualFact {
            fact_id,
            left,
            right,
            line_file,
        }
        .into(),
        "!=" => NotEqualFact {
            fact_id,
            left,
            right,
            line_file,
        }
        .into(),
        "<" => LessFact {
            fact_id,
            left,
            right,
            line_file,
        }
        .into(),
        "<=" => LessEqualFact {
            fact_id,
            left,
            right,
            line_file,
        }
        .into(),
        ">" => GreaterFact {
            fact_id,
            left,
            right,
            line_file,
        }
        .into(),
        ">=" => GreaterEqualFact {
            fact_id,
            left,
            right,
            line_file,
        }
        .into(),
        _ => return Err(LeanCompileError::unsupported("Chain/Relation")),
    })
}

/// Keep the proposition compiled alongside each proof instead of rebuilding it.
fn compile_checked_components(
    mut components: Vec<(String, String)>,
) -> Result<(String, String), LeanCompileError> {
    let Some((mut proposition, mut proof)) = components.pop() else {
        return Err(LeanCompileError::unsupported("Compound/Empty"));
    };
    while let Some((prior_proposition, prior_proof)) = components.pop() {
        proposition = format!("({prior_proposition}) ∧ ({proposition})");
        proof = format!("(And.intro {prior_proof} {proof})");
    }
    Ok((proposition, proof))
}
