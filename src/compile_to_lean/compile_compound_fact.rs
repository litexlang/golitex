use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
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
            return self.compile_compound_known_forall(
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
            checked.push(self.compile_verify(child, &prior)?.1);
        }
        let complete = SourcePosition {
            before: checked.len(),
            ..*position
        };
        Ok((
            self.fact_proposition(&Fact::ChainFact(proof.fact.clone()), &complete)?,
            compound_proof(checked)?,
        ))
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
            return self.compile_compound_known_forall(
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
            checked.push(self.compile_verify(child, &prior)?.1);
        }
        let complete = SourcePosition {
            before: checked.len(),
            ..*position
        };
        Ok((
            self.fact_proposition(&Fact::AndFact(proof.fact.clone()), &complete)?,
            compound_proof(checked)?,
        ))
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

fn compound_proof(mut proofs: Vec<String>) -> Result<String, LeanCompileError> {
    let Some(mut proof) = proofs.pop() else {
        return Err(LeanCompileError::unsupported("Compound/Empty"));
    };
    while let Some(previous) = proofs.pop() {
        proof = format!("(And.intro {previous} {proof})");
    }
    Ok(proof)
}
