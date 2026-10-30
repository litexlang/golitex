use crate::prelude::*;
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_transitive_relation::TransitiveRelationProof;

pub(super) struct CompiledTransitiveRelation {
    pub middle: Obj,
    pub known_left_proof: String,
    pub residual_proof: String,
}

impl LitexToLeanCompiler {
    pub(super) fn compile_transitive_relation(
        &self,
        goal: &AtomicFact,
        proof: &TransitiveRelationProof,
        position: &SourcePosition<'_>,
    ) -> Result<CompiledTransitiveRelation, LeanCompileError> {
        let Fact::AtomicFact(known) = self.resolve_fact(proof.known_left_fact_id, position)? else {
            return Err(LeanCompileError::unsupported("Transitivity/KnownFamily"));
        };
        let Fact::AtomicFact(residual) = &proof.residual_fact else {
            return Err(LeanCompileError::unsupported("Transitivity/ResidualFamily"));
        };
        if !atomic_fact_has_positive_polarity(goal)
            || !same_atomic_family(goal, &known)
            || !same_atomic_family(goal, residual)
            || source_subject(&proof.proof_of_residual_fact)? != proof.residual_fact
        {
            return Err(LeanCompileError::unsupported("Transitivity/Subjects"));
        }
        let target = atomic_fact_args_ref(goal);
        let left = atomic_fact_args_ref(&known);
        let right = atomic_fact_args_ref(residual);
        if target.len() != 2
            || left.len() != 2
            || right.len() != 2
            || left[0].ir() != target[0].ir()
            || left[1].ir() != right[0].ir()
            || right[1].ir() != target[1].ir()
        {
            return Err(LeanCompileError::unsupported("Transitivity/Endpoints"));
        }
        let known_left_proof = self
            .cited_fact_reference(proof.known_left_fact_id, position)?
            .1;
        let residual_proof = self
            .compile_verify(&proof.proof_of_residual_fact, position)?
            .1;
        Ok(CompiledTransitiveRelation {
            middle: left[1].clone(),
            known_left_proof,
            residual_proof,
        })
    }
}
