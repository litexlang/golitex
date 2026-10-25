use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::InferInFactIntersectBothResult;

impl LitexToLeanCompiler {
    pub(super) fn compile_intersection_inference(
        &self,
        proof: &InferInFactIntersectBothResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let Fact::AtomicFact(AtomicFact::InFact(member)) = seed else {
            return Err(LeanCompileError::unsupported("IntersectionInference/Seed"));
        };
        let Obj::SetOperator(SetOperator::Intersect(set)) = &member.set else {
            return Err(LeanCompileError::unsupported(
                "IntersectionInference/Carrier",
            ));
        };
        if proof.left_membership.primary_fact_id() == proof.right_membership.primary_fact_id()
            || [
                proof.left_membership.primary_fact_id(),
                proof.right_membership.primary_fact_id(),
            ]
            .contains(&member.fact_id)
        {
            return Err(LeanCompileError::unsupported(
                "IntersectionInference/Identity",
            ));
        }
        let mut declarations = Vec::new();
        for (i, (captured, bound)) in [&proof.left_membership, &proof.right_membership]
            .into_iter()
            .zip([&set.left, &set.right])
            .enumerate()
        {
            let prior = SourcePosition {
                before: position.before + i,
                ..*position
            };
            let fact = self.resolve_fact(captured.primary_fact_id(), &prior)?;
            if !matches!(&fact, Fact::AtomicFact(AtomicFact::InFact(p))
                if p.element.ir() == member.element.ir() && p.set.ir() == bound.ir())
            {
                return Err(LeanCompileError::unsupported(
                    "IntersectionInference/Subject",
                ));
            }
            self.validate_store(&captured.store, &fact)?;
            let term = format!(
                "(((Litex.inIntersect_iff {} {} {}).mp {}).{})",
                self.compile_object_reference(&member.element, &prior)?,
                self.compile_object_reference(&set.left, &prior)?,
                self.compile_object_reference(&set.right, &prior)?,
                compiled.1,
                i + 1
            );
            let formed = SourcePosition::new(
                Some(&prior),
                SourceOwner::InferredStore(&captured.store),
                usize::MAX,
            );
            declarations.push(self.emit_internal_fact(
                &fact,
                &(self.fact_proposition(&fact, &formed)?, term),
                &formed,
            )?);
        }
        Ok(declarations)
    }
}
