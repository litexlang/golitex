//! Project a recorded power-set membership to its recorded subset FactId.
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::InferPowerSetMembershipProjectionResult;

impl LitexToLeanCompiler {
    pub(super) fn compile_power_set_inference(
        &self,
        proof: &InferPowerSetMembershipProjectionResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let Fact::AtomicFact(AtomicFact::InFact(member)) = seed else {
            return Err(LeanCompileError::unsupported("PowerSetInference/Seed"));
        };
        let Obj::SetOperator(SetOperator::PowerSet(power)) = &member.set else {
            return Err(LeanCompileError::unsupported(
                "PowerSetInference/CarrierEvidence",
            ));
        };
        let captured = &proof.derived;
        let fact = self.resolve_fact(captured.primary_fact_id(), position)?;
        if captured.primary_fact_id() == member.fact_id
            || !matches!(&fact,Fact::AtomicFact(AtomicFact::SubsetFact(p)) if p.left.ir()==member.element.ir() && p.right.ir()==power.set.ir())
        {
            return Err(LeanCompileError::unsupported("PowerSetInference/Subject"));
        }
        self.validate_store(&captured.store, &fact)?;
        let term = format!(
            "((Litex.inPowerSet_iff {} {}).mp {})",
            self.compile_object_reference(&member.element, position)?,
            self.compile_object_reference(&power.set, position)?,
            compiled.1
        );
        let formed = SourcePosition::new(
            Some(position),
            SourceOwner::InferredStore(&captured.store),
            usize::MAX,
        );
        Ok(vec![self.emit_internal_fact(
            &fact,
            &(self.fact_proposition(&fact, &formed)?, term),
            &formed,
        )?])
    }
}
