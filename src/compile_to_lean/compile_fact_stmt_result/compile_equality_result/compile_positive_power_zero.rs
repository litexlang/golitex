use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_positive_power_zero(
        &self,
        goal: &EqualFact,
        premise: &EqualFactSearchedProof,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (base, zero, reversed) = if is_exact_zero(&goal.right) {
            (&goal.left, &goal.right, false)
        } else if is_exact_zero(&goal.left) {
            (&goal.right, &goal.left, true)
        } else {
            return Err(LeanCompileError::unsupported("PositivePowerZero/Zero"));
        };
        if requirements.len() != 2
            || membership_subject(&source_subject(&requirements[0])?, base)? != StandardSet::C
        {
            return Err(LeanCompileError::unsupported("PositivePowerZero/Base"));
        }
        let Fact::AtomicFact(AtomicFact::InFact(exponent)) = source_subject(&requirements[1])?
        else {
            return Err(LeanCompileError::unsupported("PositivePowerZero/Exponent"));
        };
        if exponent.set != Obj::StandardSet(StandardSet::NPos) {
            return Err(LeanCompileError::unsupported("PositivePowerZero/Exponent"));
        }
        let mut children = Vec::new();
        for (index, requirement) in requirements.iter().enumerate() {
            let prior = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(requirements),
                index,
            );
            children.push(self.compile_verify(requirement, &prior)?.1);
        }
        let complete = SourcePosition::new(
            Some(position),
            SourceOwner::EqualityRequirements(requirements),
            requirements.len(),
        );
        // The selected elementary rule's two original subjects fix this
        // obligation. No new fact or WD certificate is registered here.
        let power = Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
            base: Box::new(base.clone()),
            exponent: Box::new(exponent.element),
        }));
        let obligation = EqualFact {
            fact_id: goal.fact_id,
            left: power.clone(),
            right: zero.clone(),
            line_file: goal.line_file.clone(),
        };
        let equality = self.compile_equality_search(&obligation, premise, &complete)?;
        let term = self.compile_object_reference(&power, &complete)?;
        let proof = format!(
            "(Litex.sameBaseZeroOfPositivePowerZero {term} {} {} {equality})",
            children[0], children[1]
        );
        Ok(if reversed {
            format!("({proof}).symm")
        } else {
            proof
        })
    }
}
