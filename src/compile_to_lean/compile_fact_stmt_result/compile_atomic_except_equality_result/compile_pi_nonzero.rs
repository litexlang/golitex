use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_pi_nonzero(
        &self,
        goal: &AtomicFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::NotEqualFact(fact) = goal else {
            return Err(LeanCompileError::unsupported("PiNonzero/Family"));
        };
        let reversed = match (&fact.left, &fact.right) {
            (Obj::Literal(Literal::Pi(_)), Obj::Literal(Literal::Number(n)))
                if n.normalized_value == "0" =>
            {
                false
            }
            (Obj::Literal(Literal::Number(n)), Obj::Literal(Literal::Pi(_)))
                if n.normalized_value == "0" =>
            {
                true
            }
            _ => return Err(LeanCompileError::unsupported("PiNonzero/Subjects")),
        };
        let left = self.compile_numeric_observation(&fact.left, position)?;
        let right = self.compile_numeric_observation(&fact.right, position)?;
        let native = "(Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos))";
        Ok(format!(
            "(Litex.NativeBridge.notSameOfDenoteNumber {} {} {} {} {} {} ({}{}))",
            self.compile_object_reference(&fact.left, position)?,
            self.compile_object_reference(&fact.right, position)?,
            left.0,
            right.0,
            left.1,
            right.1,
            if reversed { "Ne.symm " } else { "" },
            native
        ))
    }
}
