use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_negation_nonzero(
        &self,
        fact: &NotEqualFact,
        premise: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (object, zero, reverse) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Obj::ArithmeticOperator(ArithmeticOperator::Neg(negative)) = object else {
                continue;
            };
            if !is_exact_zero(zero) {
                continue;
            }
            if !matches!(source_subject(premise)?, Fact::AtomicFact(AtomicFact::NotEqualFact(p)) if p.left.ir()==negative.arg.ir() && p.right.ir()==zero.ir())
            {
                return Err(LeanCompileError::unsupported("NegationNonzero/Premise"));
            }
            let checked = self.compile_verify(premise, position)?.1;
            let arg = self.compile_object_reference(&negative.arg, position)?;
            let value = self.compile_object_reference(object, position)?;
            let a = self.compile_numeric_observation(&negative.arg, position)?;
            let n = self.compile_numeric_observation(object, position)?;
            let z = self.compile_numeric_observation(zero, position)?;
            let zero_equal = format!(
                "(({}).trans (congrArg M.number (by norm_num : {} = (0 : ℂ))))",
                z.1, z.0
            );
            let orientation = if reverse { ".symm" } else { "" };
            return Ok(format!("(by\n  have _premise : ¬ Litex.Same {arg} (Litex.number (M := M) 0) := fun h => {checked} (h.trans ({zero_equal}).symm)\n  have _native := Litex.NativeBridge.nativeNonzeroOfDenote {arg} {} {} _premise\n  have _negated := Litex.NativeBridge.notSameOfNativeNonzero {value} {} {} (by simpa only [neg_ne_zero] using _native)\n  exact fun h => _negated (h{orientation}.trans {zero_equal}))", a.0, a.1, n.0, n.1));
        }
        Err(LeanCompileError::unsupported("NegationNonzero/Subject"))
    }
}
