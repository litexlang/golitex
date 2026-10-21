use crate::prelude::*;

impl crate::compile_to_lean::LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_complex_arithmetic_closure(
        &self,
        goal: &InFact,
        position: &crate::compile_to_lean::source_position::SourcePosition<'_>,
    ) -> Result<String, crate::compile_to_lean::LeanCompileError> {
        if goal.set != Obj::StandardSet(StandardSet::C) {
            return Err(crate::compile_to_lean::LeanCompileError::new(
                "ArithmeticClosure/Carrier",
                "Complex closure proves only membership in C.",
            ));
        }
        let (law, fields) = match &goal.element {
            Obj::ArithmeticOperator(ArithmeticOperator::Add(_)) => ("addInC", "_arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2"),
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(_)) => ("subInC", "_arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2"),
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(_)) => ("mulInC", "_arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2"),
            Obj::ArithmeticOperator(ArithmeticOperator::Div(_)) => ("divInC", "_arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2.1 _arithmetic.wd.2.2"),
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(_)) => ("negInC", "_arithmetic.val.arg _arithmetic.wd"),
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(_)) => ("powObjInC", "_arithmetic"),
            _ => return Err(crate::compile_to_lean::LeanCompileError::unsupported(
                "ArithmeticClosure/Constructor",
            )),
        };
        // This selected builtin uses the already checked constructor domain.
        // Observing every operand as a native number would replay its entire
        // arithmetic subtree even though this rule only needs C-membership.
        let term = self.compile_object_reference(&goal.element, position)?;
        Ok(format!(
            "(by\n  let _arithmetic := {term}\n  exact Litex.{law} {fields})"
        ))
    }
}
