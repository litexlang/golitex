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
        match &goal.element {
            Obj::ArithmeticOperator(
                ArithmeticOperator::Add(_)
                | ArithmeticOperator::Sub(_)
                | ArithmeticOperator::Mul(_)
                | ArithmeticOperator::Div(_)
                | ArithmeticOperator::Neg(_)
                | ArithmeticOperator::Pow(_),
            ) => {
                // The selected leaf relies on this original constructor's WD.
                // Numeric observation replays those exact checked children and
                // guards and returns its construction-derived C-membership.
                Ok(self.compile_numeric_observation(&goal.element, position)?.2)
            }
            _ => Err(crate::compile_to_lean::LeanCompileError::unsupported(
                "ArithmeticClosure/Constructor",
            )),
        }
    }
}
