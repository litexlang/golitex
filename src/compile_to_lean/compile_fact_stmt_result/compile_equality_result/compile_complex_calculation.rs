use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::rational_expression::exact_complex::exact_complex_coordinates;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_closed_complex_relation(
        &self,
        left: &Obj,
        right: &Obj,
        values: &ClosedValuePair,
        equal: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let route = if equal {
            "ClosedEquality/Values"
        } else {
            "ClosedNotEqual/Values"
        };
        let ClosedValuePair::Complex {
            left_real,
            left_imaginary,
            right_real,
            right_imaginary,
        } = values
        else {
            return Err(LeanCompileError::unsupported("ClosedComplex/Certificate"));
        };
        let (Some(a), Some(b)) = (
            exact_complex_coordinates(left),
            exact_complex_coordinates(right),
        ) else {
            return Err(LeanCompileError::unsupported("ClosedComplex/Expression"));
        };
        if &a.0 != left_real
            || &a.1 != left_imaginary
            || &b.0 != right_real
            || &b.1 != right_imaginary
            || (a == b) != equal
        {
            return Err(LeanCompileError::unsupported(route));
        }
        let x = self.compile_numeric_observation(left, position)?;
        let y = self.compile_numeric_observation(right, position)?;
        let law = if equal {
            "sameOfDenoteNumber"
        } else {
            "notSameOfDenoteNumber"
        };
        Ok(format!(
            "(Litex.NativeBridge.{law} {} {} {} {} {} {} (by norm_num [Complex.ext_iff]))",
            self.compile_object_reference(left, position)?,
            self.compile_object_reference(right, position)?,
            x.0,
            y.0,
            x.1,
            y.1
        ))
    }

    pub(in crate::compile_to_lean) fn compile_closed_complex_membership(
        &self,
        element: &Obj,
        real: &EvalRational,
        imaginary: &EvalRational,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Some((a, b)) = exact_complex_coordinates(element) else {
            return Err(LeanCompileError::unsupported(
                "ClosedMembership/ComplexExpression",
            ));
        };
        if &a != real || &b != imaginary {
            return Err(LeanCompileError::unsupported("ClosedMembership/Value"));
        }
        // The exact coordinate certificate is validated above. Numeric observation
        // replays the original constructor's domain proof, including division WD.
        Ok(self.compile_numeric_observation(element, position)?.2)
    }

    pub(in crate::compile_to_lean) fn compile_complex_polynomial(
        &self,
        goal: &EqualFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        validate_arithmetic_expression(&goal.left)?;
        validate_arithmetic_expression(&goal.right)?;
        if !normalization_nonzero_subjects(&goal.left, &goal.right)?.is_empty() {
            return Err(LeanCompileError::unsupported(
                "ComplexPolynomial/UnrecordedGuards",
            ));
        }
        let x = self.compile_numeric_observation(&goal.left, position)?;
        let y = self.compile_numeric_observation(&goal.right, position)?;
        // The original Complex tag selects polynomial normalization with i²=-1.
        // Coordinate expansion is fixed and performs no theorem search.
        Ok(format!(
            "(Litex.NativeBridge.sameOfDenoteNumber _ _ {} {} {} {} (by litex_normalize_complex))",
            x.0, y.0, x.1, y.1
        ))
    }
}
