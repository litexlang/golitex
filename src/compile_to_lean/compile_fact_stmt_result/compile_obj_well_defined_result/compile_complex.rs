use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{arithmetic_stages, SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

pub(in crate::compile_to_lean) fn complex_argument(
    obj: &Obj,
) -> Option<(&'static str, &'static str, &Obj)> {
    match obj {
        Obj::ComplexOperator(ComplexOperator::Conjugate(p)) => Some(("Conjugate", "conj", &p.arg)),
        Obj::ComplexOperator(ComplexOperator::RealPart(p)) => Some(("RealPart", "re", &p.arg)),
        Obj::ComplexOperator(ComplexOperator::ImaginaryPart(p)) => {
            Some(("ImaginaryPart", "img", &p.arg))
        }
        Obj::ComplexOperator(ComplexOperator::ComplexAbs(p)) => {
            Some(("ComplexAbs", "complexAbs", &p.arg))
        }
        _ => None,
    }
}

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_complex_wd(
        &self,
        argument: &Obj,
        operation: &str,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let ([child], [membership]) = (children, requirements) else {
            return Err(LeanCompileError::unsupported("Complex/WDStages"));
        };
        ensure_object(argument, child)?;
        if membership_subject(&source_subject(membership)?, argument)? != StandardSet::C {
            return Err(LeanCompileError::unsupported("Complex/WDCarrier"));
        }
        let arg = self.compile_wd(
            child,
            &SourcePosition {
                before: 0,
                ..*position
            },
        )?;
        let member = self.compile_wd_requirement(
            membership,
            &SourcePosition {
                before: 1,
                ..*position
            },
        )?;
        Ok(format!("(Litex.{operation} {arg} {member})"))
    }

    pub(in crate::compile_to_lean) fn compile_complex_modulus_nonnegative(
        &self,
        goal: &AtomicFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        if strict || !EvalRational::from_obj(low).is_some_and(|v| v.is_zero()) {
            return Err(LeanCompileError::unsupported("Complex/NonnegativeZero"));
        }
        let Some(("ComplexAbs", _, arg)) = complex_argument(high) else {
            return Err(LeanCompileError::unsupported("Complex/NonnegativeSubject"));
        };
        let z = self.compile_numeric_observation(arg, position)?;
        let zero = self.compile_numeric_observation(low, position)?;
        let lo = self.compile_object_reference(low, position)?;
        let hi = self.compile_object_reference(high, position)?;
        Ok(format!("(Litex.NativeBridge.leOfDenoteReal {lo} {hi} 0 ‖({})‖ (({}).trans (congrArg M.number (by norm_num))) (Litex.denoteComplexAbs {hi} {} {}) (norm_nonneg _))",z.0,zero.1,z.0,z.1))
    }

    pub(in crate::compile_to_lean) fn numeric_complex_wd(
        &self,
        wd: &ObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String, String, Option<EvalRational>), LeanCompileError> {
        let (kind, operation, _) = complex_argument(wd.obj())
            .ok_or_else(|| LeanCompileError::unsupported("Complex/Observation"))?;
        let term = self.compile_wd(wd, position)?;
        let (children, _) = arithmetic_stages(wd)
            .ok_or_else(|| LeanCompileError::unsupported("Complex/ObservationStages"))?;
        let formed = SourcePosition::new(Some(position), SourceOwner::WD(wd), usize::MAX);
        let child = self.numeric_wd(&children[0], &formed)?;
        let native = match kind {
            "Conjugate" => format!("(star ({}))", child.0),
            "RealPart" => format!("(({}).re : ℂ)", child.0),
            "ImaginaryPart" => format!("(({}).im : ℂ)", child.0),
            "ComplexAbs" => format!("(‖({})‖ : ℂ)", child.0),
            _ => unreachable!(),
        };
        let denote = format!(
            "(let _complex := {term}; Litex.denote{kind} _complex {} {})",
            child.0, child.1
        );
        let member = format!("(Litex.{operation}InC {term})");
        if let Some(value) = EvalRational::from_obj(wd.obj()) {
            let literal = exact_rational_literal(&value, "ℂ")?;
            let calculation = if kind == "ComplexAbs" {
                let real = exact_rational_literal(&value, "ℝ")?;
                format!("have _norm : ‖({})‖ = {real} := (by rw [Complex.norm_def]; exact (Real.sqrt_eq_iff_eq_sq (Complex.normSq_nonneg _) (by norm_num)).mpr (by norm_num [Complex.normSq])); exact (congrArg (fun r : ℝ => (r : ℂ)) _norm).trans (by norm_num)",child.0)
            } else {
                "norm_num [Complex.div_re, Complex.div_im, Complex.normSq]".to_string()
            };
            let checked = format!(
                "(({denote}).trans (congrArg M.number (by {calculation} : {native} = {literal})))"
            );
            return Ok((literal, checked, member, Some(value)));
        }
        Ok((native, denote, member, None))
    }
}
