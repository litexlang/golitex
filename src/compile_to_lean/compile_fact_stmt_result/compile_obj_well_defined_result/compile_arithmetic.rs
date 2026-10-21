use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn binary_wd_arguments(
        &self,
        left: &Obj,
        right: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        operation: BinaryArithmetic,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let division = matches!(operation, BinaryArithmetic::Div);
        if children.len() != 2 || requirements.len() != if division { 3 } else { 2 } {
            return Err(LeanCompileError::new(
                "WD/Arithmetic",
                "Arithmetic evidence has the wrong stage arity.",
            ));
        }
        ensure_object(left, &children[0])?;
        ensure_object(right, &children[1])?;
        let a = self.compile_wd(
            &children[0],
            &SourcePosition {
                before: 0,
                ..*position
            },
        )?;
        let b = self.compile_wd(
            &children[1],
            &SourcePosition {
                before: 1,
                ..*position
            },
        )?;
        let mut proofs = Vec::new();
        for (index, requirement) in requirements.iter().enumerate() {
            proofs.push(self.compile_wd_requirement(
                requirement,
                &SourcePosition {
                    before: children.len() + index,
                    ..*position
                },
            )?);
        }
        let offset = usize::from(division);
        ensure_complex_member(&source_subject(&requirements[offset])?, left)?;
        ensure_complex_member(&source_subject(&requirements[offset + 1])?, right)?;
        let guard = if division {
            ensure_nonzero_subject(&source_subject(&requirements[0])?, right)?;
            format!(" {}", proofs[0])
        } else {
            String::new()
        };
        Ok(format!(
            "{a} {b} {} {}{guard}",
            proofs[offset],
            proofs[offset + 1]
        ))
    }

    pub(in crate::compile_to_lean) fn compile_binary_wd(
        &self,
        left: &Obj,
        right: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        operation: BinaryArithmetic,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let arguments =
            self.binary_wd_arguments(left, right, children, requirements, operation, position)?;
        let (name, _, _) = operation.names();
        Ok(format!("(Litex.{name} {arguments})"))
    }

    pub(in crate::compile_to_lean) fn numeric_binary_wd(
        &self,
        left: &Obj,
        right: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        operation: BinaryArithmetic,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String, String, Option<EvalRational>), LeanCompileError> {
        let arguments =
            self.binary_wd_arguments(left, right, children, requirements, operation, position)?;
        let formed = SourcePosition {
            before: children.len() + requirements.len(),
            ..*position
        };
        // The ordered child certificates are already in this result. Do not
        // walk the enclosing proof tree again to rediscover their formation.
        let x = self.numeric_wd(&children[0], &formed)?;
        let y = self.numeric_wd(&children[1], &formed)?;
        let (name, symbol, bridge) = operation.names();
        let closed = match (&x.3, &y.3) {
            (Some(x), Some(y)) => match operation {
                BinaryArithmetic::Add => x.add(y),
                BinaryArithmetic::Sub => x.sub(y),
                BinaryArithmetic::Mul => x.mul(y),
                BinaryArithmetic::Div => x.div(y),
            },
            _ => None,
        };
        // The child certificates determine their scalar arguments. Reprinting
        // x.0/y.0 here duplicates the observation tree at every arithmetic node.
        Ok((
            format!("({} {symbol} {})", x.0, y.0),
            format!(
                "(Litex.NativeBridge.denote{bridge} {arguments} _ _ {} {})",
                x.1, y.1
            ),
            format!("(Litex.{name}InC {arguments})"),
            closed,
        ))
    }

    pub(in crate::compile_to_lean) fn neg_wd_arguments(
        &self,
        argument: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if children.len() != 1 || requirements.len() != 1 {
            return Err(LeanCompileError::new(
                "WD/Neg",
                "Negation evidence has the wrong stage arity.",
            ));
        }
        ensure_object(argument, &children[0])?;
        let a = self.compile_wd(
            &children[0],
            &SourcePosition {
                before: 0,
                ..*position
            },
        )?;
        let member = self.compile_wd_requirement(
            &requirements[0],
            &SourcePosition {
                before: 1,
                ..*position
            },
        )?;
        ensure_complex_member(&source_subject(&requirements[0])?, argument)?;
        Ok(format!("{a} {member}"))
    }

    pub(in crate::compile_to_lean) fn compile_neg_wd(
        &self,
        argument: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        Ok(format!(
            "(Litex.neg {})",
            self.neg_wd_arguments(argument, children, requirements, position)?
        ))
    }

    pub(in crate::compile_to_lean) fn numeric_neg_wd(
        &self,
        argument: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<(String, String, String, Option<EvalRational>), LeanCompileError> {
        let arguments = self.neg_wd_arguments(argument, children, requirements, position)?;
        let formed = SourcePosition {
            before: 2,
            ..*position
        };
        let x = self.numeric_wd(&children[0], &formed)?;
        Ok((
            format!("(- {})", x.0),
            format!("(Litex.NativeBridge.denoteNeg {arguments} _ {})", x.1),
            format!("(Litex.negInC {arguments})"),
            x.3.as_ref()
                .and_then(|value| EvalRational::new(0, 1)?.sub(value)),
        ))
    }

    pub(in crate::compile_to_lean) fn pow_wd_arguments(
        &self,
        base: &Obj,
        exponent: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<(&'static str, &'static str, String, String, Option<i128>), LeanCompileError> {
        if children.len() != 2 || !(requirements.len() == 2 || requirements.len() == 3) {
            return Err(LeanCompileError::new(
                "WD/Pow",
                "Integer-power evidence has the wrong stage arity.",
            ));
        }
        ensure_object(base, &children[0])?;
        ensure_object(exponent, &children[1])?;
        let a = self.compile_wd(
            &children[0],
            &SourcePosition {
                before: 0,
                ..*position
            },
        )?;
        let e = self.compile_wd(
            &children[1],
            &SourcePosition {
                before: 1,
                ..*position
            },
        )?;
        let integer = closed_integer(exponent);
        let mut proved = Vec::new();
        for (index, requirement) in requirements.iter().enumerate() {
            proved.push(self.compile_wd_requirement(
                requirement,
                &SourcePosition {
                    before: 2 + index,
                    ..*position
                },
            )?);
        }
        let formed = SourcePosition {
            before: 2 + requirements.len(),
            ..*position
        };
        let base_set = membership_subject(&source_subject(&requirements[0])?, base)?;
        let exponent_set = membership_subject(&source_subject(&requirements[1])?, exponent)?;
        let natural_value = || match integer {
            Some(n) if n >= 0 => Ok(format!("({n} : ℕ)")),
            Some(_) => Err(LeanCompileError::new(
                "WD/Pow/NaturalValue",
                "A recorded natural exponent cannot be a negative literal.",
            )),
            None => Ok(format!("(Litex.NativeBridge.asNat {e} {})", proved[1])),
        };
        let (name, bridge, exponent_value) = match (base_set, exponent_set, requirements.len()) {
            (StandardSet::R, StandardSet::N, 2) => ("powNatReal", "PowNatReal", natural_value()?),
            (StandardSet::C, StandardSet::N, 2) => ("powNat", "PowNat", natural_value()?),
            (StandardSet::C, StandardSet::Z, 3) => {
                ensure_nonzero_subject(&source_subject(&requirements[2])?, base)?;
                let n = integer.ok_or_else(|| {
                    LeanCompileError::unsupported("WD/Pow/NonClosedIntegerExponent")
                })?;
                ("powInt", "PowInt", format!("({n} : ℤ)"))
            }
            _ => return Err(LeanCompileError::unsupported("WD/Pow/Domain")),
        };
        let he_value = if integer.is_none() {
            format!("(Litex.NativeBridge.asNat_spec {e} {})", proved[1])
        } else {
            let exp_native = self.numeric_wd(&children[1], &formed)?;
            let integer_complex = format!("({exponent_value} : ℂ)");
            format!("(Litex.NativeBridge.sameOfDenoteNumber {e} (Litex.number (M := M) {integer_complex}) {} {integer_complex} {} (Litex.NativeBridge.denoteNumber (M := M) {integer_complex}) (by norm_num))", exp_native.0, exp_native.1)
        };
        let guard = if requirements.len() == 3 {
            format!(" {}", proved[2])
        } else {
            String::new()
        };
        let arguments = format!(
            "{a} {e} {exponent_value} {} {}{guard} {he_value}",
            proved[0], proved[1]
        );
        Ok((name, bridge, exponent_value, arguments, integer))
    }

    pub(in crate::compile_to_lean) fn compile_pow_wd(
        &self,
        base: &Obj,
        exponent: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (name, _, _, arguments, _) =
            self.pow_wd_arguments(base, exponent, children, requirements, position)?;
        Ok(format!("(Litex.{name} {arguments})"))
    }

    pub(in crate::compile_to_lean) fn numeric_pow_wd(
        &self,
        base: &Obj,
        exponent: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<(String, String, String, Option<EvalRational>), LeanCompileError> {
        let (name, bridge, exponent_value, arguments, integer) =
            self.pow_wd_arguments(base, exponent, children, requirements, position)?;
        let formed = SourcePosition {
            before: 2 + requirements.len(),
            ..*position
        };
        let x = self.numeric_wd(&children[0], &formed)?;
        Ok((
            format!("({} ^ {exponent_value})", x.0),
            format!("(Litex.NativeBridge.denote{bridge} {arguments} _ {})", x.1),
            format!("(Litex.{name}InC {arguments})"),
            x.3.as_ref()
                .zip(integer)
                .and_then(|(value, integer)| value.pow_integer(integer)),
        ))
    }
}
