use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{arithmetic_stages, SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

pub(in crate::compile_to_lean) fn trig_argument(obj: &Obj) -> Option<(&'static str, &Obj)> {
    match obj {
        Obj::TrigOperator(TrigOperator::Sin(p)) => Some(("Sin", &p.arg)),
        Obj::TrigOperator(TrigOperator::Cos(p)) => Some(("Cos", &p.arg)),
        Obj::TrigOperator(TrigOperator::Tan(p)) => Some(("Tan", &p.arg)),
        _ => None,
    }
}

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_trig_wd(
        &self,
        argument: &Obj,
        kind: &str,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if children.len() != 1 || requirements.len() != if kind == "Tan" { 2 } else { 1 } {
            return Err(LeanCompileError::unsupported("Trig/WDStages"));
        }
        ensure_object(argument, &children[0])?;
        if membership_subject(&source_subject(&requirements[0])?, argument)? != StandardSet::R {
            return Err(LeanCompileError::unsupported("Trig/WDCarrier"));
        }
        if kind == "Tan" {
            let Fact::AtomicFact(AtomicFact::NotEqualFact(f)) = source_subject(&requirements[1])?
            else {
                return Err(LeanCompileError::unsupported("Tan/WDNonzero"));
            };
            if !matches!(trig_argument(&f.left), Some(("Cos", arg)) if arg.ir() == argument.ir())
                || !is_exact_zero(&f.right)
            {
                return Err(LeanCompileError::unsupported("Tan/WDNonzero"));
            }
        }
        let arg = self.compile_wd(
            &children[0],
            &SourcePosition {
                before: 0,
                ..*position
            },
        )?;
        let mut args = vec![arg];
        for (i, requirement) in requirements.iter().enumerate() {
            args.push(self.compile_wd_requirement(
                requirement,
                &SourcePosition {
                    before: i + 1,
                    ..*position
                },
            )?);
        }
        Ok(format!(
            "(Litex.{} {})",
            kind.to_lowercase(),
            args.join(" ")
        ))
    }

    pub(in crate::compile_to_lean) fn numeric_trig_wd(
        &self,
        wd: &ObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String, String, Option<EvalRational>), LeanCompileError> {
        let (kind, _) = trig_argument(wd.obj())
            .ok_or_else(|| LeanCompileError::unsupported("Trig/Observation"))?;
        let term = self.compile_wd(wd, position)?;
        let (children, _) = arithmetic_stages(wd)
            .ok_or_else(|| LeanCompileError::unsupported("Trig/ObservationStages"))?;
        let formed = SourcePosition::new(Some(position), SourceOwner::WD(wd), usize::MAX);
        let child = self.numeric_wd(&children[0], &formed)?;
        let op = kind.to_lowercase();
        let value = format!("(Real.{op} ({}).re : ℂ)", child.0);
        let member = if kind == "Tan" {
            "_trig.wd.1"
        } else {
            "_trig.wd"
        };
        Ok((value, format!("(let _trig := {term}; Litex.denote{kind} _trig ({}).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg {} {member} {}))", child.0, child.0, child.1),
            format!("(let _trig := {term}; Litex.realToComplex _trig (Litex.{op}InR _trig))"), None))
    }
}
