use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{arithmetic_stages, SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

pub(in crate::compile_to_lean) fn hyperbolic_argument(obj: &Obj) -> Option<(&'static str, &Obj)> {
    match obj {
        Obj::HyperbolicOperator(HyperbolicOperator::Sinh(p)) => Some(("Sinh", &p.arg)),
        Obj::HyperbolicOperator(HyperbolicOperator::Cosh(p)) => Some(("Cosh", &p.arg)),
        Obj::HyperbolicOperator(HyperbolicOperator::Tanh(p)) => Some(("Tanh", &p.arg)),
        Obj::HyperbolicOperator(HyperbolicOperator::Coth(p)) => Some(("Coth", &p.arg)),
        Obj::HyperbolicOperator(HyperbolicOperator::Sech(p)) => Some(("Sech", &p.arg)),
        Obj::HyperbolicOperator(HyperbolicOperator::Csch(p)) => Some(("Csch", &p.arg)),
        _ => None,
    }
}

pub(in crate::compile_to_lean) fn hyperbolic_native_operation(
    kind: &str,
) -> Result<&'static str, LeanCompileError> {
    match kind {
        "Sinh" => Ok("Real.sinh"),
        "Cosh" => Ok("Real.cosh"),
        "Tanh" => Ok("Real.tanh"),
        "Coth" => Ok("Litex.nativeCoth"),
        "Sech" => Ok("Litex.nativeSech"),
        "Csch" => Ok("Litex.nativeCsch"),
        _ => Err(LeanCompileError::unsupported("Hyperbolic/Operation")),
    }
}

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_hyperbolic_wd(
        &self,
        argument: &Obj,
        kind: &str,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        hyperbolic_native_operation(kind)?;
        let guarded = matches!(kind, "Coth" | "Csch");
        if children.len() != 1 || requirements.len() != 1 + usize::from(guarded) {
            return Err(LeanCompileError::unsupported("Hyperbolic/WDStages"));
        }
        ensure_object(argument, &children[0])?;
        if membership_subject(&source_subject(&requirements[0])?, argument)? != StandardSet::R {
            return Err(LeanCompileError::unsupported("Hyperbolic/WDCarrier"));
        }
        if guarded
            && !matches!(source_subject(&requirements[1])?, Fact::AtomicFact(AtomicFact::NotEqualFact(f)) if f.left.ir() == argument.ir() && is_exact_zero(&f.right))
        {
            return Err(LeanCompileError::unsupported("Hyperbolic/WDNonzero"));
        }
        let mut args = vec![self.compile_wd(
            &children[0],
            &SourcePosition {
                before: 0,
                ..*position
            },
        )?];
        for (index, requirement) in requirements.iter().enumerate() {
            args.push(self.compile_wd_requirement(
                requirement,
                &SourcePosition {
                    before: index + 1,
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

    pub(in crate::compile_to_lean) fn numeric_hyperbolic_wd(
        &self,
        wd: &ObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String, String, Option<EvalRational>), LeanCompileError> {
        let (kind, _) = hyperbolic_argument(wd.obj())
            .ok_or_else(|| LeanCompileError::unsupported("Hyperbolic/Observation"))?;
        let term = self.compile_wd(wd, position)?;
        let (children, _) = arithmetic_stages(wd)
            .ok_or_else(|| LeanCompileError::unsupported("Hyperbolic/ObservationStages"))?;
        let formed = SourcePosition::new(Some(position), SourceOwner::WD(wd), usize::MAX);
        let child = self.numeric_wd(&children[0], &formed)?;
        let native = hyperbolic_native_operation(kind)?;
        let member = if matches!(kind, "Coth" | "Csch") {
            "_hyp.wd.1"
        } else {
            "_hyp.wd"
        };
        Ok((format!("({native} ({}).re : ℂ)", child.0),
            format!("(let _hyp := {term}; Litex.denote{kind} _hyp ({}).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg {} {member} {}))", child.0, child.0, child.1),
            format!("(let _hyp := {term}; Litex.realToComplex _hyp (Litex.{}InR _hyp))", kind.to_lowercase()),
            EvalRational::from_obj(wd.obj())))
    }
}
