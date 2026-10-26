use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{arithmetic_stages, SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

pub(in crate::compile_to_lean) fn trig_argument(obj: &Obj) -> Option<(&'static str, &Obj)> {
    match obj {
        Obj::TrigOperator(TrigOperator::Sin(p)) => Some(("Sin", &p.arg)),
        Obj::TrigOperator(TrigOperator::Cos(p)) => Some(("Cos", &p.arg)),
        Obj::TrigOperator(TrigOperator::Tan(p)) => Some(("Tan", &p.arg)),
        Obj::TrigOperator(TrigOperator::Cot(p)) => Some(("Cot", &p.arg)),
        Obj::TrigOperator(TrigOperator::Sec(p)) => Some(("Sec", &p.arg)),
        Obj::TrigOperator(TrigOperator::Csc(p)) => Some(("Csc", &p.arg)),
        Obj::TrigOperator(TrigOperator::Arcsin(p)) => Some(("Arcsin", &p.arg)),
        Obj::TrigOperator(TrigOperator::Arccos(p)) => Some(("Arccos", &p.arg)),
        Obj::TrigOperator(TrigOperator::Arctan(p)) => Some(("Arctan", &p.arg)),
        Obj::TrigOperator(TrigOperator::Arccot(p)) => Some(("Arccot", &p.arg)),
        _ => None,
    }
}

pub(in crate::compile_to_lean) fn trig_native_operation(
    kind: &str,
) -> Result<&'static str, LeanCompileError> {
    match kind {
        "Sin" => Ok("Real.sin"),
        "Cos" => Ok("Real.cos"),
        "Tan" => Ok("Real.tan"),
        "Cot" => Ok("Litex.nativeCot"),
        "Sec" => Ok("Litex.nativeSec"),
        "Csc" => Ok("Litex.nativeCsc"),
        "Arcsin" => Ok("Real.arcsin"),
        "Arccos" => Ok("Real.arccos"),
        "Arctan" => Ok("Real.arctan"),
        "Arccot" => Ok("Litex.nativeArccot"),
        _ => Err(LeanCompileError::unsupported("Trig/Operation")),
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
        trig_native_operation(kind)?;
        let bounded = matches!(kind, "Arcsin" | "Arccos");
        let guarded = matches!(kind, "Tan" | "Cot" | "Sec" | "Csc");
        let denominator = if matches!(kind, "Tan" | "Sec") {
            "Cos"
        } else {
            "Sin"
        };
        // These are the two exact special branches of the source WD producer.
        let implicit_guard = match (kind, trig_argument(argument)) {
            ("Tan" | "Sec", Some(("Arctan", _))) => Some("cosArctanNonzero"),
            ("Cot" | "Csc", Some(("Arccot", _))) => Some("sinArccotNonzero"),
            _ => None,
        };
        let count = if bounded {
            3
        } else if guarded && implicit_guard.is_none() {
            2
        } else {
            1
        };
        if children.len() != 1 || requirements.len() != count {
            return Err(LeanCompileError::unsupported("Trig/WDStages"));
        }
        ensure_object(argument, &children[0])?;
        if membership_subject(&source_subject(&requirements[0])?, argument)? != StandardSet::R {
            return Err(LeanCompileError::unsupported("Trig/WDCarrier"));
        }
        if bounded {
            for (i, bound) in [(1, -1), (2, 1)] {
                let Fact::AtomicFact(AtomicFact::LessEqualFact(f)) =
                    source_subject(&requirements[i])?
                else {
                    return Err(LeanCompileError::unsupported("Trig/WDBounds"));
                };
                let (endpoint, subject) = if i == 1 {
                    (&f.left, &f.right)
                } else {
                    (&f.right, &f.left)
                };
                if subject.ir() != argument.ir()
                    || EvalRational::from_obj(endpoint) != EvalRational::new(bound, 1)
                {
                    return Err(LeanCompileError::unsupported("Trig/WDBounds"));
                }
            }
        }
        if guarded && implicit_guard.is_none() {
            let Fact::AtomicFact(AtomicFact::NotEqualFact(f)) = source_subject(&requirements[1])?
            else {
                return Err(LeanCompileError::unsupported("Trig/WDNonzero"));
            };
            if !matches!(trig_argument(&f.left), Some((op, arg)) if op == denominator && arg.ir() == argument.ir())
                || !is_exact_zero(&f.right)
            {
                return Err(LeanCompileError::unsupported("Trig/WDNonzero"));
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
            let at = SourcePosition {
                before: i + 1,
                ..*position
            };
            let proof = self.compile_wd_requirement(requirement, &at)?;
            if bounded && i == 1 {
                let Fact::AtomicFact(AtomicFact::LessEqualFact(f)) = source_subject(requirement)?
                else {
                    return Err(LeanCompileError::unsupported("Trig/WDBounds"));
                };
                // Source IR identifies literal -1 with negation of 1, but their
                // host representations differ. Transport the original checked
                // lower-bound proof to the constructor's fixed numeric endpoint.
                // The endpoint's constructor belongs to this original fact's WD.
                let formed =
                    SourcePosition::new(Some(&at), SourceOwner::Verify(requirement), usize::MAX);
                let endpoint = self.compile_object_reference(&f.left, &formed)?;
                let numeric = self.compile_numeric_observation(&f.left, &formed)?;
                args.push(format!("(Litex.leOfSame {endpoint} (Litex.number (-1)) {} {} (({}).trans (congrArg M.number (show {} = (-1 : ℂ) from by norm_num))) rfl {proof})", args[0], args[0], numeric.1, numeric.0));
            } else {
                args.push(proof);
            }
        }
        if let Some(law) = implicit_guard {
            // Share the original owned child and derive only the producer's implicit guard.
            let operation = kind.to_lowercase();
            return Ok(format!(
                "(let _inverse := {}; Litex.{operation} _inverse {} (Litex.{law} _inverse))",
                args[0], args[1]
            ));
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
        let native = trig_native_operation(kind)?;
        let value = format!("({native} ({}).re : ℂ)", child.0);
        let member = if matches!(kind, "Sin" | "Cos" | "Arctan" | "Arccot") {
            "_trig.wd"
        } else {
            "_trig.wd.1"
        };
        Ok((value, format!("(let _trig := {term}; Litex.denote{kind} _trig ({}).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg {} {member} {}))", child.0, child.0, child.1),
            format!("(let _trig := {term}; Litex.realToComplex _trig (Litex.{op}InR _trig))"), None))
    }
}
