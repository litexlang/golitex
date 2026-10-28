use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    /// Closed eval records child WD and checks the exact numeric result;
    /// establish the log constructor's domains from those original children.
    pub(in crate::compile_to_lean) fn compile_eval_log_wd(
        &self,
        wd: &ObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        if !super::super::super::compile_eval_stmt_result::in_closed_eval(position) {
            return Ok(None);
        }
        let DetailedObjWellDefinedProof::ByDef {
            obj: Obj::ExpLogOperator(ExpLogOperator::Log(log)),
            proof:
                ObjWellDefinedProofByDef::ExpLogOperator(ExpLogOperatorObjWellDefinedProofByDef::Log(
                    proof,
                )),
        } = wd.detailed_ref()
        else {
            return Ok(None);
        };
        if proof.requirement_fact_verified.len() == 5 {
            return Ok(None);
        }
        if proof.child_obj_well_defined.len() != 2 || !proof.requirement_fact_verified.is_empty() {
            return Err(LeanCompileError::unsupported("Eval/LogWDStages"));
        }
        let mut terms = Vec::new();
        let mut members = Vec::new();
        let mut positive = Vec::new();
        let mut denotations = Vec::new();
        let mut complex_values = Vec::new();
        for (i, (object, child)) in [&log.base, &log.arg]
            .iter()
            .zip(&proof.child_obj_well_defined)
            .enumerate()
        {
            ensure_object(object, child)?;
            let prior = SourcePosition {
                before: i,
                ..*position
            };
            let term = self.compile_wd(child, &prior)?;
            let (value, denote) = self.compile_eval_closed_value(object, &prior)?;
            let (numerator, denominator) = value.parts();
            if numerator <= 0 || (i == 0 && numerator == denominator) {
                return Err(LeanCompileError::unsupported("Eval/LogWDDomain"));
            }
            let complex = exact_rational_literal(&value, "ℂ")?;
            let real = exact_rational_literal(&value, "ℝ")?;
            let real_denote = format!("(({denote}).trans (congrArg M.number (by norm_num : {complex} = (({real} : ℝ) : ℂ))))");
            members.push(format!("(Litex.NativeBridge.inOfDenoteNumber {term} {complex} Litex.R {denote} (Litex.NativeBridge.numberInROfEq {complex} {real} (by norm_num)))"));
            positive.push(format!("(Litex.NativeBridge.ltOfDenoteReal (Litex.number 0) {term} 0 {real} rfl {real_denote} (by norm_num))"));
            denotations.push(denote);
            complex_values.push(complex);
            terms.push(term);
        }
        let nonunit = format!("(Litex.NativeBridge.notSameOfDenoteNumber {} (Litex.number 1) {} 1 {} rfl (by norm_num))", terms[0], complex_values[0], denotations[0]);
        Ok(Some(format!(
            "(Litex.log {} {} {} {} {} {} {nonunit})",
            terms[0], terms[1], members[0], members[1], positive[0], positive[1]
        )))
    }

    pub(in crate::compile_to_lean) fn compile_exp_ln_wd(
        &self,
        argument: &Obj,
        logarithm: bool,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let [child] = children else {
            return Err(LeanCompileError::unsupported("ExpLn/WDStages"));
        };
        let [membership] = requirements else {
            return Err(LeanCompileError::unsupported("ExpLn/WDStages"));
        };
        ensure_object(argument, child)?;
        let target = if logarithm {
            StandardSet::RPos
        } else {
            StandardSet::R
        };
        if membership_subject(&source_subject(membership)?, argument)? != target {
            return Err(LeanCompileError::unsupported("ExpLn/WDCarrier"));
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
        let operation = if logarithm { "ln" } else { "exp" };
        Ok(format!("(Litex.{operation} {arg} {member})"))
    }

    pub(in crate::compile_to_lean) fn compile_log_wd(
        &self,
        source: &Log,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if children.len() != 2 || requirements.len() != 5 {
            return Err(LeanCompileError::unsupported("Log/WDStages"));
        }
        let mut args = Vec::new();
        for (i, object) in [&source.base, &source.arg].iter().enumerate() {
            ensure_object(object, &children[i])?;
            if membership_subject(&source_subject(&requirements[i])?, object)? != StandardSet::R {
                return Err(LeanCompileError::unsupported("Log/WDCarrier"));
            }
            if !matches!(source_subject(&requirements[i + 2])?,
                Fact::AtomicFact(AtomicFact::GreaterFact(f)) if f.left.ir() == object.ir() && is_exact_zero(&f.right))
            {
                return Err(LeanCompileError::unsupported("Log/WDPositive"));
            }
            args.push(self.compile_wd(
                &children[i],
                &SourcePosition {
                    before: i,
                    ..*position
                },
            )?);
        }
        if !matches!(source_subject(&requirements[4])?,
            Fact::AtomicFact(AtomicFact::NotEqualFact(f)) if f.left.ir() == source.base.ir() && matches!(&f.right, Obj::Literal(Literal::Number(n)) if n.normalized_value == "1"))
        {
            return Err(LeanCompileError::unsupported("Log/WDBaseNonunit"));
        }
        for (i, proof) in requirements.iter().enumerate() {
            args.push(self.compile_wd_requirement(
                proof,
                &SourcePosition {
                    before: i + 2,
                    ..*position
                },
            )?);
        }
        Ok(format!("(Litex.log {})", args.join(" ")))
    }

    pub(in crate::compile_to_lean) fn numeric_exp_log_wd(
        &self,
        wd: &ObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String, String, Option<EvalRational>), LeanCompileError> {
        let law = match wd.obj() {
            Obj::ExpLogOperator(ExpLogOperator::Exp(_)) => "expInR",
            Obj::ExpLogOperator(ExpLogOperator::Ln(_)) => "lnInR",
            Obj::ExpLogOperator(ExpLogOperator::Log(_)) => "logInR",
            _ => return Err(LeanCompileError::unsupported("ExpLog/Observation")),
        };
        let term = self.compile_wd(wd, position)?;
        let setup = format!("let _exp_log := {term};\nlet _member := Litex.realToComplex _exp_log (Litex.{law} _exp_log);\n");
        if let Some(value) = EvalRational::from_obj(wd.obj()) {
            let DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::ExpLogOperator(p),
                ..
            } = (wd).detailed_ref()
            else {
                unreachable!()
            };
            let (children, denotation) = match p {
                ExpLogOperatorObjWellDefinedProofByDef::Exp(p) => {
                    (&p.child_obj_well_defined, "denoteExp")
                }
                ExpLogOperatorObjWellDefinedProofByDef::Ln(p) => {
                    (&p.child_obj_well_defined, "denoteLn")
                }
                ExpLogOperatorObjWellDefinedProofByDef::Log(p) => {
                    (&p.child_obj_well_defined, "denoteLog")
                }
                _ => unreachable!(),
            };
            let formed = SourcePosition::new(Some(position), SourceOwner::WD(wd), usize::MAX);
            let mut values = Vec::new();
            let mut proofs = Vec::new();
            for (i, child) in children.iter().enumerate() {
                let observed = self.numeric_wd(child, &formed)?;
                let rational = observed
                    .3
                    .ok_or_else(|| LeanCompileError::unsupported("ExpLog/ClosedArgument"))?;
                let real = exact_rational_literal(&rational, "ℝ")?;
                let field = if children.len() == 2 && i == 0 {
                    "base"
                } else {
                    "arg"
                };
                proofs.push(format!("(by have _child : Litex.denote _exp_log.val.{field} = M.number {} := {}; have _cast : {} = (({real} : ℝ) : ℂ) := (by norm_num); exact _child.trans (congrArg M.number _cast))", observed.0, observed.1, observed.0));
                values.push(real);
            }
            let numeric = exact_rational_literal(&value, "ℂ")?;
            let real_numeric = exact_rational_literal(&value, "ℝ")?;
            let calculation = if children.len() == 2 {
                let (p, q) = value.parts();
                format!("have _value : Real.log {} / Real.log {} = {real_numeric} := (by convert (Litex.rationalLogValue {} {} ({p} : ℤ) ({q} : ℕ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) using 1; norm_num); rw [_value]; norm_num", values[1], values[0], values[0], values[1])
            } else {
                "norm_num [Real.exp_zero, Real.log_one]".to_string()
            };
            let native = match p {
                ExpLogOperatorObjWellDefinedProofByDef::Exp(_) => {
                    format!("(Real.exp {} : ℂ)", values[0])
                }
                ExpLogOperatorObjWellDefinedProofByDef::Ln(_) => {
                    format!("(Real.log {} : ℂ)", values[0])
                }
                _ => format!(
                    "((Real.log {} / Real.log {} : ℝ) : ℂ)",
                    values[1], values[0]
                ),
            };
            return Ok((numeric.clone(), format!("({setup}(Litex.{denotation} _exp_log {} {}).trans (congrArg M.number (by {calculation} : {native} = {numeric})))", values.join(" "), proofs.join(" ")), format!("({setup}_member)"), Some(value)));
        }
        Ok((
            format!("({setup}Litex.NativeBridge.asComplex _exp_log _member)"),
            format!("({setup}Litex.NativeBridge.asComplex_spec _exp_log _member)"),
            format!("({setup}_member)"),
            None,
        ))
    }
}
