use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

fn sign_identity_target(object: &Obj, positive: bool) -> bool {
    let one = |o: &Obj| matches!(o, Obj::Literal(Literal::Number(n)) if n.normalized_value == "1");
    if positive {
        return one(object);
    }
    match object {
        Obj::Literal(Literal::Number(n)) => n.normalized_value == "-1",
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(n)) => one(&n.arg),
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(s)) => {
            is_exact_zero(&s.left) && one(&s.right)
        }
        _ => false,
    }
}

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_sign_wd(
        &self,
        argument: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if children.len() != 1 || requirements.len() != 1 {
            return Err(LeanCompileError::unsupported("WD/SignStages"));
        }
        ensure_object(argument, &children[0])?;
        if membership_subject(&source_subject(&requirements[0])?, argument)? != StandardSet::R {
            return Err(LeanCompileError::unsupported("WD/SignRealDomain"));
        }
        let argument = self.compile_wd(
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
        Ok(format!("(Litex.sign {argument} {member})"))
    }

    pub(in crate::compile_to_lean) fn numeric_sign_wd(
        &self,
        wd: &ObjWellDefinedProof,
        children: &[Box<ObjWellDefinedProof>],
        position: &SourcePosition<'_>,
    ) -> Result<(String, String, String, Option<EvalRational>), LeanCompileError> {
        let term = self.compile_wd(wd, position)?;
        let setup = format!(
            "let _sign := {term};\nlet _member : Litex.In _sign Litex.C := Litex.integerToComplex _sign (Litex.signInZ _sign);"
        );
        if let Some(value) = EvalRational::from_obj(wd.obj()) {
            let child = self.numeric_wd(
                &children[0],
                &SourcePosition {
                    before: 0,
                    ..*position
                },
            )?;
            let exact = child
                .3
                .as_ref()
                .ok_or_else(|| LeanCompileError::unsupported("Sign/ClosedArgument"))?;
            let real = exact_rational_literal(exact, "ℝ")?;
            let value_term = exact_rational_literal(&value, "ℂ")?;
            let denotation = format!(
                "({}).trans (congrArg M.number (by norm_num : {} = (({real} : ℝ) : ℂ)))",
                child.1, child.0
            );
            return Ok((
                value_term.clone(),
                format!(
                    "({setup}\n(Litex.signDenoteReal _sign {real} ({denotation})).trans (congrArg M.number (by norm_num [Real.sign] : ((Real.sign {real} : ℝ) : ℂ) = {value_term})))"
                ),
                format!("({setup}\n_member)"),
                Some(value),
            ));
        }
        Ok((
            format!("({setup}\nLitex.NativeBridge.asComplex _sign _member)"),
            format!("({setup}\nLitex.NativeBridge.asComplex_spec _sign _member)"),
            format!("({setup}\n_member)"),
            None,
        ))
    }

    pub(in crate::compile_to_lean) fn compile_sign_identity(
        &self,
        goal: &EqualFact,
        positive: bool,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let matches = |object: &Obj, value: &Obj| {
            matches!(object, Obj::ArithmeticOperator(ArithmeticOperator::Sign(_)))
                && sign_identity_target(value, positive)
        };
        let (object, target, reversed) = if matches(&goal.left, &goal.right) {
            (&goal.left, &goal.right, false)
        } else if matches(&goal.right, &goal.left) {
            (&goal.right, &goal.left, true)
        } else {
            return Err(LeanCompileError::unsupported("Sign/IdentitySubject"));
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Sign(sign)) = object else {
            unreachable!()
        };
        let [requirement] = requirements else {
            return Err(LeanCompileError::unsupported("Sign/IdentityRequirement"));
        };
        let Fact::AtomicFact(subject) = source_subject(requirement)? else {
            return Err(LeanCompileError::unsupported("Sign/StrictOrder"));
        };
        let (low, high, strict) = source_order_oriented(&subject)?;
        let (zero, argument) = if positive { (low, high) } else { (high, low) };
        if !strict || !is_exact_zero(zero) || argument.ir() != sign.arg.ir() {
            return Err(LeanCompileError::unsupported("Sign/StrictOrder"));
        }
        let order = self.compile_verify(requirement, position)?.1;
        let term = self.compile_object_reference(object, position)?;
        let (value, denotation, _, _) = self.compile_numeric_observation(target, position)?;
        let expected = if positive { "1" } else { "(-1)" };
        let law = if positive {
            "signOfPositive"
        } else {
            "signOfNegative"
        };
        let symmetric = if reversed { ".symm" } else { "" };
        Ok(format!(
            "((Litex.{law} {term} {order}).trans (({denotation}).trans (congrArg M.number (by norm_num : {value} = ({expected} : ℂ)))).symm){symmetric}"
        ))
    }
}
