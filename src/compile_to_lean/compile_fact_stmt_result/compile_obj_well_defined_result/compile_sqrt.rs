use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    /// Closed eval retains nonnegativity, while real membership follows from
    /// the exact original child's numeric denotation.
    pub(in crate::compile_to_lean) fn compile_eval_sqrt_wd(
        &self,
        wd: &ObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        if !super::super::super::compile_eval_stmt_result::in_closed_eval(position) {
            return Ok(None);
        }
        let DetailedObjWellDefinedProof::ByDef {
            obj: Obj::ExpLogOperator(ExpLogOperator::Sqrt(sqrt)),
            proof:
                ObjWellDefinedProofByDef::ExpLogOperator(ExpLogOperatorObjWellDefinedProofByDef::Sqrt(
                    proof,
                )),
        } = wd.detailed_ref()
        else {
            return Ok(None);
        };
        if proof.requirement_fact_verified.len() == 2 {
            return Ok(None);
        }
        if proof.child_obj_well_defined.len() != 1 || proof.requirement_fact_verified.len() != 1 {
            return Err(LeanCompileError::unsupported("Eval/SqrtWDStages"));
        }
        let child = &proof.child_obj_well_defined[0];
        ensure_object(&sqrt.arg, child)?;
        let before_child = SourcePosition {
            before: 0,
            ..*position
        };
        let term = self.compile_wd(child, &before_child)?;
        let (value, denote) = self.compile_eval_closed_value(&sqrt.arg, &before_child)?;
        let complex = exact_rational_literal(&value, "ℂ")?;
        let real = exact_rational_literal(&value, "ℝ")?;
        let member = format!("(Litex.NativeBridge.inOfDenoteNumber {term} {complex} Litex.R {denote} (Litex.NativeBridge.numberInROfEq {complex} {real} (by norm_num)))");
        let requirement = &proof.requirement_fact_verified[0];
        if !matches!(source_subject(requirement)?,
            Fact::AtomicFact(AtomicFact::LessEqualFact(ref fact))
                if is_exact_zero(&fact.left) && fact.right.ir() == sqrt.arg.ir())
        {
            return Err(LeanCompileError::unsupported("Eval/SqrtWDNonnegative"));
        }
        let nonnegative = self.compile_wd_requirement(
            requirement,
            &SourcePosition {
                before: 1,
                ..*position
            },
        )?;
        Ok(Some(format!("(Litex.sqrt {term} {member} {nonnegative})")))
    }

    pub(in crate::compile_to_lean) fn compile_sqrt_wd(
        &self,
        argument: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if children.len() != 1 || requirements.len() != 2 {
            return Err(LeanCompileError::new(
                "WD/SqrtStages",
                "Square root needs one original child WD, real membership, then nonnegativity.",
            ));
        }
        ensure_object(argument, &children[0])?;
        let object = self.compile_wd(
            &children[0],
            &SourcePosition {
                before: 0,
                ..*position
            },
        )?;
        if membership_subject(&source_subject(&requirements[0])?, argument)? != StandardSet::R {
            return Err(LeanCompileError::new(
                "WD/SqrtRealDomain",
                "The first requirement must certify this exact argument in R.",
            ));
        }
        let real = self.compile_wd_requirement(
            &requirements[0],
            &SourcePosition {
                before: 1,
                ..*position
            },
        )?;
        if !matches!(source_subject(&requirements[1])?,
            Fact::AtomicFact(AtomicFact::LessEqualFact(ref fact))
                if is_exact_zero(&fact.left) && fact.right.ir() == argument.ir())
        {
            return Err(LeanCompileError::new(
                "WD/SqrtNonnegativeDomain",
                "The second requirement must be zero <= this exact argument.",
            ));
        }
        let nonnegative = self.compile_wd_requirement(
            &requirements[1],
            &SourcePosition {
                before: 2,
                ..*position
            },
        )?;
        Ok(format!("(Litex.sqrt {object} {real} {nonnegative})"))
    }

    pub(in crate::compile_to_lean) fn numeric_sqrt_wd(
        &self,
        wd: &ObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String, String, Option<EvalRational>), LeanCompileError> {
        let term = self.compile_wd(wd, position)?;
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::ExpLogOperator(ExpLogOperatorObjWellDefinedProofByDef::Sqrt(
                    proof,
                )),
            ..
        } = (wd).detailed_ref()
        else {
            return Err(LeanCompileError::unsupported("WD/SqrtObservation"));
        };
        let setup = format!("let _litex_sqrt := {term};\nlet _litex_sqrt_member : Litex.In _litex_sqrt Litex.C := Litex.sqrtInC _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2;");
        // Opaque roots use the membership observation below; do not render an
        // unused observation of their entire argument expression.
        if let Some(value) = EvalRational::from_obj(wd.obj()) {
            let formed = SourcePosition::new(Some(position), SourceOwner::WD(wd), 3);
            let child = self.numeric_wd(&proof.child_obj_well_defined[0], &formed)?;
            let argument = child
                .3
                .as_ref()
                .ok_or_else(|| LeanCompileError::unsupported("WD/SqrtClosedArgument"))?;
            let argument = exact_rational_literal(argument, "ℝ")?;
            let value_term = exact_rational_literal(&value, "ℂ")?;
            let real_value = exact_rational_literal(&value, "ℝ")?;
            let denotation = format!(
                "({}).trans (congrArg M.number (by norm_num : {} = (({argument} : ℝ) : ℂ)))",
                child.1, child.0
            );
            return Ok((
                value_term.clone(),
                format!("({setup}\n(Litex.NativeBridge.denoteSqrt _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2 {argument} ({denotation})).trans (congrArg M.number (by have _sqrt_value : Real.sqrt {argument} = {real_value} := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num); rw [_sqrt_value]; norm_num : ((Real.sqrt {argument} : ℝ) : ℂ) = {value_term})))"),
                format!("({setup}\n_litex_sqrt_member)"),
                Some(value),
            ));
        }
        // Exact rational radicands can retain a native symbolic square root;
        // its denotation follows from the same source WD, without rounding.
        if let Some(argument) = EvalRational::from_obj(proof.child_obj_well_defined[0].obj()) {
            let formed = SourcePosition::new(Some(position), SourceOwner::WD(wd), 3);
            let child = self.numeric_wd(&proof.child_obj_well_defined[0], &formed)?;
            let argument = exact_rational_literal(&argument, "ℝ")?;
            let denotation = format!(
                "({}).trans (congrArg M.number (by norm_num : {} = (({argument} : ℝ) : ℂ)))",
                child.1, child.0
            );
            return Ok((format!("(Real.sqrt {argument} : ℂ)"),
                format!("({setup}\nLitex.NativeBridge.denoteSqrt _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2 {argument} ({denotation}))"),
                format!("({setup}\n_litex_sqrt_member)"),None));
        }
        Ok((
            format!("({setup}\nLitex.NativeBridge.asComplex _litex_sqrt _litex_sqrt_member)"),
            format!("({setup}\nLitex.NativeBridge.asComplex_spec _litex_sqrt _litex_sqrt_member)"),
            format!("({setup}\n_litex_sqrt_member)"),
            None,
        ))
    }
}
