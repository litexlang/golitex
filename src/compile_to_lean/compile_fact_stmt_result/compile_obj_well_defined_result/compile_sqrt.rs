use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
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
}
