use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_abs_wd(
        &self,
        argument: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (argument, real) = self.abs_wd_arguments(argument, children, requirements, position)?;
        Ok(format!("(Litex.abs {argument} {real})"))
    }

    fn abs_wd_arguments(
        &self,
        argument: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        if children.len() != 1 || requirements.len() != 1 {
            return Err(LeanCompileError::new(
                "WD/Abs",
                "Real absolute value needs its one original child WD and real-domain proof.",
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
                "WD/AbsDomain",
                "The absolute-value domain must certify this exact argument in R.",
            ));
        }
        let real = self
            .compile_verify(
                &requirements[0],
                &SourcePosition {
                    before: 1,
                    ..*position
                },
            )?
            .1;
        Ok((object, real))
    }

    pub(in crate::compile_to_lean) fn numeric_abs_wd(
        &self,
        argument: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<(String, String, String, Option<EvalRational>), LeanCompileError> {
        let (object, real) = self.abs_wd_arguments(argument, children, requirements, position)?;
        let formed = SourcePosition {
            before: 2,
            ..*position
        };
        let child = self.compile_numeric_observation(argument, &formed)?;
        let (native_real, denotation) = match &child.3 {
            Some(value) => {
                let r = exact_rational_literal(value, "ℝ")?;
                let hr = format!(
                    "({}).trans (congrArg M.number (by norm_num : {} = (({r} : ℝ) : ℂ)))",
                    child.1, child.0
                );
                (r, hr)
            }
            None => (
                format!("(Litex.NativeBridge.asReal {object} {real})"),
                format!("(Litex.NativeBridge.asReal_spec {object} {real})"),
            ),
        };
        let exact = child.3.as_ref().and_then(|value| {
            if value.is_negative() {
                EvalRational::new(0, 1)?.sub(value)
            } else {
                Some(value.clone())
            }
        });
        Ok((
            format!("((|{native_real}| : ℝ) : ℂ)"),
            format!("(Litex.NativeBridge.denoteAbs {object} {real} {native_real} ({denotation}))"),
            format!("(Litex.absInC {object} {real})"),
            exact,
        ))
    }
}
