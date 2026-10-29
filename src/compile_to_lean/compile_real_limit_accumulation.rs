//! Real-domain accumulation uses a proved witness, with no function hypothesis.
use super::compile_function_limit::{finite_side, infinite_direction};
use super::compile_function_limit_definition::validate_approach_accumulation;
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::BuiltinThmApplication;
use crate::prelude::*;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("RealLimitAccumulation/{stage}"))
}

impl LitexToLeanCompiler {
    pub(super) fn compile_real_limit_accumulation(
        &self,
        builtin: &BuiltinThmApplication,
        checked: &[VerifyFactResult],
        stored: &[StoreFactAndInferResult],
        conclusions_wd: &[FactWellDefinedProof],
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, String, Vec<Fact>), LeanCompileError> {
        use BuiltinTheoremId::*;
        let finite = matches!(
            builtin.theorem,
            FnLimitAtRealAccumulation | FnLimitLeftRealAccumulation | FnLimitRightRealAccumulation
        );
        let count = usize::from(finite);
        if builtin.arguments.len() != count
            || builtin.requirements.len() != count
            || checked.len() != count
            || stored.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("Stages"));
        }
        let approach = match builtin.theorem {
            FnLimitAtRealAccumulation => {
                LimitApproach::AtPoint(builtin.arguments[0].clone().into())
            }
            FnLimitLeftRealAccumulation => {
                LimitApproach::FromLeft(builtin.arguments[0].clone().into())
            }
            FnLimitRightRealAccumulation => {
                LimitApproach::FromRight(builtin.arguments[0].clone().into())
            }
            FnLimitPosInfRealAccumulation => LimitApproach::AtPositiveInfinity,
            FnLimitNegInfRealAccumulation => LimitApproach::AtNegativeInfinity,
            _ => return Err(invalid("Id")),
        };
        let mut definitions = Vec::new();
        if finite {
            let expected = &builtin.requirements[0];
            if !matches!(expected, Fact::AtomicFact(AtomicFact::InFact(f))
                if f.element.ir() == builtin.arguments[0].ir() && f.set == Obj::StandardSet(StandardSet::R))
                || source_subject(&checked[0])? != *expected
            {
                return Err(invalid("RealPoint"));
            }
            self.validate_store(&stored[0].store, expected)?;
            let proof = self.compile_verify(&checked[0], position)?;
            definitions.push(self.emit_internal_fact(expected, &proof, position)?);
            definitions.extend(self.compile_stored_inferences(
                &stored[0],
                expected,
                &(proof.0, format!("h_{}", expected.fact_id().value())),
                &SourcePosition {
                    before: 1,
                    ..*position
                },
            )?);
        }
        let goal = &builtin.conclusions[0];
        if *validate_approach_accumulation(&approach, &[], goal)?
            != Obj::StandardSet(StandardSet::R)
        {
            return Err(invalid("RealDomain"));
        }
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        let wd = &conclusions_wd[0];
        self.compile_fact_wd(wd, goal, &formed)?;
        let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
        let statement = self.compile_formed_fact_proposition(wd, goal, &formed)?;
        let body = if finite {
            let (side, point) = finite_side(&approach)?;
            format!("intro _Host _rep _radius _radius_member\n  obtain ⟨_input, _input_member, _positive, _near⟩ := Litex.realFiniteLimitAccumulation .{side} {} h_{} _radius _radius_member\n  exact ⟨_input, _input_member, _positive, _near⟩",
                self.compile_object_reference(point, &scope)?, builtin.requirements[0].fact_id().value())
        } else {
            let direction = infinite_direction(&approach)?;
            format!("intro _Host _rep _bound _bound_member\n  obtain ⟨_input, _input_member, _beyond⟩ := Litex.realInfiniteLimitAccumulation .{direction} _bound _bound_member\n  exact ⟨_input, _input_member, _beyond⟩")
        };
        Ok((
            definitions,
            format!("(show {statement} from (by\n  {body}\n))"),
            builtin.conclusions.clone(),
        ))
    }
}
