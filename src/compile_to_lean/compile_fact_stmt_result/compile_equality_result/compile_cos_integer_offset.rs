use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_builtin_strategy_result::CosZeroIntegerOffsetStrategySingleStep;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_inverse_trig::{half_pi, pi_obj};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_cos_integer_offset(
        &self,
        goal: &EqualFact,
        proof: &CosZeroIntegerOffsetStrategySingleStep,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let invalid = |part| LeanCompileError::unsupported(&format!("CosIntegerOffset/{part}"));
        let (argument, reversed) = [
            (&goal.left, &goal.right, false),
            (&goal.right, &goal.left, true),
        ]
        .into_iter()
        .find_map(|(cosine, zero, reversed)| match (cosine, zero) {
            (Obj::TrigOperator(TrigOperator::Cos(cosine)), Obj::Literal(Literal::Number(n)))
                if n.normalized_value == "0" =>
            {
                Some((cosine.arg.as_ref(), reversed))
            }
            _ => None,
        })
        .ok_or_else(|| invalid("Conclusion"))?;
        let requirements = &proof.requirement_facts;
        let children = &proof.proof_of_requirement_facts;
        if !matches!(requirements.len(), 1 | 2) || requirements.len() != children.len() {
            return Err(invalid("Requirements"));
        }
        let Fact::AtomicFact(AtomicFact::InFact(member)) = requirements.last().unwrap() else {
            return Err(invalid("IntegerMembership"));
        };
        if !matches!(member.set, Obj::StandardSet(StandardSet::Z)) {
            return Err(invalid("IntegerCarrier"));
        }
        let offset = if requirements.len() == 1 {
            &member.element
        } else {
            let Fact::AtomicFact(AtomicFact::EqualFact(equal)) = &requirements[0] else {
                return Err(invalid("WitnessEquality"));
            };
            if equal.right.ir() != member.element.ir() {
                return Err(invalid("WitnessSubject"));
            }
            &equal.left
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Div(quotient)) = offset else {
            return Err(invalid("Offset"));
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Sub(shift)) = quotient.left.as_ref() else {
            return Err(invalid("Offset"));
        };
        if shift.left.ir() != argument.ir()
            || shift.right.ir() != half_pi().ir()
            || quotient.right.ir() != pi_obj().ir()
        {
            return Err(invalid("OffsetSubject"));
        }
        let mut lines = Vec::new();
        for (index, (requirement, child)) in requirements.iter().zip(children).enumerate() {
            let subject = source_subject(child)?;
            if subject.fact_id() != requirement.fact_id() || subject.ir() != requirement.ir() {
                return Err(invalid("RequirementSubject"));
            }
            let prior = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(children),
                index,
            );
            let compiled = self.compile_verify(child, &prior)?;
            lines.push(format!(
                "have _cos_requirement_{index} : {} := {}",
                compiled.0, compiled.1
            ));
        }
        let completed = SourcePosition::new(
            Some(position),
            SourceOwner::EqualityRequirements(children),
            children.len(),
        );
        let witness = self.compile_object_reference(&member.element, &completed)?;
        let observed = self.compile_numeric_observation(offset, &completed)?;
        let angle = self.compile_numeric_observation(argument, position)?.0;
        let membership = children.len() - 1;
        lines.push(format!("obtain ⟨_cos_integer, _cos_integer_value⟩ := (M.integer_members (Litex.denote {witness})).mp _cos_requirement_{membership}"));
        let integer_value = if children.len() == 1 {
            "_cos_integer_value"
        } else {
            "(_cos_requirement_0.trans _cos_integer_value)"
        };
        lines.push(format!("have _cos_offset_native : {} = (_cos_integer : ℂ) := M.number_injective (({}).symm.trans {integer_value})", observed.0, observed.1));
        lines.push(format!("have _cos_real_offset : (({angle}).re - Real.pi / 2) / Real.pi = (_cos_integer : ℝ) := by\n  have _cos_offset_re := congrArg Complex.re _cos_offset_native\n  simpa only [Complex.div_ofReal_re, Complex.div_ofNat_re, Complex.sub_re, Complex.ofReal_re, Complex.intCast_re] using _cos_offset_re"));
        lines.push(format!("have _cos_zero : Real.cos ({angle}).re = 0 := by\n  apply Real.cos_eq_zero_iff.mpr\n  refine ⟨_cos_integer, ?_⟩\n  have _cos_angle := (div_eq_iff (ne_of_gt Real.pi_pos)).mp _cos_real_offset\n  linarith"));
        let tactic = format!(
            "{}simp only [_cos_zero, Complex.ofReal_zero]",
            if reversed { "symm; " } else { "" }
        );
        lines.push(format!(
            "exact {}",
            self.compile_trig_native_identity(goal, &tactic, position)?
        ));
        Ok(format!(
            "(by\n  {}\n)",
            lines.join("\n").replace('\n', "\n  ")
        ))
    }
}
