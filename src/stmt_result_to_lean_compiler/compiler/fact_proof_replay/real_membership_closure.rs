//! Real arithmetic membership closure.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Wrap`: the arithmetic-closure Result owns exactly one conjunction
    /// child Result. The child retains the two ordered operand memberships;
    /// no diagnostic label or rebuilt verifier search participates here.
    pub(in super::super) fn construct_lean_real_arithmetic_membership_closure_from_result(
        &mut self,
        target: &Fact,
        rule: RealArithmeticMembershipClosureBuiltinRule,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let (target_element, target_set) = membership_parts(target)?;
        if !matches!(target_set, Obj::StandardSet(StandardSet::R)) {
            return Err("real arithmetic membership Result changed its target carrier".into());
        }
        if let (RealArithmeticMembershipClosureBuiltinRule::Abs, Obj::Abs(operation)) =
            (rule, target_element)
        {
            if !subgoals.is_empty() {
                return Err(
                    "real absolute-value membership retained unexpected child Results".into(),
                );
            }
            return Ok(Some(format!(
                "Litex.Rules.complexAbsInR {}",
                render_numeric_obj(operation.arg.as_ref(), &self.environment_stack)?
            )));
        }
        let (left, right, theorem) = match (rule, target_element) {
            (RealArithmeticMembershipClosureBuiltinRule::Add, Obj::Add(operation)) => (
                operation.left.as_ref(),
                operation.right.as_ref(),
                "complexAddInR",
            ),
            (RealArithmeticMembershipClosureBuiltinRule::Sub, Obj::Sub(operation)) => (
                operation.left.as_ref(),
                operation.right.as_ref(),
                "complexSubInR",
            ),
            (RealArithmeticMembershipClosureBuiltinRule::Mul, Obj::Mul(operation)) => (
                operation.left.as_ref(),
                operation.right.as_ref(),
                "complexMulInR",
            ),
            (RealArithmeticMembershipClosureBuiltinRule::Div, Obj::Div(operation)) => (
                operation.left.as_ref(),
                operation.right.as_ref(),
                "complexDivInR",
            ),
            (RealArithmeticMembershipClosureBuiltinRule::Pow, _) => return Ok(None),
            (RealArithmeticMembershipClosureBuiltinRule::Abs, _) => {
                return Err("real absolute-value membership changed its source operator".into());
            }
            _ => {
                return Err("real arithmetic membership Result changed its source operator".into());
            }
        };
        let [components] = subgoals else {
            return Err(
                "real arithmetic membership Result must retain one conjunction child".into(),
            );
        };
        let components = components
            .factual_success()
            .ok_or_else(|| "real arithmetic membership child is not factual".to_string())?;
        if !components.store.infers.is_empty() || components.store.fact_id.is_some() {
            return Err(
                "real arithmetic membership conjunction child unexpectedly published effects"
                    .into(),
            );
        }
        let retained_components = conjunction_components(&components.fact())?;
        if retained_components.len() != 2 {
            return Err("real arithmetic membership child is not a binary conjunction".into());
        }
        for (retained, expected_operand) in
            retained_components.iter().zip([left, right].into_iter())
        {
            let (retained_element, retained_set) = membership_parts(retained)?;
            if !matches!(retained_set, Obj::StandardSet(StandardSet::R))
                || obj_equality_key(retained_element) != obj_equality_key(expected_operand)
            {
                return Err("real arithmetic membership child changed its ordered operands".into());
            }
        }
        let components_proof = self
            .construct_lean_proof_from_direct_fact_result(components)?
            .ok_or_else(|| {
                "real arithmetic membership conjunction has no direct recursive Result proof adapter"
                    .to_string()
            })?;
        let components_type = render_fact(&components.fact(), &self.environment_stack)?;
        let left_proof =
            render_real_operand_membership(left, "__components.1", &self.environment_stack);
        let right_proof =
            render_real_operand_membership(right, "__components.2", &self.environment_stack);
        Ok(Some(format!(
            "(by\n  have __components : {components_type} := {components_proof}\n  exact Litex.Rules.{theorem} ({left_proof}) ({right_proof}))"
        )))
    }
}
