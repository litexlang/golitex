use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_selected_zero_bound_strategy(
        &self,
        goal: &AtomicFact,
        strategy: &AtomicExceptEqualityFactSearchProofByBuiltinStrategy,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (name, strict, child_strict, requirements, results) = match strategy {
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NonnegativeSumIsNonnegative(
                p,
            ) => (
                "addNonnegative",
                false,
                [false, false],
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
            ),
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::StrictAdditiveRightStrict(p) => (
                "addPositiveRight",
                true,
                [false, true],
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
            ),
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ProductNonnegativeBothNonneg(
                p,
            ) => (
                "mulNonnegative",
                false,
                [false, false],
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
            ),
            _ => return Err(LeanCompileError::unsupported("ZeroBound/Strategy")),
        };
        let (zero, expression, goal_strict) = source_order_oriented(goal)?;
        let operands = match expression {
            Obj::ArithmeticOperator(ArithmeticOperator::Add(p)) if name.starts_with("add") => {
                [p.left.as_ref(), p.right.as_ref()]
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) if name.starts_with("mul") => {
                [p.left.as_ref(), p.right.as_ref()]
            }
            _ => {
                return Err(LeanCompileError::new(
                    "ZeroBound/Constructor",
                    "The selected strategy differs from its original source operation.",
                ))
            }
        };
        if !is_exact_zero(zero)
            || goal_strict != strict
            || requirements.len() != 2
            || results.len() != 2
        {
            return Err(LeanCompileError::new("ZeroBound/Requirements", "The selected strategy needs the exact source zero bound and both original ordered child results."));
        }
        let mut children = Vec::new();
        for (((requirement, result), operand), strict) in requirements
            .iter()
            .zip(results)
            .zip(operands)
            .zip(child_strict)
        {
            let Fact::AtomicFact(atomic) = requirement else {
                return Err(LeanCompileError::new(
                    "ZeroBound/ChildFamily",
                    "The original bound requirement must be atomic.",
                ));
            };
            let (zero, value, actual_strict) = source_order_oriented(atomic)?;
            if !is_exact_zero(zero)
                || value.ir() != operand.ir()
                || actual_strict != strict
                || source_subject(result)? != *requirement
            {
                return Err(LeanCompileError::new("ZeroBound/ChildSubject", "An original ordered child changed its operand, source identity or comparison strength."));
            }
            children.push(self.compile_verify(result, position)?.1);
        }
        Ok(format!("(by\n  let _litex_zero_bound := {}\n  exact Litex.{name} _litex_zero_bound.val.left _litex_zero_bound.val.right _litex_zero_bound.wd.1 _litex_zero_bound.wd.2 {} {}\n)", self.compile_object_reference(expression, position)?, children[0], children[1]))
    }

    pub(in crate::compile_to_lean) fn compile_selected_mul_monotone(
        &self,
        goal: &AtomicFact,
        factor: &VerifyFactResult,
        order: &VerifyFactResult,
        common_left: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        let (
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(lhs)),
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(rhs)),
        ) = (low, high)
        else {
            return Err(LeanCompileError::new(
                "MulMonotone/Constructor",
                "The selected monotonicity needs both original product constructors.",
            ));
        };
        let (left_factor, right_factor, left_operand, right_operand) = if common_left {
            (&lhs.left, &rhs.left, &lhs.right, &rhs.right)
        } else {
            (&lhs.right, &rhs.right, &lhs.left, &rhs.left)
        };
        if strict || left_factor.ir() != right_factor.ir() {
            return Err(LeanCompileError::new(
                "MulMonotone/Factor",
                "The original weak products must retain their common factor on the selected side.",
            ));
        }
        ensure_recorded_order(factor, None, left_factor, false)?;
        ensure_recorded_order(order, Some(left_operand), right_operand, false)?;
        let law = if common_left {
            "mulStructuralLeLeft"
        } else {
            "mulStructuralLeRight"
        };
        let side = if common_left { "left" } else { "right" };
        Ok(format!("(by\n  let _litex_monotone_left := {}\n  let _litex_monotone_right := {}\n  exact Litex.{law} _litex_monotone_left _litex_monotone_right {} {} (Litex.sameRefl _litex_monotone_left.val.{side})\n)", self.compile_object_reference(low, position)?, self.compile_object_reference(high, position)?, self.compile_verify(factor, position)?.1, self.compile_verify(order, position)?.1))
    }

    pub(in crate::compile_to_lean) fn compile_selected_div_monotone(
        &self,
        goal: &AtomicFact,
        positive: &VerifyFactResult,
        order: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        if strict {
            return Err(LeanCompileError::new(
                "DivMonotone/Divisor",
                "The selected quotient monotonicity must retain its original weak comparison.",
            ));
        }
        if is_exact_zero(low) {
            if let Obj::ArithmeticOperator(ArithmeticOperator::Div(quotient)) = high {
                ensure_recorded_order(positive, None, &quotient.right, true)?;
                ensure_recorded_order(order, None, &quotient.left, false)?;
                return Ok(format!(
                    "(Litex.divStructuralNonnegative {} {} {})",
                    self.compile_object_reference(high, position)?,
                    self.compile_verify(positive, position)?.1,
                    self.compile_verify(order, position)?.1
                ));
            }
        }
        if is_exact_zero(high) {
            if let Obj::ArithmeticOperator(ArithmeticOperator::Div(quotient)) = low {
                ensure_recorded_order(positive, None, &quotient.right, true)?;
                ensure_recorded_order(order, Some(&quotient.left), high, false)?;
                return Ok(format!(
                    "(Litex.divStructuralNonpositive {} {} {})",
                    self.compile_object_reference(low, position)?,
                    self.compile_verify(positive, position)?.1,
                    self.compile_verify(order, position)?.1
                ));
            }
        }
        let (
            Obj::ArithmeticOperator(ArithmeticOperator::Div(lhs)),
            Obj::ArithmeticOperator(ArithmeticOperator::Div(rhs)),
        ) = (low, high)
        else {
            return Err(LeanCompileError::new(
                "DivMonotone/Constructor",
                "The selected monotonicity needs its original quotient constructors or exact zero endpoint.",
            ));
        };
        if lhs.right.ir() != rhs.right.ir() {
            return Err(LeanCompileError::new(
                "DivMonotone/Divisor",
                "The original weak quotients must retain their exact common divisor.",
            ));
        }
        ensure_recorded_order(positive, None, &lhs.right, true)?;
        ensure_recorded_order(order, Some(&lhs.left), &rhs.left, false)?;
        Ok(format!("(by\n  let _litex_monotone_left := {}\n  let _litex_monotone_right := {}\n  exact Litex.divStructuralLe _litex_monotone_left _litex_monotone_right {} {} (Litex.sameRefl _litex_monotone_left.val.right)\n)", self.compile_object_reference(low, position)?, self.compile_object_reference(high, position)?, self.compile_verify(positive, position)?.1, self.compile_verify(order, position)?.1))
    }

    pub(in crate::compile_to_lean) fn compile_div_monotone_strategy(
        &self,
        goal: &AtomicFact,
        requirements: &[Fact],
        results: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if requirements.len() != 2 || results.len() != 2 {
            return Err(LeanCompileError::new(
                "DivMonotone/Requirements",
                "The strategy must retain its two actual ordered requirement identities.",
            ));
        }
        for (subject, result) in requirements.iter().zip(results) {
            if source_subject(result)? != *subject {
                return Err(LeanCompileError::new("DivMonotone/RequirementCapture", "An actual divisor-strategy child differs from its ordered original requirement."));
            }
        }
        self.compile_selected_div_monotone(goal, &results[0], &results[1], position)
    }

    pub(in crate::compile_to_lean) fn compile_order_from_difference(
        &self,
        goal: &AtomicFact,
        premise: &AtomicExceptEqualityFactKnownProof,
        strict_rule: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        let (zero, difference, premise_strict) = source_order_oriented(&premise.fact)?;
        let Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)) = difference else {
            return Err(LeanCompileError::new(
                "OrderDifference/Constructor",
                "The selected original citation must compare its difference with zero.",
            ));
        };
        if !is_exact_zero(zero)
            || strict != strict_rule
            || premise_strict != strict_rule
            || sub.left.ir() != high.ir()
            || sub.right.ir() != low.ir()
        {
            return Err(LeanCompileError::new("OrderDifference/Subject", "The original difference citation changes the ordered source operands or comparison strength."));
        }
        let child = self.compile_order_known_premise(premise, position)?.1;
        let law = if strict {
            "subPositiveToLt"
        } else {
            "subNonnegativeToLe"
        };
        Ok(format!(
            "(Litex.{law} {} {} {} {child})",
            self.compile_object_reference(difference, position)?,
            self.compile_real_membership_certificate(high, position)?,
            self.compile_real_membership_certificate(low, position)?
        ))
    }

    pub(in crate::compile_to_lean) fn compile_predecessor_nonnegative_known(
        &self,
        goal: &AtomicFact,
        premise: &AtomicExceptEqualityFactKnownProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (zero, expression, strict) = source_order_oriented(goal)?;
        let Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)) = expression else {
            return Err(LeanCompileError::new(
                "PredecessorNonnegative/Constructor",
                "The original predecessor must retain its subtraction constructor.",
            ));
        };
        let (low, high, premise_strict) = source_order_oriented(&premise.fact)?;
        if strict
            || !is_exact_zero(zero)
            || closed_integer(&sub.right) != Some(1)
            || premise_strict
            || low.ir() != sub.right.ir()
            || high.ir() != sub.left.ir()
        {
            return Err(LeanCompileError::new(
                "PredecessorNonnegative/Subject",
                "The original weak citation must order this exact one and minuend.",
            ));
        }
        Ok(format!(
            "(Litex.subNonnegative {} {})",
            self.compile_object_reference(expression, position)?,
            self.compile_order_known_premise(premise, position)?.1
        ))
    }

    pub(in crate::compile_to_lean) fn compile_positive_div_product_bound(
        &self,
        goal: &AtomicFact,
        positive: &VerifyFactResult,
        bound: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        let Obj::ArithmeticOperator(ArithmeticOperator::Div(quotient)) = high else {
            return Err(LeanCompileError::new(
                "PositiveDivProductBound/Quotient",
                "The actual upper endpoint must retain its original quotient.",
            ));
        };
        let bound_subject = source_subject(bound)?;
        let Fact::AtomicFact(atomic) = &bound_subject else {
            return Err(LeanCompileError::new(
                "PositiveDivProductBound/BoundFamily",
                "The original product bound must be atomic.",
            ));
        };
        let (product_object, upper, bound_strict) = source_order_oriented(atomic)?;
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = product_object else {
            return Err(LeanCompileError::new(
                "PositiveDivProductBound/Product",
                "The original bound must retain its ordered product.",
            ));
        };
        if strict
            || bound_strict
            || product.left.ir() != quotient.right.ir()
            || product.right.ir() != low.ir()
            || upper.ir() != quotient.left.ir()
        {
            return Err(LeanCompileError::new("PositiveDivProductBound/BoundSubject", "The original product/divisor/argument endpoints must agree in their selected order."));
        }
        ensure_recorded_order(positive, None, &quotient.right, true)?;
        Ok(format!("(by\n  let _litex_bound_quotient := {}\n  let _litex_bound_product := {}\n  exact Litex.leDivOfProductBound {} _litex_bound_quotient _litex_bound_product {} {} {} (Litex.sameRefl _litex_bound_product.val.left) (Litex.sameRefl _litex_bound_product.val.right)\n)", self.compile_object_reference(high, position)?, self.compile_object_reference(product_object, position)?, self.compile_object_reference(low, position)?, self.compile_real_membership_certificate(low, position)?, self.compile_verify(positive, position)?.1, self.compile_verify(bound, position)?.1))
    }
}

fn ensure_recorded_order(
    result: &VerifyFactResult,
    low: Option<&Obj>,
    high: &Obj,
    strict: bool,
) -> Result<(), LeanCompileError> {
    let subject = source_subject(result)?;
    let Fact::AtomicFact(atomic) = &subject else {
        return Err(LeanCompileError::new(
            "SelectedOrder/ChildFamily",
            "The original selected order child must be atomic.",
        ));
    };
    let (actual_low, actual_high, actual_strict) = source_order_oriented(atomic)?;
    if actual_strict != strict
        || actual_high.ir() != high.ir()
        || low.map_or_else(
            || !is_exact_zero(actual_low),
            |low| actual_low.ir() != low.ir(),
        )
    {
        return Err(LeanCompileError::new(
            "SelectedOrder/ChildSubject",
            "The actual selected child changes its exact endpoints or comparison strength.",
        ));
    }
    Ok(())
}
