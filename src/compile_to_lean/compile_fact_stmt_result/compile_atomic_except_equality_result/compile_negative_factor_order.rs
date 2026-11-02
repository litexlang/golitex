use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{
    less::LessFactSearchProofByBuiltinRule,
    greater::GreaterFactSearchProofByBuiltinRule,
    less_equal::LessEqualFactSearchProofByBuiltinRule,
    greater_equal::GreaterEqualFactSearchProofByBuiltinRule,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    /// Borrow the two original children in producer order and the selected placements.
    pub(in crate::compile_to_lean) fn negative_factor_evidence(
        rule: &AtomicExceptEqualityFactSearchProofByBuiltinRule,
    ) -> Option<(
        SourceOrderKind,
        bool,
        bool,
        &VerifyFactResult,
        &VerifyFactResult,
    )> {
        match rule {
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(LessFactSearchProofByBuiltinRule::MulLeftNegativeReversesStrictLess(p)) =>
                Some((SourceOrderKind::Less, true, true, &p.factor_sign_proof, &p.reversed_order_proof)),
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(LessFactSearchProofByBuiltinRule::MulRightNegativeReversesStrictLess(p)) =>
                Some((SourceOrderKind::Less, false, false, &p.factor_sign_proof, &p.reversed_order_proof)),
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(LessFactSearchProofByBuiltinRule::MulLeftRightNegativeReversesStrictLess(p)) =>
                Some((SourceOrderKind::Less, true, false, &p.factor_sign_proof, &p.reversed_order_proof)),
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(LessFactSearchProofByBuiltinRule::MulRightLeftNegativeReversesStrictLess(p)) =>
                Some((SourceOrderKind::Less, false, true, &p.factor_sign_proof, &p.reversed_order_proof)),
            AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(GreaterFactSearchProofByBuiltinRule::MulLeftNegativeReversesStrictGreater(p)) =>
                Some((SourceOrderKind::Greater, true, true, &p.factor_sign_proof, &p.reversed_order_proof)),
            AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(GreaterFactSearchProofByBuiltinRule::MulRightNegativeReversesStrictGreater(p)) =>
                Some((SourceOrderKind::Greater, false, false, &p.factor_sign_proof, &p.reversed_order_proof)),
            AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(GreaterFactSearchProofByBuiltinRule::MulLeftRightNegativeReversesStrictGreater(p)) =>
                Some((SourceOrderKind::Greater, true, false, &p.factor_sign_proof, &p.reversed_order_proof)),
            AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(GreaterFactSearchProofByBuiltinRule::MulRightLeftNegativeReversesStrictGreater(p)) =>
                Some((SourceOrderKind::Greater, false, true, &p.factor_sign_proof, &p.reversed_order_proof)),
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(LessEqualFactSearchProofByBuiltinRule::MulLeftNonpositiveReversesWeakLessEqual(p)) =>
                Some((SourceOrderKind::LessEqual, true, true, &p.factor_sign_proof, &p.reversed_order_proof)),
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(LessEqualFactSearchProofByBuiltinRule::MulRightNonpositiveReversesWeakLessEqual(p)) =>
                Some((SourceOrderKind::LessEqual, false, false, &p.factor_sign_proof, &p.reversed_order_proof)),
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(LessEqualFactSearchProofByBuiltinRule::MulLeftRightNonpositiveReversesWeakLessEqual(p)) =>
                Some((SourceOrderKind::LessEqual, true, false, &p.factor_sign_proof, &p.reversed_order_proof)),
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(LessEqualFactSearchProofByBuiltinRule::MulRightLeftNonpositiveReversesWeakLessEqual(p)) =>
                Some((SourceOrderKind::LessEqual, false, true, &p.factor_sign_proof, &p.reversed_order_proof)),
            AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(GreaterEqualFactSearchProofByBuiltinRule::MulLeftNonpositiveReversesWeakGreaterEqual(p)) =>
                Some((SourceOrderKind::GreaterEqual, true, true, &p.factor_sign_proof, &p.reversed_order_proof)),
            AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(GreaterEqualFactSearchProofByBuiltinRule::MulRightNonpositiveReversesWeakGreaterEqual(p)) =>
                Some((SourceOrderKind::GreaterEqual, false, false, &p.factor_sign_proof, &p.reversed_order_proof)),
            AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(GreaterEqualFactSearchProofByBuiltinRule::MulLeftRightNonpositiveReversesWeakGreaterEqual(p)) =>
                Some((SourceOrderKind::GreaterEqual, true, false, &p.factor_sign_proof, &p.reversed_order_proof)),
            AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(GreaterEqualFactSearchProofByBuiltinRule::MulRightLeftNonpositiveReversesWeakGreaterEqual(p)) =>
                Some((SourceOrderKind::GreaterEqual, false, true, &p.factor_sign_proof, &p.reversed_order_proof)),
            _ => None,
        }
    }

    pub(in crate::compile_to_lean) fn compile_negative_factor_order(
        &self,
        goal: &AtomicFact,
        rule: &AtomicExceptEqualityFactSearchProofByBuiltinRule,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (kind, mut left_on_left, mut right_on_left, sign, order) =
            Self::negative_factor_evidence(rule)
                .ok_or_else(|| LeanCompileError::unsupported("NegativeFactor/SelectedRule"))?;
        if source_order_parts(goal)?.0 != kind {
            return Err(LeanCompileError::unsupported("NegativeFactor/SourceFamily"));
        }
        let (low, high, strict) = source_order_oriented(goal)?;
        if matches!(
            kind,
            SourceOrderKind::Greater | SourceOrderKind::GreaterEqual
        ) {
            std::mem::swap(&mut left_on_left, &mut right_on_left);
        }
        let (
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(lhs)),
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(rhs)),
        ) = (low, high)
        else {
            return Err(LeanCompileError::unsupported("NegativeFactor/Products"));
        };
        let (factor, left_operand) = if left_on_left {
            (&lhs.left, &lhs.right)
        } else {
            (&lhs.right, &lhs.left)
        };
        let (other_factor, right_operand) = if right_on_left {
            (&rhs.left, &rhs.right)
        } else {
            (&rhs.right, &rhs.left)
        };
        if factor.ir() != other_factor.ir() {
            return Err(LeanCompileError::unsupported("NegativeFactor/CommonFactor"));
        }
        let sign_subject = source_subject(sign)?;
        let order_subject = source_subject(order)?;
        let (Fact::AtomicFact(sign_atomic), Fact::AtomicFact(order_atomic)) =
            (&sign_subject, &order_subject)
        else {
            return Err(LeanCompileError::unsupported("NegativeFactor/ChildFamily"));
        };
        let (sign_low, sign_high, sign_strict) = source_order_oriented(sign_atomic)?;
        let (order_low, order_high, order_strict) = source_order_oriented(order_atomic)?;
        if sign_low.ir() != factor.ir()
            || !is_exact_zero(sign_high)
            || order_low.ir() != right_operand.ir()
            || order_high.ir() != left_operand.ir()
            || (strict && (!sign_strict || !order_strict))
        {
            return Err(LeanCompileError::unsupported(
                "NegativeFactor/ChildSubjects",
            ));
        }
        let sign_position = position.atomic_search_prior(0)?;
        let order_position = position.atomic_search_prior(1)?;
        let complete = position.atomic_search_prior(2)?;
        let mut sign_term = self.compile_verify(sign, &sign_position)?.1;
        let mut order_term = self.compile_verify(order, &order_position)?.1;
        if !strict && sign_strict {
            sign_term = format!(
                "(Litex.ltToLe {} {} {sign_term})",
                self.compile_object_reference(sign_low, &sign_position)?,
                self.compile_object_reference(sign_high, &sign_position)?
            );
        }
        if !strict && order_strict {
            order_term = format!(
                "(Litex.ltToLe {} {} {order_term})",
                self.compile_object_reference(order_low, &order_position)?,
                self.compile_object_reference(order_high, &order_position)?
            );
        }
        let normalize = |name: &str, on_left: bool| {
            if on_left {
                (name.to_string(), format!("(Litex.sameRefl {name})"))
            } else {
                (format!("(Litex.mul {name}.val.right {name}.val.left {name}.wd.2 {name}.wd.1)"),
                 format!("(Litex.sameMulComm {name}.val.right {name}.val.left {name}.wd.2 {name}.wd.1)"))
            }
        };
        let (left, left_same) = normalize("_negative_lhs", left_on_left);
        let (right, right_same) = normalize("_negative_rhs", right_on_left);
        let (transport, law) = if strict {
            ("ltOfSame", "mulStructuralLtNegativeLeft")
        } else {
            ("leOfSame", "mulStructuralLeNonpositiveLeft")
        };
        Ok(format!("(by\n  let _negative_lhs := {}\n  let _negative_rhs := {}\n  let _factor_lhs := {left}\n  let _factor_rhs := {right}\n  exact Litex.{transport} _factor_lhs _negative_lhs _factor_rhs _negative_rhs {left_same} {right_same} (Litex.{law} _factor_lhs _factor_rhs {sign_term} {order_term} (Litex.sameRefl _factor_lhs.val.left))\n)",
            self.compile_object_reference(low, &complete)?,
            self.compile_object_reference(high, &complete)?))
    }
}
