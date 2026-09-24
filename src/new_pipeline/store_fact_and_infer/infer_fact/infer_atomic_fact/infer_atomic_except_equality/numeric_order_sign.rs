use crate::new_pipeline::ast::fact::{
    AtomicFact, Fact, GreaterFact, GreaterEqualFact, LessFact, LessEqualFact,
};
use crate::new_pipeline::ast::obj::{ArithmeticOperator, Literal, Mul, Number, Obj};
use crate::new_pipeline::rational_expression::{compare_number_strings, NumberCompareResult};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::{
    InferNumericOrderSignResult, InferOrderFlipMulMinusOneResult,
};

impl Runtime {
    // When: order atom with exactly one side a resolved numeric literal.
    // Infers: selected sign vs 0 on the other side (Manual Builtin Inference).
    // Example: `a >= 1` with `1` resolved ⇒ store `0 < a`.
    pub(super) fn infer_less_order_sign(
        &mut self,
        fact: &LessFact,
    ) -> RuntimeResult<Option<InferNumericOrderSignResult>> {
        self.infer_order_sign_core(
            &fact.left,
            &fact.right,
            OrderKind::Less,
            fact.line_file.clone(),
        )
    }

    pub(super) fn infer_greater_order_sign(
        &mut self,
        fact: &GreaterFact,
    ) -> RuntimeResult<Option<InferNumericOrderSignResult>> {
        self.infer_order_sign_core(
            &fact.left,
            &fact.right,
            OrderKind::Greater,
            fact.line_file.clone(),
        )
    }

    pub(super) fn infer_less_equal_order_sign(
        &mut self,
        fact: &LessEqualFact,
    ) -> RuntimeResult<Option<InferNumericOrderSignResult>> {
        self.infer_order_sign_core(
            &fact.left,
            &fact.right,
            OrderKind::LessEqual,
            fact.line_file.clone(),
        )
    }

    pub(super) fn infer_greater_equal_order_sign(
        &mut self,
        fact: &GreaterEqualFact,
    ) -> RuntimeResult<Option<InferNumericOrderSignResult>> {
        self.infer_order_sign_core(
            &fact.left,
            &fact.right,
            OrderKind::GreaterEqual,
            fact.line_file.clone(),
        )
    }

    // When: order vs resolved 0 on the right; left is not already (-1)*u.
    // Infers: flip by multiplying left by (-1): x<0/x<=0 → (-1)*x >= 0; x>0 → (-1)*x < 0; x>=0 → (-1)*x <= 0.
    // Example: `a < 0` ⇒ soft-store `(-1)*a >= 0` when WD succeeds.
    pub(super) fn infer_order_flip_mul_minus_one_from_less(
        &mut self,
        fact: &LessFact,
    ) -> RuntimeResult<Option<InferOrderFlipMulMinusOneResult>> {
        self.infer_order_flip_mul_minus_one_core(
            &fact.left,
            &fact.right,
            OrderKind::Less,
            fact.line_file.clone(),
        )
    }

    pub(super) fn infer_order_flip_mul_minus_one_from_greater(
        &mut self,
        fact: &GreaterFact,
    ) -> RuntimeResult<Option<InferOrderFlipMulMinusOneResult>> {
        self.infer_order_flip_mul_minus_one_core(
            &fact.left,
            &fact.right,
            OrderKind::Greater,
            fact.line_file.clone(),
        )
    }

    pub(super) fn infer_order_flip_mul_minus_one_from_less_equal(
        &mut self,
        fact: &LessEqualFact,
    ) -> RuntimeResult<Option<InferOrderFlipMulMinusOneResult>> {
        self.infer_order_flip_mul_minus_one_core(
            &fact.left,
            &fact.right,
            OrderKind::LessEqual,
            fact.line_file.clone(),
        )
    }

    pub(super) fn infer_order_flip_mul_minus_one_from_greater_equal(
        &mut self,
        fact: &GreaterEqualFact,
    ) -> RuntimeResult<Option<InferOrderFlipMulMinusOneResult>> {
        self.infer_order_flip_mul_minus_one_core(
            &fact.left,
            &fact.right,
            OrderKind::GreaterEqual,
            fact.line_file.clone(),
        )
    }

    pub(crate) fn resolve_obj_to_normalized_number(&self, obj: &Obj) -> Option<String> {
        if let Obj::Literal(Literal::Number(n)) = obj {
            return Some(n.normalized_value.clone());
        }
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(entries) = env.facts.known_closed_numeric_equal.get(&obj.ir()) {
                if let Some((rep, _)) = entries.first() {
                    if let Obj::Literal(Literal::Number(n)) = rep {
                        return Some(n.normalized_value.clone());
                    }
                }
            }
        }
        None
    }

    pub(crate) fn obj_is_resolved_zero(&self, obj: &Obj) -> bool {
        self.resolve_obj_to_normalized_number(obj)
            .map(|n| {
                matches!(
                    compare_number_strings(&n, "0"),
                    NumberCompareResult::Equal
                )
            })
            .unwrap_or(false)
    }
}

impl Runtime {
    fn infer_order_sign_core(
        &mut self,
        left: &Obj,
        right: &Obj,
        kind: OrderKind,
        line_file: Option<crate::new_pipeline::ast::line_file::SourceLine>,
    ) -> RuntimeResult<Option<InferNumericOrderSignResult>> {
        let left_num = self.resolve_obj_to_normalized_number(left);
        let right_num = self.resolve_obj_to_normalized_number(right);
        let target = match (left_num.as_deref(), right_num.as_deref(), kind) {
            (None, Some(k), OrderKind::GreaterEqual)
                if matches!(
                    compare_number_strings(k, "0"),
                    NumberCompareResult::Greater
                ) =>
            {
                Some(sign_gt_zero(left.clone(), line_file, &mut self.global_ids))
            }
            (Some(k), None, OrderKind::GreaterEqual)
                if matches!(
                    compare_number_strings(k, "0"),
                    NumberCompareResult::Less
                ) =>
            {
                Some(sign_le_zero(right.clone(), line_file, &mut self.global_ids))
            }
            (None, Some(k), OrderKind::Greater)
                if matches!(
                    compare_number_strings(k, "0"),
                    NumberCompareResult::Greater
                ) =>
            {
                Some(sign_gt_zero(left.clone(), line_file, &mut self.global_ids))
            }
            (Some(k), None, OrderKind::Greater)
                if matches!(
                    compare_number_strings(k, "0"),
                    NumberCompareResult::Less | NumberCompareResult::Equal
                ) =>
            {
                Some(sign_le_zero(right.clone(), line_file, &mut self.global_ids))
            }
            (None, Some(k), OrderKind::LessEqual)
                if matches!(
                    compare_number_strings(k, "0"),
                    NumberCompareResult::Less
                ) =>
            {
                Some(sign_le_zero(left.clone(), line_file, &mut self.global_ids))
            }
            (Some(k), None, OrderKind::LessEqual)
                if matches!(
                    compare_number_strings(k, "0"),
                    NumberCompareResult::Greater
                ) =>
            {
                Some(sign_gt_zero(right.clone(), line_file, &mut self.global_ids))
            }
            (None, Some(k), OrderKind::Less)
                if matches!(
                    compare_number_strings(k, "0"),
                    NumberCompareResult::Less | NumberCompareResult::Equal
                ) =>
            {
                Some(sign_le_zero(left.clone(), line_file, &mut self.global_ids))
            }
            (Some(k), None, OrderKind::Less)
                if matches!(
                    compare_number_strings(k, "0"),
                    NumberCompareResult::Greater
                ) =>
            {
                Some(sign_gt_zero(right.clone(), line_file, &mut self.global_ids))
            }
            _ => None,
        };
        let Some(atomic) = target else {
            return Ok(None);
        };
        let derived = Box::new(self.store_inferred_fact_and_infer(&Fact::AtomicFact(atomic))?);
        Ok(Some(InferNumericOrderSignResult { derived }))
    }

    fn infer_order_flip_mul_minus_one_core(
        &mut self,
        left: &Obj,
        right: &Obj,
        kind: OrderKind,
        line_file: Option<crate::new_pipeline::ast::line_file::SourceLine>,
    ) -> RuntimeResult<Option<InferOrderFlipMulMinusOneResult>> {
        if !self.obj_is_resolved_zero(right) {
            return Ok(None);
        }
        if self.peel_mul_by_literal_neg_one(left).is_some() {
            return Ok(None);
        }
        let flipped = obj_mul_literal_neg_one(left.clone());
        let zero = zero_literal();
        let fact_id = self.global_ids.allocate_fact_id();
        let atomic = match kind {
            OrderKind::Less | OrderKind::LessEqual => {
                AtomicFact::GreaterEqualFact(GreaterEqualFact {
                    fact_id,
                    left: flipped,
                    right: zero,
                    line_file,
                })
            }
            OrderKind::Greater => AtomicFact::LessFact(LessFact {
                fact_id,
                left: flipped,
                right: zero,
                line_file,
            }),
            OrderKind::GreaterEqual => AtomicFact::LessEqualFact(LessEqualFact {
                fact_id,
                left: flipped,
                right: zero,
                line_file,
            }),
        };
        let Some(stored) = self.try_store_inferred_fact_and_infer(&Fact::AtomicFact(atomic))? else {
            return Ok(None);
        };
        Ok(Some(InferOrderFlipMulMinusOneResult {
            derived: Box::new(stored),
        }))
    }

    fn peel_mul_by_literal_neg_one(&self, obj: &Obj) -> Option<Obj> {
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(m)) = obj else {
            return None;
        };
        if let Some(ln) = self.resolve_obj_to_normalized_number(m.left.as_ref()) {
            if ln == "-1" {
                return Some(m.right.as_ref().clone());
            }
        }
        if let Some(rn) = self.resolve_obj_to_normalized_number(m.right.as_ref()) {
            if rn == "-1" {
                return Some(m.left.as_ref().clone());
            }
        }
        None
    }
}

#[derive(Clone, Copy)]
enum OrderKind {
    Less,
    Greater,
    LessEqual,
    GreaterEqual,
}

fn obj_mul_literal_neg_one(x: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
        left: Box::new(Obj::Literal(Literal::Number(Number {
            normalized_value: "-1".to_string(),
        }))),
        right: Box::new(x),
    }))
}

fn sign_gt_zero(
    side: Obj,
    line_file: Option<crate::new_pipeline::ast::line_file::SourceLine>,
    global_ids: &mut crate::new_pipeline::runtime::GlobalIds,
) -> AtomicFact {
    // Store `0 < side` (same surface as legacy).
    AtomicFact::LessFact(LessFact {
        fact_id: global_ids.allocate_fact_id(),
        left: zero_literal(),
        right: side,
        line_file,
    })
}

fn sign_le_zero(
    side: Obj,
    line_file: Option<crate::new_pipeline::ast::line_file::SourceLine>,
    global_ids: &mut crate::new_pipeline::runtime::GlobalIds,
) -> AtomicFact {
    AtomicFact::LessEqualFact(LessEqualFact {
        fact_id: global_ids.allocate_fact_id(),
        left: side,
        right: zero_literal(),
        line_file,
    })
}

fn zero_literal() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "0".to_string(),
    }))
}
