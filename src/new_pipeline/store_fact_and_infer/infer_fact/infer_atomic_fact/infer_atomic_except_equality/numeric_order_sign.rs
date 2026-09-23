use crate::new_pipeline::ast::fact::{
    AtomicFact, Fact, GreaterFact, GreaterEqualFact, LessFact, LessEqualFact,
};
use crate::new_pipeline::ast::obj::{Literal, Number, Obj};
use crate::new_pipeline::rational_expression::{compare_number_strings, NumberCompareResult};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::InferNumericOrderSignResult;

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

    fn infer_order_sign_core(
        &mut self,
        left: &Obj,
        right: &Obj,
        kind: OrderKind,
        line_file: Option<crate::new_pipeline::ast::line_file::LineFile>,
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
                Some(sign_gt_zero(left.clone(), line_file, &mut self.ids))
            }
            (Some(k), None, OrderKind::GreaterEqual)
                if matches!(
                    compare_number_strings(k, "0"),
                    NumberCompareResult::Less
                ) =>
            {
                Some(sign_le_zero(right.clone(), line_file, &mut self.ids))
            }
            (None, Some(k), OrderKind::Greater)
                if matches!(
                    compare_number_strings(k, "0"),
                    NumberCompareResult::Greater
                ) =>
            {
                Some(sign_gt_zero(left.clone(), line_file, &mut self.ids))
            }
            (Some(k), None, OrderKind::Greater)
                if matches!(
                    compare_number_strings(k, "0"),
                    NumberCompareResult::Less | NumberCompareResult::Equal
                ) =>
            {
                Some(sign_le_zero(right.clone(), line_file, &mut self.ids))
            }
            (None, Some(k), OrderKind::LessEqual)
                if matches!(
                    compare_number_strings(k, "0"),
                    NumberCompareResult::Less
                ) =>
            {
                Some(sign_le_zero(left.clone(), line_file, &mut self.ids))
            }
            (Some(k), None, OrderKind::LessEqual)
                if matches!(
                    compare_number_strings(k, "0"),
                    NumberCompareResult::Greater
                ) =>
            {
                Some(sign_gt_zero(right.clone(), line_file, &mut self.ids))
            }
            (None, Some(k), OrderKind::Less)
                if matches!(
                    compare_number_strings(k, "0"),
                    NumberCompareResult::Less | NumberCompareResult::Equal
                ) =>
            {
                Some(sign_le_zero(left.clone(), line_file, &mut self.ids))
            }
            (Some(k), None, OrderKind::Less)
                if matches!(
                    compare_number_strings(k, "0"),
                    NumberCompareResult::Greater
                ) =>
            {
                Some(sign_gt_zero(right.clone(), line_file, &mut self.ids))
            }
            _ => None,
        };
        let Some(atomic) = target else {
            return Ok(None);
        };
        let derived = Box::new(self.store_inferred_fact_and_infer(&Fact::AtomicFact(atomic))?);
        Ok(Some(InferNumericOrderSignResult { derived }))
    }

    fn resolve_obj_to_normalized_number(&self, obj: &Obj) -> Option<String> {
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
}

#[derive(Clone, Copy)]
enum OrderKind {
    Less,
    Greater,
    LessEqual,
    GreaterEqual,
}

fn sign_gt_zero(
    side: Obj,
    line_file: Option<crate::new_pipeline::ast::line_file::LineFile>,
    ids: &mut crate::new_pipeline::runtime::Ids,
) -> AtomicFact {
    // Store `0 < side` (same surface as legacy).
    AtomicFact::LessFact(LessFact {
        fact_id: ids.allocate_fact_id(),
        left: zero_literal(),
        right: side,
        line_file,
    })
}

fn sign_le_zero(
    side: Obj,
    line_file: Option<crate::new_pipeline::ast::line_file::LineFile>,
    ids: &mut crate::new_pipeline::runtime::Ids,
) -> AtomicFact {
    AtomicFact::LessEqualFact(LessEqualFact {
        fact_id: ids.allocate_fact_id(),
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
