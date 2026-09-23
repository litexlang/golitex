use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact, Fact};
use crate::new_pipeline::ast::obj::{ArithmeticOperator, Literal, Number, Obj};
use crate::new_pipeline::rational_expression::{compare_number_strings, NumberCompareResult};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::InferEqualFactSubtractionEqualsZeroResult;

impl Runtime {
    // When: stored `0 = u - v` or `u - v = 0` with u, v distinct by ir.
    // Infers: `u = v`.
    // Example: `0 = a - b` ⇒ `a = b`.
    // Uses literal `0` only (not equality-resolved): after store, `u-v` is already
    // known equal to 0, so resolved-zero would mis-read the Sub side as zero.
    pub(super) fn infer_equal_fact_subtraction_equals_zero(
        &mut self,
        equal_fact: &EqualFact,
    ) -> RuntimeResult<Option<InferEqualFactSubtractionEqualsZeroResult>> {
        let (a, b) = if obj_is_literal_zero(&equal_fact.left) {
            match &equal_fact.right {
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(s)) => {
                    (s.left.as_ref().clone(), s.right.as_ref().clone())
                }
                _ => return Ok(None),
            }
        } else if obj_is_literal_zero(&equal_fact.right) {
            match &equal_fact.left {
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(s)) => {
                    (s.left.as_ref().clone(), s.right.as_ref().clone())
                }
                _ => return Ok(None),
            }
        } else {
            return Ok(None);
        };
        if a.ir() == b.ir() {
            return Ok(None);
        }
        let fact_id = self.global_ids.allocate_fact_id();
        let atomic = AtomicFact::EqualFact(EqualFact {
            fact_id,
            left: a,
            right: b,
            line_file: equal_fact.line_file.clone(),
        });
        let derived = Box::new(self.store_inferred_fact_and_infer(&Fact::AtomicFact(atomic))?);
        Ok(Some(InferEqualFactSubtractionEqualsZeroResult { derived }))
    }
}

fn obj_is_literal_zero(obj: &Obj) -> bool {
    match obj {
        Obj::Literal(Literal::Number(Number { normalized_value })) => matches!(
            compare_number_strings(normalized_value, "0"),
            NumberCompareResult::Equal
        ),
        _ => false,
    }
}
