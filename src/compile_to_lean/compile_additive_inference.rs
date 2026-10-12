use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::InferEqualFactAdditiveCancellationResult;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_additive_inference(
        &self,
        rule: &InferEqualFactAdditiveCancellationResult,
        source: &EqualFact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let mut declarations = Vec::new();
        if rule.source_fact_id != source.fact_id {
            return Err(LeanCompileError::new(
                "Inference/AdditiveSeed",
                "Cancellation cites a different source equality identity.",
            ));
        }
        let (
            Obj::ArithmeticOperator(ArithmeticOperator::Add(source_left)),
            Obj::ArithmeticOperator(ArithmeticOperator::Add(source_right)),
        ) = (&source.left, &source.right)
        else {
            return Err(LeanCompileError::unsupported(
                "Inference/AdditiveConstructor",
            ));
        };
        let captured = &rule.derived;
        let fact = self.cancellation_fact(captured, position, "Inference/Additive")?;
        let Fact::AtomicFact(AtomicFact::EqualFact(equal)) = &fact else {
            unreachable!("the captured store is an equality")
        };
        let a = equal.left.ir();
        let b = equal.right.ir();
        let k = rule.common_operand.ir();
        let left_right = source_left.left.ir() == a && source_left.right.ir() == k;
        let left_left = source_left.left.ir() == k && source_left.right.ir() == a;
        let right_right = source_right.left.ir() == b && source_right.right.ir() == k;
        let right_left = source_right.left.ir() == k && source_right.right.ir() == b;
        let lemma = if left_right && right_right {
            "addCancelRightRight"
        } else if left_right && right_left {
            "addCancelRightLeft"
        } else if left_left && right_right {
            "addCancelLeftRight"
        } else if left_left && right_left {
            "addCancelLeftLeft"
        } else {
            return Err(LeanCompileError::new(
                "Inference/AdditiveOperands",
                "Cancellation does not retain the seed's exact shared addend and ordered remaining operands.",
            ));
        };
        let prior = SourcePosition::new(Some(position), SourceOwner::AdditiveInference(rule), 0);
        let members = self.compile_cancellation_members(
            [
                &rule.left_in_c_proof,
                &rule.right_in_c_proof,
                &rule.common_in_c_proof,
            ],
            [&equal.left, &equal.right, &rule.common_operand],
            &prior,
        )?;
        let formation = SourcePosition { before: 3, ..prior };
        let formed = SourcePosition::new(
            Some(&formation),
            SourceOwner::InferredStore(&captured.store),
            usize::MAX,
        );
        let proof = format!(
            "(Litex.{lemma} {} {} {} {} {} {} {})",
            self.compile_object_reference(&equal.left, &formed)?,
            self.compile_object_reference(&equal.right, &formed)?,
            self.compile_object_reference(&rule.common_operand, &formed)?,
            members[0],
            members[1],
            members[2],
            compiled.1,
        );
        let conclusion = (self.fact_proposition(&fact, &formed)?, proof);
        declarations.push(self.emit_internal_fact(&fact, &conclusion, position));
        Ok(declarations)
    }
}
