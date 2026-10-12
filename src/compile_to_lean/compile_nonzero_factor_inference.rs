use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::InferEqualFactNonzeroFactorCancellationResult;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_nonzero_factor_inference(
        &self,
        rule: &InferEqualFactNonzeroFactorCancellationResult,
        source: &EqualFact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let mut declarations = Vec::new();
        if rule.source_fact_id != source.fact_id {
            return Err(LeanCompileError::new(
                "Inference/NonzeroFactorSeed",
                "Cancellation cites a different source equality identity.",
            ));
        }
        let (
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(source_left)),
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(source_right)),
        ) = (&source.left, &source.right)
        else {
            return Err(LeanCompileError::unsupported(
                "Inference/NonzeroFactorConstructor",
            ));
        };
        let captured = &rule.derived;
        let fact = self.cancellation_fact(captured, position, "Inference/NonzeroFactor")?;
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
            "mulCancelRightRight"
        } else if left_right && right_left {
            "mulCancelRightLeft"
        } else if left_left && right_right {
            "mulCancelLeftRight"
        } else if left_left && right_left {
            "mulCancelLeftLeft"
        } else {
            return Err(LeanCompileError::new(
                "Inference/NonzeroFactorOperands",
                "Cancellation does not retain the seed's exact shared factor and ordered remaining operands.",
            ));
        };
        let prior =
            SourcePosition::new(Some(position), SourceOwner::NonzeroFactorInference(rule), 0);
        let members = self.compile_cancellation_members(
            [
                &rule.left_in_c_proof,
                &rule.right_in_c_proof,
                &rule.common_in_c_proof,
            ],
            [&equal.left, &equal.right, &rule.common_operand],
            &prior,
        )?;
        ensure_nonzero_subject(
            &source_subject(&rule.factor_nonzero_proof)?,
            &rule.common_operand,
        )?;
        let nonzero_stage = SourcePosition { before: 3, ..prior };
        let nonzero = self
            .compile_verify(&rule.factor_nonzero_proof, &nonzero_stage)?
            .1;
        let formation = SourcePosition { before: 4, ..prior };
        self.compile_fact_wd(&captured.well_defined, &fact, &formation)?;
        let formed = SourcePosition::new(
            Some(&formation),
            SourceOwner::FactWD(&captured.well_defined),
            usize::MAX,
        );
        let proof = format!(
            "(Litex.{lemma} {} {} {} {} {} {} {} {})",
            self.compile_object_reference(&equal.left, &formed)?,
            self.compile_object_reference(&equal.right, &formed)?,
            self.compile_object_reference(&rule.common_operand, &formed)?,
            members[0],
            members[1],
            members[2],
            nonzero,
            compiled.1,
        );
        let conclusion = (self.fact_proposition(&fact, &formed)?, proof);
        declarations.push(self.emit_internal_fact(&fact, &conclusion, position));
        let after =
            SourcePosition::new(Some(position), SourceOwner::NonzeroFactorInference(rule), 5);
        let name = format!("h_{}", fact.fact_id().value());
        let reference = if after.is_local() {
            name
        } else {
            self.context_application(&name, &after)
        };
        Ok(declarations)
    }
}
