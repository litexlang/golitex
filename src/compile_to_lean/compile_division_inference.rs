use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferEqualFactCommonDenominatorCancellationResult,
    InferEqualFactNonzeroNumeratorCancellationResult,
};

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_common_denominator_inference(
        &self,
        rule: &InferEqualFactCommonDenominatorCancellationResult,
        source: &EqualFact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let mut declarations = Vec::new();
        if rule.source_fact_id != source.fact_id {
            return Err(LeanCompileError::new(
                "Inference/CommonDenominatorSeed",
                "Cancellation cites a different source equality identity.",
            ));
        }
        let (
            Obj::ArithmeticOperator(ArithmeticOperator::Div(source_left)),
            Obj::ArithmeticOperator(ArithmeticOperator::Div(source_right)),
        ) = (&source.left, &source.right)
        else {
            return Err(LeanCompileError::unsupported(
                "Inference/CommonDenominatorConstructor",
            ));
        };
        let captured = &rule.derived;
        let derived = &captured.store_and_infer;
        let fact = self.cancellation_fact(captured, position, "Inference/CommonDenominator")?;
        let Fact::AtomicFact(AtomicFact::EqualFact(equal)) = &fact else {
            unreachable!("the captured store is an equality")
        };
        let a = equal.left.ir();
        let b = equal.right.ir();
        let k = rule.common_operand.ir();
        if !(source_left.left.ir() == a
            && source_left.right.ir() == k
            && source_right.left.ir() == b
            && source_right.right.ir() == k)
        {
            return Err(LeanCompileError::new(
                "Inference/CommonDenominatorOperands",
                "Cancellation does not retain the seed's exact same-position operand and ordered remaining operands.",
            ));
        }
        let lemma = "divCancelCommonDenominator";
        let prior = SourcePosition::new(
            Some(position),
            SourceOwner::CommonDenominatorInference(rule),
            0,
        );
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
            &source_subject(&rule.denominator_nonzero_proof)?,
            &rule.common_operand,
        )?;
        let stage = SourcePosition { before: 3, ..prior };
        let nonzero_3 = self
            .compile_verify(&rule.denominator_nonzero_proof, &stage)?
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
            nonzero_3,
            compiled.1,
        );
        let conclusion = (self.fact_proposition(&fact, &formed)?, proof);
        declarations.push(self.emit_internal_fact(&fact, &conclusion, position));
        let after = SourcePosition::new(
            Some(position),
            SourceOwner::CommonDenominatorInference(rule),
            5,
        );
        let name = format!("h_{}", fact.fact_id().value());
        let reference = if after.is_local() {
            name
        } else {
            self.context_application(&name, &after)
        };
        declarations.extend(self.compile_stored_inferences(
            derived,
            &fact,
            &(conclusion.0, reference),
            &after,
        )?);
        Ok(declarations)
    }
}

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_nonzero_numerator_inference(
        &self,
        rule: &InferEqualFactNonzeroNumeratorCancellationResult,
        source: &EqualFact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let mut declarations = Vec::new();
        if rule.source_fact_id != source.fact_id {
            return Err(LeanCompileError::new(
                "Inference/NonzeroNumeratorSeed",
                "Cancellation cites a different source equality identity.",
            ));
        }
        let (
            Obj::ArithmeticOperator(ArithmeticOperator::Div(source_left)),
            Obj::ArithmeticOperator(ArithmeticOperator::Div(source_right)),
        ) = (&source.left, &source.right)
        else {
            return Err(LeanCompileError::unsupported(
                "Inference/NonzeroNumeratorConstructor",
            ));
        };
        let captured = &rule.derived;
        let derived = &captured.store_and_infer;
        let fact = self.cancellation_fact(captured, position, "Inference/NonzeroNumerator")?;
        let Fact::AtomicFact(AtomicFact::EqualFact(equal)) = &fact else {
            unreachable!("the captured store is an equality")
        };
        let a = equal.left.ir();
        let b = equal.right.ir();
        let k = rule.common_operand.ir();
        if !(source_left.left.ir() == k
            && source_left.right.ir() == a
            && source_right.left.ir() == k
            && source_right.right.ir() == b)
        {
            return Err(LeanCompileError::new(
                "Inference/NonzeroNumeratorOperands",
                "Cancellation does not retain the seed's exact same-position operand and ordered remaining operands.",
            ));
        }
        let lemma = "divCancelNonzeroNumerator";
        let prior = SourcePosition::new(
            Some(position),
            SourceOwner::NonzeroNumeratorInference(rule),
            0,
        );
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
            &source_subject(&rule.numerator_nonzero_proof)?,
            &rule.common_operand,
        )?;
        let stage = SourcePosition { before: 3, ..prior };
        let nonzero_3 = self
            .compile_verify(&rule.numerator_nonzero_proof, &stage)?
            .1;
        ensure_nonzero_subject(
            &source_subject(&rule.left_denominator_nonzero_proof)?,
            &equal.left,
        )?;
        let stage = SourcePosition { before: 4, ..prior };
        let nonzero_4 = self
            .compile_verify(&rule.left_denominator_nonzero_proof, &stage)?
            .1;
        ensure_nonzero_subject(
            &source_subject(&rule.right_denominator_nonzero_proof)?,
            &equal.right,
        )?;
        let stage = SourcePosition { before: 5, ..prior };
        let nonzero_5 = self
            .compile_verify(&rule.right_denominator_nonzero_proof, &stage)?
            .1;
        let formation = SourcePosition { before: 6, ..prior };
        self.compile_fact_wd(&captured.well_defined, &fact, &formation)?;
        let formed = SourcePosition::new(
            Some(&formation),
            SourceOwner::FactWD(&captured.well_defined),
            usize::MAX,
        );
        let proof = format!(
            "(Litex.{lemma} {} {} {} {} {} {} {} {} {} {})",
            self.compile_object_reference(&equal.left, &formed)?,
            self.compile_object_reference(&equal.right, &formed)?,
            self.compile_object_reference(&rule.common_operand, &formed)?,
            members[0],
            members[1],
            members[2],
            nonzero_3,
            nonzero_4,
            nonzero_5,
            compiled.1,
        );
        let conclusion = (self.fact_proposition(&fact, &formed)?, proof);
        declarations.push(self.emit_internal_fact(&fact, &conclusion, position));
        let after = SourcePosition::new(
            Some(position),
            SourceOwner::NonzeroNumeratorInference(rule),
            7,
        );
        let name = format!("h_{}", fact.fact_id().value());
        let reference = if after.is_local() {
            name
        } else {
            self.context_application(&name, &after)
        };
        declarations.extend(self.compile_stored_inferences(
            derived,
            &fact,
            &(conclusion.0, reference),
            &after,
        )?);
        Ok(declarations)
    }
}
