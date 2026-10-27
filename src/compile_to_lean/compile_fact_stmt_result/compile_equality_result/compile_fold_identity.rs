use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_reduce_last_step(
        &self,
        fact: &EqualFact,
        proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_reduce_last_step::ReduceLastStepProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let nonempty = source_subject(&proof.nonempty)?;
        let endpoint = source_subject(&proof.endpoint)?;
        let result = source_subject(&proof.result)?;
        let (
            Fact::AtomicFact(AtomicFact::LessEqualFact(nonempty)),
            Fact::AtomicFact(AtomicFact::EqualFact(endpoint)),
            Fact::AtomicFact(AtomicFact::EqualFact(result)),
        ) = (&nonempty, &endpoint, &result)
        else {
            return Err(LeanCompileError::unsupported("ReduceLastStep/Requirements"));
        };
        for (whole, other, reverse) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Obj::IteratedOperator(IteratedOperator::Reduce(fold)) = whole else {
                continue;
            };
            if nonempty.left.ir() != fold.start.ir()
                || nonempty.right.ir() != fold.end.ir()
                || result.right.ir() != other.ir()
                || !matches!(&endpoint.left, Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) if p.left.ir() == fold.end.ir() && matches!(p.right.as_ref(), Obj::Literal(Literal::Number(_))) && closed_integer(&p.right) == Some(1))
            {
                continue;
            }
            let previous = Obj::IteratedOperator(IteratedOperator::Reduce(Reduce {
                start: fold.start.clone(),
                end: Box::new(endpoint.right.clone()),
                func: fold.func.clone(),
                op: fold.op.clone(),
                seed: fold.seed.clone(),
            }));
            let term = fold_application(&fold.func, &[fold.end.as_ref().clone()])?;
            let unfolded_previous = Obj::IteratedOperator(IteratedOperator::Reduce(Reduce {
                start: fold.start.clone(),
                end: Box::new(endpoint.left.clone()),
                func: fold.func.clone(),
                op: fold.op.clone(),
                seed: fold.seed.clone(),
            }));
            let unfolded = fold_application(&fold.op, &[unfolded_previous, term.clone()])?;
            let expected = fold_application(&fold.op, &[previous, term])?;
            if result.left.ir() != expected.ir() {
                continue;
            }
            let first = self.compile_verify(&proof.nonempty, position)?;
            let first_position = SourcePosition::new(
                Some(position),
                SourceOwner::Verify(&proof.nonempty),
                usize::MAX,
            );
            let second = self.compile_verify(&proof.endpoint, &first_position)?;
            let second_position = SourcePosition::new(
                Some(&first_position),
                SourceOwner::Verify(&proof.endpoint),
                usize::MAX,
            );
            let third = self.compile_verify(&proof.result, &second_position)?;
            let formed = SourcePosition::new(
                Some(&second_position),
                SourceOwner::Verify(&proof.result),
                usize::MAX,
            );
            let object = self.compile_object_reference(whole, position)?;
            let endpoint_raw_left = self.compile_normalization_value(&endpoint.left, &formed)?;
            let endpoint_raw_right = self.compile_normalization_value(&endpoint.right, &formed)?;
            let whole_raw = self.compile_function_raw_expression_bound(
                whole,
                &formed,
                &std::collections::HashMap::new(),
            )?;
            let expected_raw = self.compile_function_raw_expression_bound(
                &result.left,
                &formed,
                &std::collections::HashMap::new(),
            )?;
            let unfolded_raw = self.compile_function_raw_expression_bound(
                &unfolded,
                &formed,
                &std::collections::HashMap::new(),
            )?;
            let result_left = self.compile_object_reference(&result.left, &formed)?;
            let first_id = nonempty.fact_id.value();
            let second_id = endpoint.fact_id.value();
            let third_id = result.fact_id.value();
            let ending = if reverse { ".symm" } else { "" };
            return Ok(format!("(by\n  have h_{first_id} : {} := {}\n  have h_{second_id} : {} := {}\n  have h_{third_id} : {} := {}\n  have _endpoint : {endpoint_raw_left} = {endpoint_raw_right} := h_{second_id}\n  have _step : Litex.Same {object} {result_left} := by\n    change {whole_raw} = {expected_raw}\n    have _last := Litex.rangeFoldLast {object} h_{first_id}\n    change {whole_raw} = {unfolded_raw} at _last\n    simpa only [_endpoint] using _last\n  exact (_step.trans h_{third_id}){ending})", first.0, first.1, second.0, second.1, third.0, third.1));
        }
        Err(LeanCompileError::unsupported("ReduceLastStep/Subjects"))
    }

    pub(super) fn compile_finite_fold_empty(
        &self,
        fact: &EqualFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (fold, seed, reverse) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(value)) = fold else {
                continue;
            };
            if value.seed.ir() != seed.ir()
                || !matches!(value.set.as_ref(), Obj::SetFormer(SetFormer::ListSet(s)) if s.list.is_empty())
            {
                continue;
            }
            let object = self.compile_object_reference(fold, position)?;
            let orientation = if reverse { ".symm" } else { "" };
            return Ok(format!(
                "((Litex.finiteFoldEmpty {object} rfl){orientation})"
            ));
        }
        Err(LeanCompileError::unsupported("FiniteFoldEmpty/Subjects"))
    }

    pub(super) fn compile_reduce_empty(
        &self,
        fact: &EqualFact,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if requirements.len() != 1 {
            return Err(LeanCompileError::unsupported("ReduceEmpty/Requirement"));
        }
        let goal = source_subject(&requirements[0])?;
        for (fold, seed, reverse) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Obj::IteratedOperator(IteratedOperator::Reduce(value)) = fold else {
                continue;
            };
            if value.seed.ir() != seed.ir()
                || !matches!(&goal, Fact::AtomicFact(AtomicFact::LessFact(f)) if f.left.ir()==value.end.ir() && f.right.ir()==value.start.ir())
            {
                continue;
            }
            let prior = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(requirements),
                0,
            );
            let proof = self.compile_verify(&requirements[0], &prior)?.1;
            let object = self.compile_object_reference(fold, position)?;
            let orientation = if reverse { ".symm" } else { "" };
            return Ok(format!(
                "((Litex.rangeFoldEmptyOfLt {object} {proof}){orientation})"
            ));
        }
        Err(LeanCompileError::unsupported("ReduceEmpty/Subjects"))
    }
}
