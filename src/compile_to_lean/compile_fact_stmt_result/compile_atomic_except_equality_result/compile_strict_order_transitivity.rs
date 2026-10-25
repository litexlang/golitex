use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less::LessTransitivityBuiltinRuleProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_strict_order_transitivity(
        &self,
        goal: &AtomicFact,
        proof: &LessTransitivityBuiltinRuleProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (left, right, strict) = source_order_oriented(goal)?;
        let law = match (proof.left_to_mid_strict, proof.mid_to_right_strict) {
            (true, true) => "ltTrans",
            (true, false) => "ltLeTrans",
            (false, true) => "leLtTrans",
            (false, false) => {
                return Err(LeanCompileError::unsupported(
                    "StrictTransitivity/NoStrictPremise",
                ))
            }
        };
        let first = self.compile_registered_order(proof.left_to_mid_cite_fact_id, position)?;
        let second = self.compile_registered_order(proof.mid_to_right_cite_fact_id, position)?;
        let (a, b, first_strict) = source_order_oriented(first.0)?;
        let (b2, c, second_strict) = source_order_oriented(second.0)?;
        if !strict
            || a.ir() != left.ir()
            || b.ir() != b2.ir()
            || c.ir() != right.ir()
            || first_strict != proof.left_to_mid_strict
            || second_strict != proof.mid_to_right_strict
        {
            return Err(LeanCompileError::new(
                "StrictTransitivity/CitationSubject",
                "The original citations must form this left-middle-right chain and match both recorded strictness flags.",
            ));
        }
        Ok(format!(
            "(Litex.{law} {} {} {} {} {})",
            self.compile_object_reference(a, position)?,
            self.compile_object_reference(b, position)?,
            self.compile_object_reference(c, position)?,
            first.1,
            second.1,
        ))
    }
}
