use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_greater::NotGreaterFactSearchProofByBuiltinRule;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_negative_order_builtin(
        &self,
        goal: &AtomicFact,
        rule: &AtomicExceptEqualityFactSearchProofByBuiltinRule,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (
            AtomicFact::NotGreaterFact(goal),
            AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterFact(
                NotGreaterFactSearchProofByBuiltinRule::FromKnownOrderComplement(proof),
            ),
        ) = (goal, rule)
        else {
            return Err(LeanCompileError::unsupported("Order/NegativeBuiltin"));
        };
        if !matches!(&proof.premise_proof.fact, AtomicFact::LessEqualFact(f) if f.left.ir()==goal.left.ir() && f.right.ir()==goal.right.ir())
            || proof.real_carrier_proofs.len() != 2
        {
            return Err(LeanCompileError::unsupported("Order/ComplementSubjects"));
        }
        let left = self.compile_object_reference(&goal.left, position)?;
        let right = self.compile_object_reference(&goal.right, position)?;
        let real = [&goal.left, &goal.right]
            .into_iter()
            .zip(&proof.real_carrier_proofs)
            .map(|(obj, result)| {
                if membership_subject(&source_subject(result)?, obj)? != StandardSet::R {
                    return Err(LeanCompileError::unsupported("Order/ComplementRealCarrier"));
                }
                Ok(self.compile_verify(result, position)?.1)
            })
            .collect::<Result<Vec<_>, LeanCompileError>>()?;
        let premise = self
            .compile_order_known_premise(&proof.premise_proof, position)?
            .1;
        Ok(format!("(fun _strict => not_lt_of_ge ((Litex.NativeBridge.le_iff_asReal {left} {right} {} {}).mp {premise}) ((Litex.NativeBridge.lt_iff_asReal {right} {left} {} {}).mp _strict))", real[0], real[1], real[1], real[0]))
    }
}
