//! Monotonicity of two already-defined principal real square roots.
use super::less_equal::LessEqualFactSearchProofByBuiltinRule;
use crate::ast::fact::{Fact, GreaterEqualFact, LessEqualFact};
use crate::ast::obj::{ExpLogOperator, Obj};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

pub struct SqrtMonotoneFromDefinedRootsProof {
    pub arguments_order: VerifyFactResult,
}
impl SqrtMonotoneFromDefinedRootsProof {
    pub fn new(arguments_order: VerifyFactResult) -> Self {
        Self { arguments_order }
    }
}
impl Runtime {
    pub(super) fn sqrt_monotone_from_defined_roots(
        &mut self,
        fact: &LessEqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let (
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(left)),
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(right)),
        ) = (&fact.left, &fact.right)
        else {
            return Ok(None);
        };
        // Parent WD has proved both real, nonnegative radicands. Do not
        // rediscover that domain below the builtin's premise ceiling.
        // Example: 0<=x, x<=y => sqrt(x)<=sqrt(y).
        let requirement: Fact = LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: *left.arg.clone(),
            right: *right.arg.clone(),
            line_file: fact.line_file.clone(),
        }
        .into();
        let mut arguments_order = self.verify_builtin_rule_premise(&requirement, state)?;
        if arguments_order.is_failed() {
            let requirement: Fact = GreaterEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: *right.arg.clone(),
                right: *left.arg.clone(),
                line_file: fact.line_file.clone(),
            }
            .into();
            arguments_order = self.verify_builtin_rule_premise(&requirement, state)?;
        }
        if arguments_order.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::SqrtMonotoneFromDefinedRoots(
                SqrtMonotoneFromDefinedRootsProof::new(arguments_order),
            ),
        ))
    }
}
