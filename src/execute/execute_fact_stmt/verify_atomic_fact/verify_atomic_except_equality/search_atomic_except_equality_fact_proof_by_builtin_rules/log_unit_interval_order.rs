//! Same-base logarithms with 0<a<1 reverse strict and weak order.
//! Parent log WD retains real carriers, positivity and the nonunit base.
use super::less::LessFactSearchProofByBuiltinRule;
use super::less_equal::LessEqualFactSearchProofByBuiltinRule;
use crate::ast::line_file::SourceLine;
use crate::ast::obj::{Literal, Number, Obj};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

// Mandatory guards, in the order they are actually checked.
pub struct LogUnitIntervalOrderGuardsProof {
    pub base_positive_proof: VerifyFactResult,
    pub base_lt_one_proof: VerifyFactResult,
    pub left_arg_positive_proof: VerifyFactResult,
    pub right_arg_positive_proof: VerifyFactResult,
}
impl LogUnitIntervalOrderGuardsProof {
    pub fn new(
        base_positive_proof: VerifyFactResult,
        base_lt_one_proof: VerifyFactResult,
        left_arg_positive_proof: VerifyFactResult,
        right_arg_positive_proof: VerifyFactResult,
    ) -> Self {
        Self { base_positive_proof, base_lt_one_proof, left_arg_positive_proof, right_arg_positive_proof }
    }
}

// Example: 0<a<1, 0<x,y and x<y => log(a,y)<log(a,x).
pub struct LogStrictDecreasingProof {
    pub guards: LogUnitIntervalOrderGuardsProof,
    pub argument_order: VerifyFactResult,
}
impl LogStrictDecreasingProof {
    pub fn new(guards: LogUnitIntervalOrderGuardsProof, argument_order: VerifyFactResult) -> Self {
        Self { guards, argument_order }
    }
}

// Example: 0<a<1, 0<x,y and x<=y => log(a,y)<=log(a,x).
pub struct LogWeakDecreasingProof {
    pub guards: LogUnitIntervalOrderGuardsProof,
    pub argument_order: VerifyFactResult,
}
impl LogWeakDecreasingProof {
    pub fn new(guards: LogUnitIntervalOrderGuardsProof, argument_order: VerifyFactResult) -> Self {
        Self { guards, argument_order }
    }
}

impl Runtime {
    // Caller has matched two logs with exactly the same IR base.
    pub(super) fn log_unit_interval_strict_proof(
        &mut self,
        base: &Obj,
        left_arg: &Obj,
        right_arg: &Obj,
        line_file: Option<SourceLine>,
        state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        let Some(guards) = self.log_unit_interval_order_guards(
            base, left_arg, right_arg, line_file.clone(), state,
        )? else { return Ok(None); };
        // The target left log has the larger argument; preserve the actual
        // right_arg < left_arg or left_arg > right_arg source and its citation.
        let Some(argument_order) = self.strict_order_premise(
            right_arg, left_arg, line_file, state,
        )? else { return Ok(None); };
        Ok(Some(LessFactSearchProofByBuiltinRule::LogStrictDecreasing(
            LogStrictDecreasingProof::new(guards, argument_order),
        )))
    }

    pub(super) fn log_unit_interval_weak_proof(
        &mut self,
        base: &Obj,
        left_arg: &Obj,
        right_arg: &Obj,
        line_file: Option<SourceLine>,
        state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let Some(guards) = self.log_unit_interval_order_guards(
            base, left_arg, right_arg, line_file.clone(), state,
        )? else { return Ok(None); };
        let Some(argument_order) = self.weak_order_premise(
            right_arg, left_arg, line_file, state,
        )? else { return Ok(None); };
        Ok(Some(LessEqualFactSearchProofByBuiltinRule::LogWeakDecreasing(
            LogWeakDecreasingProof::new(guards, argument_order),
        )))
    }

    fn log_unit_interval_order_guards(
        &mut self,
        base: &Obj,
        left_arg: &Obj,
        right_arg: &Obj,
        line_file: Option<SourceLine>,
        state: VerifyState,
    ) -> RuntimeResult<Option<LogUnitIntervalOrderGuardsProof>> {
        let zero = Obj::Literal(Literal::Number(Number { normalized_value: "0".to_string() }));
        let one = Obj::Literal(Literal::Number(Number { normalized_value: "1".to_string() }));
        let Some(base_positive_proof) = self.strict_order_premise(&zero, base, line_file.clone(), state)? else { return Ok(None); };
        let Some(base_lt_one_proof) = self.strict_order_premise(base, &one, line_file.clone(), state)? else { return Ok(None); };
        let Some(left_arg_positive_proof) = self.strict_order_premise(&zero, left_arg, line_file.clone(), state)? else { return Ok(None); };
        let Some(right_arg_positive_proof) = self.strict_order_premise(&zero, right_arg, line_file, state)? else { return Ok(None); };
        Ok(Some(LogUnitIntervalOrderGuardsProof::new(
            base_positive_proof, base_lt_one_proof, left_arg_positive_proof, right_arg_positive_proof,
        )))
    }
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/log_unit_interval_order/tests.rs"]
mod log_unit_interval_order_tests;
