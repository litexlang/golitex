//! Eval-mode WD for closed-numeric sources (no ExecEnv WD memoization).
//!
//! Ordinary Add/Mul WD proves each child `$in C`, and InFact WD re-runs full
//! object WD on that child → exponential on left-associated `2*2*…*2`.
//! While `Runtime::eval_closed_numeric_source_wd` is set, closed-numeric objects
//! use children + non-carrier domain checks only; `eval` then adds one root
//! `$in C` gate.

use super::obj_well_defined_by_def_common::ObjWellDefinedByDefCommonStages;
use super::wrap_obj_well_defined_by_def::finish_by_def;
use super::VerifyObjWellDefinedResult;
use crate::ast::fact::{AtomicFact, LessEqualFact, NotEqualFact};
use crate::ast::obj::{
    ArithmeticOperator, ExpLogOperator, IntegerOperator, Literal, Number, Obj, StandardSet,
};
use crate::execute::execute_fact_stmt::well_defined_results::fail_to_verify_obj_well_defined_others;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::rational_expression::ClosedNumericExpr;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Called only from `eval` when the source classifies as closed-numeric.
    pub(crate) fn verify_closed_numeric_source_for_eval(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        if ClosedNumericExpr::try_from_obj(obj).is_none() {
            return Ok(VerifyObjWellDefinedResult::Failed {
                obj: obj.clone(),
                reason: fail_to_verify_obj_well_defined_others(
                    "eval closed-numeric WD requires a closed-numeric source".to_string(),
                ),
            });
        }
        let previous = self.eval_closed_numeric_source_wd;
        self.eval_closed_numeric_source_wd = true;
        let built = self.verify_obj_well_definedness(obj, verify_state.clone());
        let result = match built {
            Ok(VerifyObjWellDefinedResult::Success(proof)) => {
                let gate = self.require_obj_in_standard_set(
                    obj,
                    StandardSet::C,
                    verify_state,
                    "eval closed-numeric source is not in C".to_string(),
                )?;
                if gate.is_failed() {
                    Ok(VerifyObjWellDefinedResult::Failed {
                        obj: obj.clone(),
                        reason: fail_to_verify_obj_well_defined_others(
                            "eval closed-numeric source failed the root `$in C` gate".to_string(),
                        ),
                    })
                } else {
                    Ok(VerifyObjWellDefinedResult::Success(proof))
                }
            }
            other => other,
        };
        self.eval_closed_numeric_source_wd = previous;
        result
    }

    pub(super) fn verify_closed_numeric_source_node_without_carrier(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let stages = self.closed_numeric_source_stages_without_carrier(obj, verify_state)?;
        match finish_by_def(obj, stages, self.result_detail())? {
            Ok(by_def) => Ok(VerifyObjWellDefinedResult::Success(by_def)),
            Err(reason) => Ok(VerifyObjWellDefinedResult::Failed {
                obj: obj.clone(),
                reason,
            }),
        }
    }

    fn closed_numeric_source_stages_without_carrier(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        match obj {
            Obj::Literal(Literal::Number(_)) => {
                Ok(ObjWellDefinedByDefCommonStages::leaf(self.result_detail()))
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Add(v)) => self
                .verify_binary_obj_well_definedness_by_def(
                    v.left.as_ref(),
                    v.right.as_ref(),
                    verify_state,
                ),
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(v)) => self
                .verify_binary_obj_well_definedness_by_def(
                    v.left.as_ref(),
                    v.right.as_ref(),
                    verify_state,
                ),
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(v)) => self
                .verify_binary_obj_well_definedness_by_def(
                    v.left.as_ref(),
                    v.right.as_ref(),
                    verify_state,
                ),
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(v)) => {
                self.verify_unary_obj_well_definedness_by_def(v.arg.as_ref(), verify_state)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Abs(v)) => {
                self.verify_unary_obj_well_definedness_by_def(v.arg.as_ref(), verify_state)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Floor(v)) => {
                self.verify_unary_obj_well_definedness_by_def(v.arg.as_ref(), verify_state)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Ceil(v)) => {
                self.verify_unary_obj_well_definedness_by_def(v.arg.as_ref(), verify_state)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Sign(v)) => {
                self.verify_unary_obj_well_definedness_by_def(v.arg.as_ref(), verify_state)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Min(v)) => self
                .verify_binary_obj_well_definedness_by_def(
                    v.left.as_ref(),
                    v.right.as_ref(),
                    verify_state,
                ),
            Obj::ArithmeticOperator(ArithmeticOperator::Max(v)) => self
                .verify_binary_obj_well_definedness_by_def(
                    v.left.as_ref(),
                    v.right.as_ref(),
                    verify_state,
                ),
            Obj::ArithmeticOperator(ArithmeticOperator::Div(v)) => {
                let proof = self.verify_binary_obj_well_definedness_by_def(
                    v.left.as_ref(),
                    v.right.as_ref(),
                    verify_state.clone(),
                )?;
                let req = self
                    .closed_numeric_nonzero_divisor_requirement(v.right.as_ref(), verify_state)?;
                Ok(self.with_requirements(proof, vec![req]))
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(v)) => self
                .verify_binary_obj_well_definedness_by_def(
                    v.base.as_ref(),
                    v.exponent.as_ref(),
                    verify_state,
                ),
            Obj::IntegerOperator(IntegerOperator::Mod(v)) => {
                let proof = self.verify_binary_obj_well_definedness_by_def(
                    v.left.as_ref(),
                    v.right.as_ref(),
                    verify_state.clone(),
                )?;
                let req = self
                    .closed_numeric_nonzero_divisor_requirement(v.right.as_ref(), verify_state)?;
                Ok(self.with_requirements(proof, vec![req]))
            }
            Obj::IntegerOperator(IntegerOperator::Quot(v)) => {
                let proof = self.verify_binary_obj_well_definedness_by_def(
                    v.left.as_ref(),
                    v.right.as_ref(),
                    verify_state.clone(),
                )?;
                let req = self
                    .closed_numeric_nonzero_divisor_requirement(v.right.as_ref(), verify_state)?;
                Ok(self.with_requirements(proof, vec![req]))
            }
            Obj::IntegerOperator(IntegerOperator::Gcd(v)) => self
                .verify_binary_obj_well_definedness_by_def(
                    v.left.as_ref(),
                    v.right.as_ref(),
                    verify_state,
                ),
            Obj::IntegerOperator(IntegerOperator::Lcm(v)) => self
                .verify_binary_obj_well_definedness_by_def(
                    v.left.as_ref(),
                    v.right.as_ref(),
                    verify_state,
                ),
            Obj::IntegerOperator(IntegerOperator::Factorial(v)) => {
                self.verify_unary_obj_well_definedness_by_def(v.arg.as_ref(), verify_state)
            }
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(v)) => {
                let proof = self.verify_unary_obj_well_definedness_by_def(
                    v.arg.as_ref(),
                    verify_state.clone(),
                )?;
                let req =
                    self.closed_numeric_nonnegative_sqrt_requirement(v.arg.as_ref(), verify_state)?;
                Ok(self.with_requirements(proof, vec![req]))
            }
            Obj::ExpLogOperator(ExpLogOperator::Log(v)) => self
                .verify_binary_obj_well_definedness_by_def(
                    v.base.as_ref(),
                    v.arg.as_ref(),
                    verify_state,
                ),
            Obj::ExpLogOperator(ExpLogOperator::Exp(v)) => {
                self.verify_unary_obj_well_definedness_by_def(v.arg.as_ref(), verify_state)
            }
            Obj::ExpLogOperator(ExpLogOperator::Ln(v)) => {
                self.verify_unary_obj_well_definedness_by_def(v.arg.as_ref(), verify_state)
            }
            _ => Ok(ObjWellDefinedByDefCommonStages::leaf(self.result_detail())),
        }
    }

    fn closed_numeric_nonzero_divisor_requirement(
        &mut self,
        divisor: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<crate::execute::execute_fact_stmt::VerifyFactResult> {
        let zero = Obj::Literal(Literal::Number(Number {
            normalized_value: "0".to_string(),
        }));
        let nonzero = AtomicFact::NotEqualFact(NotEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: divisor.clone(),
            right: zero,
            line_file: None,
        });
        self.verify_required_atomic_fact(
            nonzero,
            verify_state,
            "divisor must be non-zero".to_string(),
        )
    }

    fn closed_numeric_nonnegative_sqrt_requirement(
        &mut self,
        argument: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<crate::execute::execute_fact_stmt::VerifyFactResult> {
        let zero = Obj::Literal(Literal::Number(Number {
            normalized_value: "0".to_string(),
        }));
        let nonnegative = AtomicFact::LessEqualFact(LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: zero,
            right: argument.clone(),
            line_file: None,
        });
        self.verify_required_atomic_fact(
            nonnegative,
            verify_state,
            "sqrt: argument must be >= 0".to_string(),
        )
    }
}
