//! Nonzero/nonunit evidence needed to use common Obj relationship formulas.
use super::not_equal::NotEqualFactSearchProofByBuiltinRule;
use crate::ast::fact::{Fact, InFact, NotEqualFact};
use crate::ast::obj::{ArithmeticOperator, ExpLogOperator, IntegerOperator, Literal, Number, Obj, StandardSet};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::log_algebra_base_proof::LogAlgebraBaseProof;
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

pub struct LcmNonzeroFromNonzeroOperandsProof {
    pub first_nonzero: VerifyFactResult,
    pub second_nonzero: VerifyFactResult,
}
pub struct LogNonzeroFromNonunitArgumentProof {
    pub base_proof: LogAlgebraBaseProof,
    pub argument_proof: LogAlgebraBaseProof,
}
pub struct PositiveNonunitIntegerPowerProof {
    pub base_proof: LogAlgebraBaseProof,
    pub exponent_integer: VerifyFactResult,
    pub exponent_nonzero: VerifyFactResult,
}

impl Runtime {
    pub(super) fn search_common_relation_nonzero(
        &mut self,
        fact: &NotEqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<NotEqualFactSearchProofByBuiltinRule>> {
        let zero = Obj::Literal(Literal::Number(Number::new("0".into())));
        let one = Obj::Literal(Literal::Number(Number::new("1".into())));
        for (value, excluded) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if excluded.ir() == zero.ir() {
                if let Obj::IntegerOperator(IntegerOperator::Lcm(lcm)) = value {
                    // Parent WD checks integer operands; a,b!=0 => lcm(a,b)!=0.
                    let first_nonzero = self.verify_order_nonzero(&lcm.left, state)?;
                    if first_nonzero.is_failed() {
                        continue;
                    }
                    let second_nonzero = self.verify_order_nonzero(&lcm.right, state)?;
                    if second_nonzero.is_failed() {
                        continue;
                    }
                    return Ok(Some(
                        NotEqualFactSearchProofByBuiltinRule::LcmNonzeroFromNonzeroOperands(
                            LcmNonzeroFromNonzeroOperandsProof {
                                first_nonzero,
                                second_nonzero,
                            },
                        ),
                    ));
                }
                if let Obj::ExpLogOperator(ExpLogOperator::Log(log)) = value {
                    // Example: b>0, b!=1, x>0, x!=1 => log(b,x)!=0.
                    let Some(base_proof) = self.verify_log_algebra_base_guard(&log.base, state)?
                    else {
                        continue;
                    };
                    // The same positive-nonunit guard accepts x<1 or x>1
                    // directly, without requiring a deeper derived x!=1.
                    let Some(argument_proof) =
                        self.verify_log_algebra_base_guard(&log.arg, state)?
                    else {
                        continue;
                    };
                    return Ok(Some(
                        NotEqualFactSearchProofByBuiltinRule::LogNonzeroFromNonunitArgument(
                            LogNonzeroFromNonunitArgumentProof {
                                base_proof,
                                argument_proof,
                            },
                        ),
                    ));
                }
            }
            if excluded.ir() == one.ir() {
                if let Obj::ArithmeticOperator(ArithmeticOperator::Pow(pow)) = value {
                    // Example: b>0, b!=1, n in Z, n!=0 => b^n!=1.
                    let Some(base_proof) = self.verify_log_algebra_base_guard(&pow.base, state)?
                    else {
                        continue;
                    };
                    let integer: Fact = InFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        element: *pow.exponent.clone(),
                        set: Obj::StandardSet(StandardSet::Z),
                        line_file: fact.line_file.clone(),
                    }
                    .into();
                    let exponent_integer = self.verify_builtin_rule_premise(&integer, state)?;
                    if exponent_integer.is_failed() {
                        continue;
                    }
                    let exponent_nonzero = self.verify_order_nonzero(&pow.exponent, state)?;
                    if exponent_nonzero.is_failed() {
                        continue;
                    }
                    return Ok(Some(
                        NotEqualFactSearchProofByBuiltinRule::PositiveNonunitIntegerPower(
                            PositiveNonunitIntegerPowerProof {
                                base_proof,
                                exponent_integer,
                                exponent_nonzero,
                            },
                        ),
                    ));
                }
            }
        }
        Ok(None)
    }
}
