//! Fixed-base identities under the enclosing equality's checked object WD.
use super::search_equal_fact_builtin_rule_result::EqualitySearchProofByBuiltinRule;
use crate::ast::fact::EqualFact;
use crate::ast::obj::{ArithmeticOperator, ExpLogOperator, Literal, Obj};

pub struct LnAsEulerLogProof {}
impl LnAsEulerLogProof {
    pub fn new() -> Self {
        Self {}
    }
}
pub struct ExpAsEulerIntegerPowerProof {}
impl ExpAsEulerIntegerPowerProof {
    pub fn new() -> Self {
        Self {}
    }
}

// ln(x)=log(e,x) for x in R+; exp(n)=e^n on the current integer power domain.
// Parent equality WD checks both expressions, including log-base and power guards.
// This leaf only checks the literal Euler base and the identical bound argument.
pub(super) fn native_fixed_base(fact: &EqualFact) -> Option<EqualitySearchProofByBuiltinRule> {
    for (native, other) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
        match (native, other) {
            (
                Obj::ExpLogOperator(ExpLogOperator::Ln(ln)),
                Obj::ExpLogOperator(ExpLogOperator::Log(log)),
            ) if matches!(log.base.as_ref(), Obj::Literal(Literal::EulerNumber(_)))
                && ln.arg.ir() == log.arg.ir() =>
            {
                return Some(EqualitySearchProofByBuiltinRule::LnAsEulerLog(
                    LnAsEulerLogProof::new(),
                ));
            }
            (
                Obj::ExpLogOperator(ExpLogOperator::Exp(exp)),
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(pow)),
            ) if matches!(pow.base.as_ref(), Obj::Literal(Literal::EulerNumber(_)))
                && exp.arg.ir() == pow.exponent.ir() =>
            {
                return Some(EqualitySearchProofByBuiltinRule::ExpAsEulerIntegerPower(
                    ExpAsEulerIntegerPowerProof::new(),
                ));
            }
            _ => {}
        }
    }
    None
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/native_fixed_base/tests.rs"]
mod native_fixed_base_tests;
