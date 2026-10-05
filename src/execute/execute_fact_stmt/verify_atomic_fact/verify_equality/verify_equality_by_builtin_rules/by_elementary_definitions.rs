//! Native defining identities; all input domains are retained in parent WD.
use super::search_equal_fact_builtin_rule_result::EqualitySearchProofByBuiltinRule;
use crate::ast::fact::EqualFact;
use crate::ast::obj::{ArithmeticOperator, IntegerOperator, Obj, TrigOperator};

pub struct TanQuotientDefinitionProof {}
impl TanQuotientDefinitionProof {
    pub fn new() -> Self {
        Self {}
    }
}
pub struct CotQuotientDefinitionProof {}
impl CotQuotientDefinitionProof {
    pub fn new() -> Self {
        Self {}
    }
}
pub struct GcdEuclideanStepProof {}
impl GcdEuclideanStepProof {
    pub fn new() -> Self {
        Self {}
    }
}

// Exact argument matching only. Parent WD proves real trig inputs,
// nonzero denominators, integer gcd inputs and a nonzero remainder divisor.
pub(super) fn elementary_definition(fact: &EqualFact) -> Option<EqualitySearchProofByBuiltinRule> {
    for (native, other) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
        match (native, other) {
            (
                Obj::TrigOperator(TrigOperator::Tan(tan)),
                Obj::ArithmeticOperator(ArithmeticOperator::Div(div)),
            ) => {
                if let (
                    Obj::TrigOperator(TrigOperator::Sin(sin)),
                    Obj::TrigOperator(TrigOperator::Cos(cos)),
                ) = (&*div.left, &*div.right)
                {
                    if tan.arg.ir() == sin.arg.ir() && tan.arg.ir() == cos.arg.ir() {
                        return Some(EqualitySearchProofByBuiltinRule::TanQuotientDefinition(
                            TanQuotientDefinitionProof::new(),
                        ));
                    }
                }
            }
            (
                Obj::TrigOperator(TrigOperator::Cot(cot)),
                Obj::ArithmeticOperator(ArithmeticOperator::Div(div)),
            ) => {
                if let (
                    Obj::TrigOperator(TrigOperator::Cos(cos)),
                    Obj::TrigOperator(TrigOperator::Sin(sin)),
                ) = (&*div.left, &*div.right)
                {
                    if cot.arg.ir() == cos.arg.ir() && cot.arg.ir() == sin.arg.ir() {
                        return Some(EqualitySearchProofByBuiltinRule::CotQuotientDefinition(
                            CotQuotientDefinitionProof::new(),
                        ));
                    }
                }
            }
            (
                Obj::IntegerOperator(IntegerOperator::Gcd(gcd)),
                Obj::IntegerOperator(IntegerOperator::Gcd(step)),
            ) => {
                if let Obj::IntegerOperator(IntegerOperator::Mod(rem)) = &*step.right {
                    if step.left.ir() == gcd.right.ir()
                        && rem.left.ir() == gcd.left.ir()
                        && rem.right.ir() == gcd.right.ir()
                    {
                        return Some(EqualitySearchProofByBuiltinRule::GcdEuclideanStep(
                            GcdEuclideanStepProof::new(),
                        ));
                    }
                }
            }
            _ => {}
        }
    }
    None
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/obj_definition_builtins/tests.rs"]
mod obj_definition_builtins_tests;
