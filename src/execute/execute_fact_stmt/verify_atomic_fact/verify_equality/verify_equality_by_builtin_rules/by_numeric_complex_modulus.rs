use crate::ast::fact::EqualFact;
use crate::ast::obj::{ComplexOperator, Obj};
use crate::rational_expression::exact_complex::{exact_modulus_radicand, principal_root};
use crate::rational_expression::exact_rational::EvalRational;
use crate::rational_expression::objs_equal_by_rational_expression_evaluation;

pub struct NumericComplexModulusBuiltinRuleProof {
    pub real: Obj,
    pub imaginary: Obj,
    pub squared_modulus: Obj,
    pub value: Obj,
}

impl NumericComplexModulusBuiltinRuleProof {
    fn new(real: Obj, imaginary: Obj, squared_modulus: Obj, value: Obj) -> Self {
        Self { real, imaginary, squared_modulus, value }
    }
}

// Principal modulus: |a+b*i| is nonnegative and its square is a²+b².
// Example: C_abs(-4*i+3)=5; the negative root -5 must never be accepted.
// Whole-equality WD is checked before entering this closed calculation leaf.
pub(super) fn numeric_complex_modulus(fact: &EqualFact) -> Option<NumericComplexModulusBuiltinRuleProof> {
    for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
        let Obj::ComplexOperator(ComplexOperator::ComplexAbs(abs)) = left else { continue; };
        let Some((real, imaginary, squared)) = exact_modulus_radicand(&abs.arg) else { continue; };
        let value = if let Some(candidate) = EvalRational::from_obj(right) {
            if candidate.is_negative() || candidate.mul(&candidate)? != squared { continue; }
            candidate.to_obj()
        } else {
            let value = principal_root(&squared);
            if !objs_equal_by_rational_expression_evaluation(&value, right) { continue; }
            value
        };
        return Some(NumericComplexModulusBuiltinRuleProof::new(real.to_obj(), imaginary.to_obj(), squared.to_obj(), value));
    }
    None
}
