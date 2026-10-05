//! Principal complex modulus triangle inequalities; whole-fact WD checks carriers.
use super::less_equal::LessEqualFactSearchProofByBuiltinRule;
use crate::ast::fact::LessEqualFact;
use crate::ast::obj::{ArithmeticOperator, ComplexOperator, Obj};

pub struct ComplexTriangleProof {}
pub struct ComplexReverseTriangleProof {}

pub(super) fn search_complex_triangle(fact:&LessEqualFact)
    -> Option<LessEqualFactSearchProofByBuiltinRule> {
    // |z+w|<=|z|+|w| and ||z|-|w||<=|z-w| for complex z,w.
    if let (Some(sum),Obj::ArithmeticOperator(ArithmeticOperator::Add(bound)))=(modulus_arg(&fact.left),&fact.right) {
        if let (Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)),Some(a),Some(b))=(sum,modulus_arg(&bound.left),modulus_arg(&bound.right)) {
            if (sum.left.ir()==a.ir() && sum.right.ir()==b.ir()) || (sum.left.ir()==b.ir() && sum.right.ir()==a.ir()) {
                return Some(LessEqualFactSearchProofByBuiltinRule::ComplexTriangle(ComplexTriangleProof{}));
            }
        }
    }
    if let (Obj::ArithmeticOperator(ArithmeticOperator::Abs(a)),Some(bound))=(&fact.left,modulus_arg(&fact.right)) {
        if let (Obj::ArithmeticOperator(ArithmeticOperator::Sub(diff)),Obj::ArithmeticOperator(ArithmeticOperator::Sub(bound)))=(&*a.arg,bound) {
            if let (Some(z),Some(w))=(modulus_arg(&diff.left),modulus_arg(&diff.right)) {
                if (z.ir()==bound.left.ir() && w.ir()==bound.right.ir()) || (z.ir()==bound.right.ir() && w.ir()==bound.left.ir()) {
                    return Some(LessEqualFactSearchProofByBuiltinRule::ComplexReverseTriangle(ComplexReverseTriangleProof{}));
                }
            }
        }
    }
    None
}

fn modulus_arg(obj:&Obj)->Option<&Obj> {
    match obj {Obj::ComplexOperator(ComplexOperator::ComplexAbs(a))=>Some(&a.arg),_=>None}
}
