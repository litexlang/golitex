//! Fixed quotient identities; enclosing equality WD owns every partial domain.
use super::by_trig_complex_identities::TrigComplexIdentityProof;
use crate::ast::obj::{ArithmeticOperator as A, Literal, Number, Obj, TrigOperator as T};
use crate::rational_expression::objs_equal_by_rational_expression_evaluation;

pub struct TanCotProductBuiltinRuleProof {
    pub angle: Obj,
}
impl TanCotProductBuiltinRuleProof {
    pub fn new(angle: Obj) -> Self {
        Self { angle }
    }
}
pub struct TanSquareReciprocalCosineBuiltinRuleProof {
    pub angle: Obj,
}
impl TanSquareReciprocalCosineBuiltinRuleProof {
    pub fn new(angle: Obj) -> Self {
        Self { angle }
    }
}

// tan(x)cot(x)=1 and 1+tan(x)^2=1/cos(x)^2 follow from the checked
// quotient definitions and sin(x)^2+cos(x)^2=1. Parent WD must retain real
// arguments and every sin/cos nonzero proof; this matcher searches no premise.
pub(super) fn trig_quotient_relation(left: &Obj, right: &Obj) -> Option<TrigComplexIdentityProof> {
    if number_matches(right, "1") {
        if let Obj::ArithmeticOperator(A::Mul(product)) = left {
            for (tan, cot) in [
                (&*product.left, &*product.right),
                (&*product.right, &*product.left),
            ] {
                if let (Obj::TrigOperator(T::Tan(tan)), Obj::TrigOperator(T::Cot(cot))) = (tan, cot)
                {
                    if tan.arg.ir() == cot.arg.ir() {
                        return Some(TrigComplexIdentityProof::TanCotProduct(
                            TanCotProductBuiltinRuleProof::new(tan.arg.as_ref().clone()),
                        ));
                    }
                }
            }
        }
    }
    let Obj::ArithmeticOperator(A::Add(add)) = left else {
        return None;
    };
    let Obj::ArithmeticOperator(A::Div(div)) = right else {
        return None;
    };
    if !number_matches(&div.left, "1") {
        return None;
    }
    let cosine = square_base(&div.right)?;
    let Obj::TrigOperator(T::Cos(cosine)) = cosine else {
        return None;
    };
    for (unit, square) in [(&*add.left, &*add.right), (&*add.right, &*add.left)] {
        if !number_matches(unit, "1") {
            continue;
        }
        let Some(tangent) = square_base(square) else {
            continue;
        };
        let Obj::TrigOperator(T::Tan(tangent)) = tangent else {
            continue;
        };
        if tangent.arg.ir() == cosine.arg.ir() {
            return Some(TrigComplexIdentityProof::TanSquareReciprocalCosine(
                TanSquareReciprocalCosineBuiltinRuleProof::new(tangent.arg.as_ref().clone()),
            ));
        }
    }
    None
}

fn square_base(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::ArithmeticOperator(A::Pow(pow)) if number_matches(&pow.exponent, "2") => {
            Some(&pow.base)
        }
        Obj::ArithmeticOperator(A::Mul(mul)) if mul.left.ir() == mul.right.ir() => Some(&mul.left),
        _ => None,
    }
}
fn number_matches(obj: &Obj, value: &str) -> bool {
    objs_equal_by_rational_expression_evaluation(
        obj,
        &Obj::Literal(Literal::Number(Number {
            normalized_value: value.to_string(),
        })),
    )
}
