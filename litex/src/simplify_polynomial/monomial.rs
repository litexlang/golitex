use crate::obj::Obj;
use crate::common::keywords::{LEFT_BRACE, MUL, RIGHT_BRACE};

#[derive(Clone)]
pub struct Monomial {
    pub non_zero_scalar: String, // -1, 1, -15.12 etc.
    pub ordered_operands: Option<Vec<(Obj, String)>>,
}

impl Monomial {
    pub fn new(scalar: String, ordered_operands: Option<Vec<(Obj, String)>>) -> Self {
        Monomial {
            non_zero_scalar: scalar,
            ordered_operands,
        }
    }

    pub fn operands_equal(&self, other: &Monomial) -> bool {
        match (&self.ordered_operands, &other.ordered_operands) {
            (Some(ref self_operands), Some(ref other_operands)) => {
                if self_operands.len() != other_operands.len() {
                    return false;
                }
                for (self_operand, other_operand) in self_operands.iter().zip(other_operands.iter()) {
                    if self_operand.1 != other_operand.1 {
                        return false;
                    }
                }
                true
            }
            (None, None) => true,
            (None, Some(_)) => false,
            (Some(_), None) => false,
        }
    }

    fn operands_to_string(&self) -> String {
        match &self.ordered_operands {
            None => String::new(),
            Some(operands) => operands.iter().map(|p| p.1.as_str()).collect::<Vec<_>>().join("\n"),
        }
    }
}

/// 按每个 monomial 的 operands_to_string 对 vec 原地排序。
pub fn sort_monomials_by_operands(monomials: &mut Vec<Monomial>) {
    monomials.sort_by(|a, b| a.operands_to_string().cmp(&b.operands_to_string()));
}
