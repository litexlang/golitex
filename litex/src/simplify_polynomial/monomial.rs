// use crate::obj::Obj;
// use crate::common::keywords::{LEFT_BRACE, MUL, RIGHT_BRACE};

// pub struct Monomial {
//     pub non_zero_scalar: String, // -1, 1, -15.12 etc.
//     pub operand: Option<Vec<String>>,
// }

// impl Monomial {
//     pub fn new(scalar: String, operand: Option<Vec<String>>) -> Self {
//         Monomial {
//             non_zero_scalar: scalar,
//             operand,
//         }
//     }

//     pub fn operands_equal(&self, other: &Monomial) -> bool {
//         match (&self.operand, &other.operand) {
//             (Some(ref self_operands), Some(ref other_operands)) => {
//                 if self_operands.len() != other_operands.len() {
//                     return false;
//                 }
//                 for (self_operand, other_operand) in self_operands.iter().zip(other_operands.iter()) {
//                     if self_operand.to_string() != other_operand.to_string() {
//                         return false;
//                     }
//                 }
//                 true
//             }
//             (None, None) => true,
//             (None, Some(_)) => false,
//             (Some(_), None) => false,
//         }
//     }

//     pub fn sorted_multiply_operands_string(operands: &Vec<String>) -> String {
//         let mut result = vec![];
//         for operand in operands {
//             result.push(format!("{}{}{}", LEFT_BRACE, operand, RIGHT_BRACE));
//         }
//         result.sort();
//         result.join(MUL)
//     }
// }
