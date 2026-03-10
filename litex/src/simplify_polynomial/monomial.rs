use crate::obj::Obj;

#[derive(Clone)]
pub struct MonomialWithNonZeroScalarAndOrderedOperands {
    pub non_zero_scalar: String, // -1, 1, -15.12 etc.
    pub ordered_operands: Option<Vec<(Obj, String)>>,
}

impl MonomialWithNonZeroScalarAndOrderedOperands {
    /// 按情况讨论：scalar 为空/全空白、或规范化后为 0 则返回 None；否则返回 Some(Monomial)，且 scalar 存规范化后的值。
    pub fn new_and_check_scalar_is_not_zero(scalar: String, ordered_operands: Option<Vec<(Obj, String)>>) -> Option<Self> {
        if scalar == "0" {
            return None;
        }
        Some(MonomialWithNonZeroScalarAndOrderedOperands {
            non_zero_scalar: scalar,
            ordered_operands,
        })
    }

    pub fn operands_equal(&self, other: &MonomialWithNonZeroScalarAndOrderedOperands) -> bool {
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

}
