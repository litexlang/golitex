use crate::prelude::*;

#[derive(Clone)]
pub struct MonomialWithNonZeroScalarAndOrderedOperands {
    pub non_zero_scalar: String, // -1, 1, -15.12 etc.
    pub ordered_operands: Option<Vec<(Obj, String)>>,
}

impl MonomialWithNonZeroScalarAndOrderedOperands {
    pub fn new_and_check_scalar_is_not_zero(
        scalar: String,
        ordered_operands: Option<Vec<(Obj, String)>>,
    ) -> Option<Self> {
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
                for (self_operand, other_operand) in self_operands.iter().zip(other_operands.iter())
                {
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

    pub fn new(scalar: String, ordered_operands: Option<Vec<(Obj, String)>>) -> Self {
        MonomialWithNonZeroScalarAndOrderedOperands {
            non_zero_scalar: scalar,
            ordered_operands,
        }
    }

    pub fn key(&self) -> String {
        match &self.ordered_operands {
            Some(ordered_operands) => {
                return ordered_operands
                    .iter()
                    .map(|(obj, _)| obj.to_string())
                    .collect::<Vec<String>>()
                    .join("\n");
            }
            None => {
                return "".to_string();
            }
        }
    }
}
