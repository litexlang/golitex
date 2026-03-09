use crate::obj::Obj;

pub struct Monomial {
    pub non_zero_scalar: String, // -1, 1, -15.12 etc.
    pub operand: Option<Obj>,
}

impl Monomial {
    pub fn new(scalar: String, operand: Option<Obj>) -> Self {
        Monomial {
            non_zero_scalar: scalar,
            operand,
        }
    }
}
