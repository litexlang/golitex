// use crate::obj::Obj;

// struct Monomial {
//     scalar: String, // 可能带负号
//     operand: Option<Obj>
// }

// impl Monomial {
//     fn new(scalar: String, operand: Option<Obj>) -> Self {
//         Monomial { scalar, operand }
//     }
// }

// fn collect_monomials(obj: &Obj) -> Vec<Monomial> {
//     match obj {
//         Obj::Number(num) => vec![Monomial::new(num.value.clone(), None)],
//         _ => vec![],
//     }
// }