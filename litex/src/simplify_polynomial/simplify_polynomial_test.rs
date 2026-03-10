// use crate::obj::{Number, Obj};
// use crate::simplify_polynomial::collect_monomials::collect_monomials;

// #[test]
// fn test_simplify_polynomial_number() {
//     let obj = Obj::Number(Number::new("1"));
//     let monomials = collect_monomials(&obj);
//     assert_eq!(monomials.len(), 1);
//     assert_eq!(monomials[0].non_zero_scalar, "1");
//     assert!(monomials[0].operand.is_none());
// }

// #[test]
// fn test_simplify_polynomial_add_two_numbers() {
//     let one = Obj::Number(Number::new("1"));
//     let two = Obj::Number(Number::new("2"));
//     let one_plus_two = Obj::Add(crate::obj::Add::new(one, two, true));
//     let monomials = collect_monomials(&one_plus_two);
//     assert_eq!(monomials.len(), 1);
//     assert_eq!(monomials[0].non_zero_scalar, "3");
//     assert!(monomials[0].operand.is_none());
// }
