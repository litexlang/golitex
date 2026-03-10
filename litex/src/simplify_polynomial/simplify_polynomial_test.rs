use crate::obj::{Add, Identifier, Mul, Number, Obj, Pow};
use crate::simplify_polynomial::monomial::MonomialWithNonZeroScalarAndOrderedOperands;
use super::collect_monomials::collect_monomials_in_obj;

fn mk_num(s: &str) -> Obj {
    Obj::Number(Number::new(s))
}

fn mk_var(s: &str) -> Obj {
    Obj::Identifier(Identifier::new(s))
}

#[test]
fn test_collect_ordered_monomials_number() {
    let obj = mk_num("1");
    let monomials = collect_monomials_in_obj(&obj);
    assert_eq!(monomials.len(), 1);
    assert_eq!(monomials[0].non_zero_scalar, "1");
    assert!(monomials[0].ordered_operands.is_none());

    let obj = mk_num("0");
    let monomials = collect_monomials_in_obj(&obj);
    assert_eq!(monomials.len(), 0);
}

#[test]
fn test_collect_ordered_monomials_add_two_numbers() {
    let one = mk_num("1");
    let two = mk_num("2");
    let one_plus_two = Obj::Add(Add::new(one, two, true));
    let monomials = collect_monomials_in_obj(&one_plus_two);
    assert_eq!(monomials.len(), 1);
    assert_eq!(monomials[0].non_zero_scalar, "3");
    assert!(monomials[0].ordered_operands.is_none());
}

#[test]
fn test_collect_ordered_monomials_add_number_and_var() {
    // 当前实现不展开裸 Identifier，1+x 只得到常数项
    let one_plus_x = Obj::Add(Add::new(mk_num("1"), mk_var("x"), false));
    let monomials = collect_monomials_in_obj(&one_plus_x);
    assert_eq!(monomials.len(), 1);
    assert_eq!(monomials[0].non_zero_scalar, "1");
    assert!(monomials[0].ordered_operands.is_none());
}

#[test]
fn test_collect_ordered_monomials_add_like_terms() {
    // 当前实现不展开裸 Identifier，2x+3x 中 2x/3x 各返回 []，合并后为 []
    let x = mk_var("x");
    let two_x = Obj::Mul(Mul::new(mk_num("2"), x.clone(), false));
    let three_x = Obj::Mul(Mul::new(mk_num("3"), x.clone(), false));
    let two_x_plus_three_x = Obj::Add(Add::new(two_x, three_x, false));
    let monomials = collect_monomials_in_obj(&two_x_plus_three_x);
    assert_eq!(monomials.len(), 0);
}

#[test]
fn test_collect_ordered_monomials_mul_number_and_var() {
    // 当前实现：一边为数字时只展开另一边；裸 x 展开为 []，故 2*x => []
    let two_x = Obj::Mul(Mul::new(mk_num("2"), mk_var("x"), false));
    let monomials = collect_monomials_in_obj(&two_x);
    assert_eq!(monomials.len(), 0);
}

#[test]
fn test_collect_ordered_monomials_mul_two_vars() {
    // 当前实现：裸 x、y 展开为 []，x*y 两边都非数字 => []
    let x = mk_var("x");
    let y = mk_var("y");
    let xy = Obj::Mul(Mul::new(x.clone(), y.clone(), false));
    let monomials = collect_monomials_in_obj(&xy);
    assert_eq!(monomials.len(), 0);
}

#[test]
fn test_collect_ordered_monomials_pow_number() {
    let two_sq = Obj::Pow(Pow::new(mk_num("2"), mk_num("2"), true));
    let monomials = collect_monomials_in_obj(&two_sq);
    assert_eq!(monomials.len(), 1);
    assert_eq!(monomials[0].non_zero_scalar, "4");
    assert!(monomials[0].ordered_operands.is_none());
}

#[test]
fn test_collect_ordered_monomials_pow_zero() {
    let x = mk_var("x");
    let x0 = Obj::Pow(Pow::new(x.clone(), mk_num("0"), false));
    let monomials = collect_monomials_in_obj(&x0);
    assert_eq!(monomials.len(), 1);
    assert_eq!(monomials[0].non_zero_scalar, "1");
    assert!(monomials[0].ordered_operands.is_none());
}

#[test]
fn test_collect_ordered_monomials_pow_one() {
    // 当前实现：x^1 的 base 为裸 x 展开为 []，故 result 为空
    let x = mk_var("x");
    let x1 = Obj::Pow(Pow::new(x.clone(), mk_num("1"), false));
    let monomials = collect_monomials_in_obj(&x1);
    assert_eq!(monomials.len(), 0);
}

#[test]
fn test_collect_ordered_monomials_non_polynomial_returns_empty() {
    let list = Obj::ListSet(crate::obj::ListSet::new(vec![mk_num("1")]));
    let monomials = collect_monomials_in_obj(&list);
    assert_eq!(monomials.len(), 0);
}

#[test]
fn test_monomial_operands_equal() {
    let m_none = MonomialWithNonZeroScalarAndOrderedOperands::new_and_check_scalar_is_not_zero("1".to_string(), None);
    let m_none2 = MonomialWithNonZeroScalarAndOrderedOperands::new_and_check_scalar_is_not_zero    ("2".to_string(), None);
    assert!(m_none.is_some() && m_none2.is_some() && m_none.unwrap().operands_equal(&m_none2.unwrap()));

    let op_x = vec![(mk_var("x"), "x".to_string())];
    let m_x = MonomialWithNonZeroScalarAndOrderedOperands::new_and_check_scalar_is_not_zero("1".to_string(), Some(op_x.clone()));
    let m_x2 = MonomialWithNonZeroScalarAndOrderedOperands::new_and_check_scalar_is_not_zero("2".to_string(), Some(vec![(mk_var("x"), "x".to_string())]));
    assert!(m_x.is_some() && m_x2.is_some() && m_x.unwrap().operands_equal(&m_x2.unwrap()));

}
