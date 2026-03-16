use crate::obj::{Add, Identifier, Mul, Number, Obj, Pow};
use crate::simplify_polynomial::monomial::MonomialWithNonZeroScalarAndOrderedOperands;
use super::collect_monomials::collect_monomials_in_obj;

fn mk_num(s: String) -> Obj {
    Obj::Number(Number::new(s))
}

fn mk_var(s: String) -> Obj {
    Obj::Identifier(Identifier::new(s))
}

#[test]
fn test_collect_ordered_monomials_number() {
    let obj = mk_num("1".to_string());
    let monomials = collect_monomials_in_obj(&obj);
    assert_eq!(monomials.len(), 1);
    assert_eq!(monomials[0].non_zero_scalar, "1");
    assert!(monomials[0].ordered_operands.is_none());

    let obj = mk_num("0".to_string());
    let monomials = collect_monomials_in_obj(&obj);
    assert_eq!(monomials.len(), 0);
}

#[test]
fn test_collect_ordered_monomials_add_two_numbers() {
    let one = mk_num("1".to_string());
    let two = mk_num("2".to_string());
    let one_plus_two = Obj::Add(Add::new(one, two, true));
    let monomials = collect_monomials_in_obj(&one_plus_two);
    assert_eq!(monomials.len(), 1);
    assert_eq!(monomials[0].non_zero_scalar, "3");
    assert!(monomials[0].ordered_operands.is_none());
}

#[test]
fn test_collect_ordered_monomials_add_number_and_var() {
    let one_plus_x = Obj::Add(Add::new(mk_num("1".to_string()), mk_var("x".to_string()), false));
    let monomials = collect_monomials_in_obj(&one_plus_x);
    assert_eq!(monomials.len(), 2, "1+x => constant 1 and monomial x");
    let sorted = sort_monomials_for_test(monomials);
    assert!(sorted[0].ordered_operands.is_none() || sorted[1].ordered_operands.is_none());
    assert!(sorted.iter().any(|m| m.non_zero_scalar == "1" && m.ordered_operands.is_none()));
    assert!(sorted.iter().any(|m| m.non_zero_scalar == "1" && m.key() == "x"));
}

#[test]
fn test_collect_ordered_monomials_add_like_terms() {
    let x = mk_var("x".to_string());
    let two_x = Obj::Mul(Mul::new(mk_num("2".to_string()), x.clone(), false));
    let three_x = Obj::Mul(Mul::new(mk_num("3".to_string()), x.clone(), false));
    let two_x_plus_three_x = Obj::Add(Add::new(two_x, three_x, false));
    let monomials = collect_monomials_in_obj(&two_x_plus_three_x);
    assert_eq!(monomials.len(), 1, "2x+3x => 5x");
    assert_eq!(monomials[0].non_zero_scalar, "5");
    assert_eq!(monomials[0].key(), "x");
}

#[test]
fn test_collect_ordered_monomials_mul_number_and_var() {
    let two_x = Obj::Mul(Mul::new(mk_num("2".to_string()), mk_var("x".to_string()), false));
    let monomials = collect_monomials_in_obj(&two_x);
    assert_eq!(monomials.len(), 1, "2*x => 2x");
    assert_eq!(monomials[0].non_zero_scalar, "2");
    assert_eq!(monomials[0].key(), "x");
}

#[test]
fn test_collect_ordered_monomials_mul_two_vars() {
    let x = mk_var("x".to_string());
    let y = mk_var("y".to_string());
    let xy = Obj::Mul(Mul::new(x, y, false));
    let monomials = collect_monomials_in_obj(&xy);
    assert_eq!(monomials.len(), 1, "x*y => xy");
    assert_eq!(monomials[0].non_zero_scalar, "1");
    assert_eq!(monomials[0].key(), "x\ny");
}

#[test]
fn test_collect_ordered_monomials_pow_number() {
    let two_sq = Obj::Pow(Pow::new(mk_num("2".to_string()), mk_num("2".to_string()), true));
    let monomials = collect_monomials_in_obj(&two_sq);
    assert_eq!(monomials.len(), 1);
    assert_eq!(monomials[0].non_zero_scalar, "4");
    assert!(monomials[0].ordered_operands.is_none());
}

#[test]
fn test_collect_ordered_monomials_pow_zero() {
    let x = mk_var("x".to_string());
    let x0 = Obj::Pow(Pow::new(x.clone(), mk_num("0".to_string()), false));
    let monomials = collect_monomials_in_obj(&x0);
    assert_eq!(monomials.len(), 1);
    assert_eq!(monomials[0].non_zero_scalar, "1");
    assert!(monomials[0].ordered_operands.is_none());
}

#[test]
fn test_collect_ordered_monomials_pow_one() {
    let x = mk_var("x".to_string());
    let x1 = Obj::Pow(Pow::new(x, mk_num("1".to_string()), false));
    let monomials = collect_monomials_in_obj(&x1);
    assert_eq!(monomials.len(), 1, "x^1 => x");
    assert_eq!(monomials[0].non_zero_scalar, "1");
    assert_eq!(monomials[0].key(), "x");
}

#[test]
fn test_collect_ordered_monomials_non_polynomial_as_single_operand() {
    let list = Obj::ListSet(crate::obj::ListSet::new(vec![mk_num("1".to_string())]));
    let monomials = collect_monomials_in_obj(&list);
    assert_eq!(monomials.len(), 1, "non-polynomial is wrapped as 1*obj by catch-all");
}

/// Sort monomials by canonical key (operand product string) so that comparison is deterministic.
fn sort_monomials_for_test(mut monomials: Vec<MonomialWithNonZeroScalarAndOrderedOperands>) -> Vec<MonomialWithNonZeroScalarAndOrderedOperands> {
    monomials.sort_by(|a, b| a.key().cmp(&b.key()));
    monomials
}

#[test]
fn test_collect_and_sort_a_plus_b() {
    let a = mk_var("a".to_string());
    let b = mk_var("b".to_string());
    let a_plus_b = Obj::Add(Add::new(a, b, false));
    let monomials = collect_monomials_in_obj(&a_plus_b);
    let sorted = sort_monomials_for_test(monomials);
    assert_eq!(sorted.len(), 2, "a+b should be two monomials");
    assert_eq!(sorted[0].non_zero_scalar, "1");
    assert_eq!(sorted[0].key(), "a");
    assert_eq!(sorted[1].non_zero_scalar, "1");
    assert_eq!(sorted[1].key(), "b");
}

#[test]
fn test_collect_and_sort_a_plus_b_squared() {
    let a = mk_var("a".to_string());
    let b = mk_var("b".to_string());
    let a_plus_b = Obj::Add(Add::new(a.clone(), b.clone(), false));
    let a_plus_b_sq = Obj::Pow(Pow::new(a_plus_b, mk_num("2".to_string()), false));
    let monomials = collect_monomials_in_obj(&a_plus_b_sq);
    let sorted = sort_monomials_for_test(monomials);
    assert_eq!(sorted.len(), 3, "(a+b)^2 should be a^2, 2ab, b^2");
    assert_eq!(sorted[0].non_zero_scalar, "1");
    assert_eq!(sorted[0].key(), "a\na");
    assert_eq!(sorted[1].non_zero_scalar, "2");
    assert_eq!(sorted[1].key(), "a\nb");
    assert_eq!(sorted[2].non_zero_scalar, "1");
    assert_eq!(sorted[2].key(), "b\nb");
}

#[test]
fn test_collect_and_sort_a_times_b() {
    let a = mk_var("a".to_string());
    let b = mk_var("b".to_string());
    let a_times_b = Obj::Mul(Mul::new(a, b, false));
    let monomials = collect_monomials_in_obj(&a_times_b);
    let sorted = sort_monomials_for_test(monomials);
    assert_eq!(sorted.len(), 1);
    assert_eq!(sorted[0].non_zero_scalar, "1");
    assert_eq!(sorted[0].key(), "a\nb");
}

#[test]
fn test_collect_and_sort_two_a_plus_three_b() {
    let a = mk_var("a".to_string());
    let b = mk_var("b".to_string());
    let two_a = Obj::Mul(Mul::new(mk_num("2".to_string()), a, false));
    let three_b = Obj::Mul(Mul::new(mk_num("3".to_string()), b, false));
    let expr = Obj::Add(Add::new(two_a, three_b, false));
    let monomials = collect_monomials_in_obj(&expr);
    let sorted = sort_monomials_for_test(monomials);
    assert_eq!(sorted.len(), 2);
    assert_eq!(sorted[0].non_zero_scalar, "2");
    assert_eq!(sorted[0].key(), "a");
    assert_eq!(sorted[1].non_zero_scalar, "3");
    assert_eq!(sorted[1].key(), "b");
}

#[test]
fn test_monomial_operands_equal() {
    let m_none = MonomialWithNonZeroScalarAndOrderedOperands::new_and_check_scalar_is_not_zero("1".to_string(), None);
    let m_none2 = MonomialWithNonZeroScalarAndOrderedOperands::new_and_check_scalar_is_not_zero    ("2".to_string(), None);
    match (m_none, m_none2) {
        (Some(m1), Some(m2)) => assert!(m1.operands_equal(&m2)),
        _ => panic!("m_none and m_none2 should be Some"),
    }

    let op_x = vec![(mk_var("x".to_string()), "x".to_string())];
    let m_x = MonomialWithNonZeroScalarAndOrderedOperands::new_and_check_scalar_is_not_zero("1".to_string(), Some(op_x.clone()));
    let m_x2 = MonomialWithNonZeroScalarAndOrderedOperands::new_and_check_scalar_is_not_zero("2".to_string(), Some(vec![(mk_var("x".to_string()), "x".to_string())]));
    match (m_x, m_x2) {
        (Some(m1), Some(m2)) => assert!(m1.operands_equal(&m2)),
        _ => panic!("m_x and m_x2 should be Some"),
    }

}
