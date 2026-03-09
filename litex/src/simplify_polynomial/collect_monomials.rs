use crate::obj::{Add, Mul, Obj};
use super::calculate::add_decimal_str;
use super::monomial::Monomial;
use super::calculate::normalize_decimal_result;

pub fn collect_monomials(obj: &Obj) -> Vec<Monomial> {
    match obj {
        // 变成 to_string 后，如果经过 normalize_decimal_result 化简后变成0，那就返回空的；否则返回 Monomial::new(num.value.clone(), None)
        Obj::Number(num) => {
            let num_str = num.value.clone();
            let normalized_num_str = normalize_decimal_result(&num_str);
            if normalized_num_str == "0" {
                vec![]
            } else {
                vec![Monomial::new(normalized_num_str, None)]
            }
        },
        Obj::Add(add) => collect_monomial_in_add(add),
        _ => vec![],
    }
}

pub fn collect_monomial_in_add(add: &Add) -> Vec<Monomial> {
    let left_monomials = collect_monomials(&add.left);
    let right_monomials = collect_monomials(&add.right);

    let mut result = Vec::new();
    let mut right_used = vec![false; right_monomials.len()];

    for left_monomial in left_monomials {
        let mut left_merged = false;
        for (i, right_monomial) in right_monomials.iter().enumerate() {
            if right_used[i] {
                continue;
            }
            match (&left_monomial.operand, &right_monomial.operand) {
                (Some(left_operand), Some(_)) => {
                    if left_monomial.operands_equal(right_monomial) {
                        let new_scalar = add_decimal_str(
                            &left_monomial.non_zero_scalar,
                            &right_monomial.non_zero_scalar,
                        );
                        if new_scalar != "0" {
                            result.push(Monomial::new(
                                new_scalar,
                                Some(left_operand.clone()),
                            ));
                        }
                        right_used[i] = true;
                        left_merged = true;
                        break;
                    }
                }
                (Some(_), None) => {
                    result.push(Monomial::new(
                        left_monomial.non_zero_scalar.clone(),
                        left_monomial.operand.clone(),
                    ));
                    left_merged = true;
                    break;
                }
                (None, Some(_)) => continue,
                (None, None) => {
                    let new_scalar = add_decimal_str(
                        &left_monomial.non_zero_scalar,
                        &right_monomial.non_zero_scalar,
                    );
                    if new_scalar != "0" {
                        result.push(Monomial::new(new_scalar, None));
                    }
                    right_used[i] = true;
                    left_merged = true;
                    break;
                }
            }
        }
        if !left_merged {
            result.push(left_monomial);
        }
    }

    for (i, right_monomial) in right_monomials.into_iter().enumerate() {
        if !right_used[i] {
            result.push(right_monomial);
        }
    }
    result
}

pub fn collect_monomial_in_mul(mul: &Mul) -> Vec<Monomial> {
    // 遍历left，遍历right，让每一位都相乘，放在一个
    panic!("")
    
    // 如果两个都是没有operand，那就相乘

    // 如果一个有，一个没有
}