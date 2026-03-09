use crate::obj::{Add, Obj};
use super::calculate::add_decimal_str;
use super::monomial::Monomial;

pub fn collect_monomials(obj: &Obj) -> Vec<Monomial> {
    match obj {
        Obj::Number(num) => vec![Monomial::new(num.value.clone(), None)],
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
                (Some(left_operand), Some(right_operand)) => {
                    if left_operand.to_string() == right_operand.to_string() {
                        let new_scalar = add_decimal_str(
                            &left_monomial.non_zero_scalar,
                            &right_monomial.non_zero_scalar,
                        );
                        if new_scalar != "0" && new_scalar != "-0" {
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
                    if new_scalar != "0" && new_scalar != "-0" {
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
