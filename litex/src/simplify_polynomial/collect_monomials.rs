use crate::common::helper::is_number_string_literally_integer_without_dot;
use crate::obj::{Add, Mul, Obj, Pow};
use crate::simplify_polynomial::calculate::{mul_decimal_str, pow_decimal_str, sub_decimal_str};
use crate::simplify_polynomial::monomial::sort_monomials_by_operands;
use super::calculate::add_decimal_str;
use super::monomial::Monomial;
use super::calculate::normalize_decimal_result;

pub fn collect_ordered_monomials(obj: &Obj) -> Vec<Monomial> {
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
        Obj::Add(add) => {
            collect_ordered_monomial_in_add(add)
        },
        Obj::Mul(mul) => {
            collect_ordered_monomial_in_mul(mul)
        },
        Obj::Pow(pow) => {
            collect_ordered_monomial_in_pow(pow)
        },
        _ => vec![],
    }
}

pub fn collect_ordered_monomial_in_sub(add: &Add) -> Vec<Monomial> {
    if add.can_be_calculated {
        let left = add.left.calculate_to_string();
        let right = add.right.calculate_to_string();
        return vec![sub_numbers_and_return_monomial(&left, &right)]
    }

    let left_monomial_collections = collect_ordered_monomials(&add.left);
    let right_monomial_collections = collect_ordered_monomials(&add.right);

    let mut already_processed_indexes: Vec<usize> = vec![];
    let mut result: Vec<Monomial> = vec![];
    for (i, left_monomial) in left_monomial_collections.iter().enumerate() {
        if already_processed_indexes.contains(&i) {
            continue;
        }

        let mut already_pushed = false;
        
        for (j, right_monomial) in right_monomial_collections.iter().enumerate() {
            if already_processed_indexes.contains(&j) {
                continue;
            }

            if left_monomial.operands_equal(right_monomial) {
                let new_scalar = sub_decimal_str(&left_monomial.non_zero_scalar, &right_monomial.non_zero_scalar);
                already_processed_indexes.push(j);
                result.push(Monomial::new(new_scalar, left_monomial.ordered_operands.clone()));
                already_pushed = true
                break;
            }
        }

        if !already_pushed {
            result.push(left_monomial.clone());
        }
    }

    sort_monomials_by_operands(&mut result);
    result
}


pub fn collect_ordered_monomial_in_add(add: &Add) -> Vec<Monomial> {
    if add.can_be_calculated {
        let left = add.left.calculate_to_string();
        let right = add.right.calculate_to_string();
        return vec![add_numbers_and_return_monomial(&left, &right)]
    }

    let left_monomial_collections = collect_ordered_monomials(&add.left);
    let right_monomial_collections = collect_ordered_monomials(&add.right);

    let mut already_processed_indexes: Vec<usize> = vec![];
    let mut result: Vec<Monomial> = vec![];
    for (i, left_monomial) in left_monomial_collections.iter().enumerate() {
        if already_processed_indexes.contains(&i) {
            continue;
        }

        let mut already_pushed = false;
        
        for (j, right_monomial) in right_monomial_collections.iter().enumerate() {
            if already_processed_indexes.contains(&j) {
                continue;
            }

            if left_monomial.operands_equal(right_monomial) {
                let new_scalar = add_decimal_str(&left_monomial.non_zero_scalar, &right_monomial.non_zero_scalar);
                already_processed_indexes.push(j);
                result.push(Monomial::new(new_scalar, left_monomial.ordered_operands.clone()));
                already_pushed = true;
                break;
            }
        }

        if !already_pushed {
            result.push(left_monomial.clone())
        }
    }

    sort_monomials_by_operands(&mut result);
    result
}

fn collect_ordered_monomial_in_mul(mul: &Mul) -> Vec<Monomial> {
    if mul.can_be_calculated {
        let left = mul.left.calculate_to_string();
        let right = mul.right.calculate_to_string();
        return vec![multiply_numbers_and_return_monomial(&left, &right)]
    }

    if mul.left.can_be_calculated() {
        let left = mul.left.calculate_to_string();
        let collected_monomials_of_right = collect_ordered_monomials(&mul.right);
        let mut result = vec![];
        for right in collected_monomials_of_right.iter() {
            result.push(multiply_numbers_to_monomial(left.as_str(), right));
        }
        return result
    }

    if mul.right.can_be_calculated() {
        let right = mul.right.calculate_to_string();
        let collected_monomials_of_left = collect_ordered_monomials(&mul.left);
        let mut result = vec![];
        for left in collected_monomials_of_left.iter() {
            result.push(multiply_numbers_to_monomial(right.as_str(), left));
        }
        return result
    }

    let collections_of_left = collect_ordered_monomials(&mul.left);
    let collections_of_right = collect_ordered_monomials(&mul.right);
    
    collect_ordered_monomials_of_mul_of_ordered_monomial_vec(&collections_of_left, &collections_of_right)
}

fn collect_ordered_monomials_of_mul_of_ordered_monomial_vec(collections_of_left: &Vec<Monomial>, collections_of_right: &Vec<Monomial>) -> Vec<Monomial> {
    let mut collect_monomials_after_mul: Vec<Monomial> = vec![];
    for left in collections_of_left.iter() {
        for right in collections_of_right.iter() {
            let multiplied = multiply_two_monomials_with_operands(left, right);
            collect_monomials_after_mul.push(multiplied);
        }
    }

    let mut already_processed_indexes: Vec<usize> = vec![];
    let mut result: Vec<Monomial> = vec![];
    for (i, monomial) in collect_monomials_after_mul.iter().enumerate() {
        if already_processed_indexes.contains(&i) {
            continue;
        }

        let mut current_scalar = monomial.non_zero_scalar.clone();

        for j in (i + 1)..collect_monomials_after_mul.len() {
            let current_right_monomial = &collect_monomials_after_mul[j];
            if monomial.operands_equal(current_right_monomial) {
                current_scalar = add_decimal_str(&current_scalar, &current_right_monomial.non_zero_scalar);
                already_processed_indexes.push(j);
            }
        }

        result.push(Monomial::new(current_scalar, monomial.ordered_operands.clone()));
    }

    sort_monomials_by_operands(&mut result);
    result
}

fn collect_ordered_monomial_in_pow(pow: &Pow) -> Vec<Monomial> {
    if pow.can_be_calculated {
        let left = pow.base.calculate_to_string();
        let right = pow.exponent.calculate_to_string();
        let value = pow_decimal_str(&left, &right);
        return vec![Monomial::new(value, None)]
    }

    // 判断 exponent 字面量是否为 0 或正整数，返回 (是否 ok, 解析出的数字)
    let (exponent_ok, exponent_value) = if let Obj::Number(num) = &*pow.exponent {
        if is_number_string_literally_integer_without_dot(&num.value)
            && !num.value.starts_with('-')
        {
            if let Ok(n) = num.value.parse::<i64>() {
                if n >= 0 {
                    (true, Some(n))
                } else {
                    (false, None)
                }
            } else {
                (false, None)
            }
        } else {
            (false, None)
        }
    } else {
        (false, None)
    };

    if !exponent_ok || exponent_value.unwrap() > 32 {
        return vec![Monomial::new("1".to_string(), Some(vec![(Obj::Pow(pow.clone()), pow.to_string())]))];
    }

    if exponent_value == Some(0) {
        return vec![Monomial::new("1".to_string(), None)]
    }

    let n = exponent_value.unwrap();
    let base_monomials = collect_ordered_monomials(&pow.base);
    let mut result = base_monomials.clone();
    for _ in 0..(n - 1) {
        result = collect_ordered_monomials_of_mul_of_ordered_monomial_vec(&result, &base_monomials);
    }

    sort_monomials_by_operands(&mut result);
    result
}

fn multiply_numbers_and_return_monomial(left: &str, right: &str) -> Monomial {
    let scalar = mul_decimal_str(left, right);
    Monomial::new(scalar, None)
}

fn add_numbers_and_return_monomial(left: &str, right: &str) -> Monomial {
    let scalar = add_decimal_str(left, right);
    Monomial::new(scalar, None)
}


fn multiply_numbers_to_monomial(left: &str, right: &Monomial) -> Monomial {
    let scalar = mul_decimal_str(left, right.non_zero_scalar.as_str());
    Monomial::new(scalar, right.ordered_operands.clone())
}

fn multiply_two_monomials_with_operands(left: &Monomial, right: &Monomial) -> Monomial {
    let mut new_operands = vec![];
    let new_scalar = mul_decimal_str(&left.non_zero_scalar, &right.non_zero_scalar);
    for operand in (left.ordered_operands.as_ref()).unwrap().iter() {
        let obj = operand.0.clone();
        let obj_string = operand.1.clone();
        new_operands.push((obj, obj_string));
    }
    for operand in right.ordered_operands.as_ref().unwrap().iter() {
        let obj = operand.0.clone();
        let obj_string = operand.1.clone();
        new_operands.push((obj, obj_string));
    }
    new_operands.sort_by(|a, b| a.1.cmp(&b.1));

    Monomial::new(new_scalar, Some(new_operands))
}

fn sub_numbers_and_return_monomial(left: &str, right: &str) -> Monomial {
    let scalar = sub_decimal_str(left, right);
    Monomial::new(scalar, None)
}