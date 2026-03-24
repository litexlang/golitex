use super::calculate::add_decimal_str;
use super::monomial::MonomialWithNonZeroScalarAndOrderedOperands;
use crate::calculate_and_simplify_rational_expression::calculate::{
    mul_decimal_str, pow_decimal_str, sub_decimal_str,
};
use crate::common::helper::is_number_string_literally_integer_without_dot;
use crate::obj::{Add, Mul, Obj, Pow, Sub};

pub fn collect_monomials_in_obj(obj: &Obj) -> Vec<MonomialWithNonZeroScalarAndOrderedOperands> {
    match obj {
        Obj::Number(_) => {
            // must be calculated so that it is normalized
            let num_str = obj.calculate_to_string_panic_when_cannot_be_calculated();
            let current_monomial =
                MonomialWithNonZeroScalarAndOrderedOperands::new_and_check_scalar_is_not_zero(
                    num_str, None,
                );
            if let Some(current_monomial) = current_monomial {
                vec![current_monomial]
            } else {
                vec![]
            }
        }
        Obj::Add(add) => collect_monomials_in_add(add),
        Obj::Mul(mul) => collect_monomials_in_mul(mul),
        Obj::Pow(pow) => collect_monomials_in_pow(pow),
        Obj::Sub(sub) => collect_monomials_in_sub(sub),
        obj => {
            if let Some(m) =
                MonomialWithNonZeroScalarAndOrderedOperands::new_and_check_scalar_is_not_zero(
                    "1".to_string(),
                    Some(vec![(obj.clone(), obj.to_string())]),
                )
            {
                vec![m]
            } else {
                unreachable!();
            }
        }
    }
}

pub fn collect_monomials_in_sub(sub: &Sub) -> Vec<MonomialWithNonZeroScalarAndOrderedOperands> {
    if sub.calculated_value.is_some() {
        let left = sub.left.calculate_to_string_panic_when_cannot_be_calculated();
        let right = sub.right.calculate_to_string_panic_when_cannot_be_calculated();
        let current_monomial = sub_numbers_and_return_monomial(&left, &right);
        if let Some(current_monomial) = current_monomial {
            return vec![current_monomial];
        }
        return vec![];
    }

    let left_monomial_collections = collect_monomials_in_obj(&sub.left);
    let right_monomial_collections = collect_monomials_in_obj(&sub.right);

    let mut already_processed_indexes: Vec<usize> = Vec::with_capacity(
        left_monomial_collections.len() + right_monomial_collections.len(),
    );
    let mut result: Vec<MonomialWithNonZeroScalarAndOrderedOperands> = Vec::with_capacity(
        left_monomial_collections.len() + right_monomial_collections.len(),
    );
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
                let new_scalar = sub_decimal_str(
                    &left_monomial.non_zero_scalar,
                    &right_monomial.non_zero_scalar,
                );
                already_processed_indexes.push(j);
                let current_monomial =
                    MonomialWithNonZeroScalarAndOrderedOperands::new_and_check_scalar_is_not_zero(
                        new_scalar,
                        left_monomial.ordered_operands.clone(),
                    );
                if let Some(m) = current_monomial {
                    result.push(m);
                }
                already_pushed = true;
                break;
            }
        }

        if !already_pushed {
            result.push(left_monomial.clone());
        }
    }

    for (j, right_monomial) in right_monomial_collections.iter().enumerate() {
        if already_processed_indexes.contains(&j) {
            continue;
        }
        let negated_scalar = sub_decimal_str("0", &right_monomial.non_zero_scalar);
        if let Some(m) =
            MonomialWithNonZeroScalarAndOrderedOperands::new_and_check_scalar_is_not_zero(
                negated_scalar,
                right_monomial.ordered_operands.clone(),
            )
        {
            result.push(m);
        }
    }

    result
}

pub fn collect_monomials_in_add(add: &Add) -> Vec<MonomialWithNonZeroScalarAndOrderedOperands> {
    if add.calculated_value.is_some() {
        let left = add.left.calculate_to_string_panic_when_cannot_be_calculated();
        let right = add.right.calculate_to_string_panic_when_cannot_be_calculated();
        let current_monomial = add_numbers_and_return_monomial(&left, &right);
        return if let Some(current_monomial) = current_monomial {
            vec![current_monomial]
        } else {
            vec![]
        };
    }

    let left_monomial_collections = collect_monomials_in_obj(&add.left);
    let right_monomial_collections = collect_monomials_in_obj(&add.right);

    let mut already_processed_indexes: Vec<usize> = Vec::with_capacity(
        left_monomial_collections.len() + right_monomial_collections.len(),
    );
    let mut result: Vec<MonomialWithNonZeroScalarAndOrderedOperands> = Vec::with_capacity(
        left_monomial_collections.len() + right_monomial_collections.len(),
    );
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
                let new_scalar = add_decimal_str(
                    &left_monomial.non_zero_scalar,
                    &right_monomial.non_zero_scalar,
                );
                already_processed_indexes.push(j);
                let current_monomial =
                    MonomialWithNonZeroScalarAndOrderedOperands::new_and_check_scalar_is_not_zero(
                        new_scalar,
                        left_monomial.ordered_operands.clone(),
                    );
                if let Some(m) = current_monomial {
                    result.push(m);
                }
                already_pushed = true;
                break;
            }
        }

        if !already_pushed {
            result.push(left_monomial.clone())
        }
    }

    for (j, right_monomial) in right_monomial_collections.iter().enumerate() {
        if already_processed_indexes.contains(&j) {
            continue;
        }
        result.push(right_monomial.clone());
    }

    result
}

fn collect_monomials_in_mul(mul: &Mul) -> Vec<MonomialWithNonZeroScalarAndOrderedOperands> {
    if mul.calculated_value.is_some() {
        let left = mul.left.calculate_to_string_panic_when_cannot_be_calculated();
        let right = mul.right.calculate_to_string_panic_when_cannot_be_calculated();
        let current_monomial = multiply_numbers_and_return_monomial(&left, &right);
        return if let Some(current_monomial) = current_monomial {
            vec![current_monomial]
        } else {
            vec![]
        };
    }

    if mul.left.calculated_value().is_some() {
        let left = mul.left.calculate_to_string_panic_when_cannot_be_calculated();
        let collected_monomials_of_right = collect_monomials_in_obj(&mul.right);
        let mut result: Vec<MonomialWithNonZeroScalarAndOrderedOperands> =
            Vec::with_capacity(collected_monomials_of_right.len());
        for right in collected_monomials_of_right.iter() {
            let current_monomial = multiply_numbers_to_monomial(left.as_str(), right);
            if let Some(m) = current_monomial {
                result.push(m);
            }
        }
        return result;
    }

    if mul.right.calculated_value().is_some() {
        let right = mul.right.calculate_to_string_panic_when_cannot_be_calculated();
        let collected_monomials_of_left = collect_monomials_in_obj(&mul.left);
        let mut result: Vec<MonomialWithNonZeroScalarAndOrderedOperands> =
            Vec::with_capacity(collected_monomials_of_left.len());
        for left in collected_monomials_of_left.iter() {
            let current_monomial = multiply_numbers_to_monomial(right.as_str(), left);
            if let Some(m) = current_monomial {
                result.push(m);
            }
        }
        return result;
    }

    let collections_of_left = collect_monomials_in_obj(&mul.left);
    let collections_of_right = collect_monomials_in_obj(&mul.right);

    collect_monomials_of_mul_of_monomial_vec(collections_of_left, collections_of_right)
}

fn collect_monomials_of_mul_of_monomial_vec(
    collections_of_left: Vec<MonomialWithNonZeroScalarAndOrderedOperands>,
    collections_of_right: Vec<MonomialWithNonZeroScalarAndOrderedOperands>,
) -> Vec<MonomialWithNonZeroScalarAndOrderedOperands> {
    let mut collect_monomials_after_mul: Vec<MonomialWithNonZeroScalarAndOrderedOperands> =
        Vec::with_capacity(collections_of_left.len() * collections_of_right.len());
    for left in collections_of_left.iter() {
        for right in collections_of_right.iter() {
            let multiplied = multiply_two_non_zero_monomials_with_operands(left, right);
            collect_monomials_after_mul.push(multiplied);
        }
    }

    let mut already_processed_indexes: Vec<usize> =
        Vec::with_capacity(collect_monomials_after_mul.len());
    let mut result: Vec<MonomialWithNonZeroScalarAndOrderedOperands> =
        Vec::with_capacity(collect_monomials_after_mul.len());
    for (i, monomial) in collect_monomials_after_mul.iter().enumerate() {
        if already_processed_indexes.contains(&i) {
            continue;
        }

        let mut current_scalar = monomial.non_zero_scalar.clone();

        for j in (i + 1)..collect_monomials_after_mul.len() {
            let current_right_monomial = &collect_monomials_after_mul[j];
            if monomial.operands_equal(current_right_monomial) {
                current_scalar =
                    add_decimal_str(&current_scalar, &current_right_monomial.non_zero_scalar);
                already_processed_indexes.push(j);
            }
        }

        let current_monomial =
            MonomialWithNonZeroScalarAndOrderedOperands::new_and_check_scalar_is_not_zero(
                current_scalar,
                monomial.ordered_operands.clone(),
            );
        if let Some(m) = current_monomial {
            result.push(m);
        }
    }

    result
}

fn collect_monomials_in_pow(pow: &Pow) -> Vec<MonomialWithNonZeroScalarAndOrderedOperands> {
    if pow.calculated_value.is_some() {
        let left = pow.base.calculate_to_string_panic_when_cannot_be_calculated();
        let right = pow.exponent.calculate_to_string_panic_when_cannot_be_calculated();
        let value = pow_decimal_str(&left, &right);
        let current_monomial =
            MonomialWithNonZeroScalarAndOrderedOperands::new_and_check_scalar_is_not_zero(
                value, None,
            );
        if let Some(m) = current_monomial {
            return vec![m];
        }
        return vec![];
    }

    // 判断 exponent 字面量是否为 0 或正整数，返回 (是否 ok, 解析出的数字)
    let (exponent_ok, exponent_value) = if let Obj::Number(num) = &*pow.exponent {
        if is_number_string_literally_integer_without_dot(num.value.clone())
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

    if !exponent_ok {
        return default_pow_fallback(pow);
    }
    let n = match exponent_value {
        Some(0) => {
            if let Some(m) =
                MonomialWithNonZeroScalarAndOrderedOperands::new_and_check_scalar_is_not_zero(
                    "1".to_string(),
                    None,
                )
            {
                return vec![m];
            }
            return vec![];
        }
        Some(n) if n > 32 => return default_pow_fallback(pow),
        Some(n) => n,
        None => return default_pow_fallback(pow),
    };
    let base_monomials = collect_monomials_in_obj(&pow.base);
    let mut result = base_monomials.clone();
    for _ in 0..(n - 1) {
        result = collect_monomials_of_mul_of_monomial_vec(result, base_monomials.clone());
    }

    result
}

fn default_pow_fallback(pow: &Pow) -> Vec<MonomialWithNonZeroScalarAndOrderedOperands> {
    if let Some(m) = MonomialWithNonZeroScalarAndOrderedOperands::new_and_check_scalar_is_not_zero(
        "1".to_string(),
        Some(vec![(Obj::Pow(pow.clone()), pow.to_string())]),
    ) {
        vec![m]
    } else {
        vec![]
    }
}

fn multiply_numbers_and_return_monomial(
    left: &str,
    right: &str,
) -> Option<MonomialWithNonZeroScalarAndOrderedOperands> {
    let scalar = mul_decimal_str(left, right);
    MonomialWithNonZeroScalarAndOrderedOperands::new_and_check_scalar_is_not_zero(scalar, None)
}

fn add_numbers_and_return_monomial(
    left: &str,
    right: &str,
) -> Option<MonomialWithNonZeroScalarAndOrderedOperands> {
    let scalar = add_decimal_str(left, right);
    MonomialWithNonZeroScalarAndOrderedOperands::new_and_check_scalar_is_not_zero(scalar, None)
}

fn multiply_numbers_to_monomial(
    left: &str,
    right: &MonomialWithNonZeroScalarAndOrderedOperands,
) -> Option<MonomialWithNonZeroScalarAndOrderedOperands> {
    let scalar = mul_decimal_str(left, right.non_zero_scalar.as_str());
    MonomialWithNonZeroScalarAndOrderedOperands::new_and_check_scalar_is_not_zero(
        scalar,
        right.ordered_operands.clone(),
    )
}

fn multiply_two_non_zero_monomials_with_operands(
    left: &MonomialWithNonZeroScalarAndOrderedOperands,
    right: &MonomialWithNonZeroScalarAndOrderedOperands,
) -> MonomialWithNonZeroScalarAndOrderedOperands {
    let left_operand_count = left
        .ordered_operands
        .as_ref()
        .map_or(0, |ordered_operands| ordered_operands.len());
    let right_operand_count = right
        .ordered_operands
        .as_ref()
        .map_or(0, |ordered_operands| ordered_operands.len());
    let mut new_operands = Vec::with_capacity(left_operand_count + right_operand_count);
    let new_scalar = mul_decimal_str(&left.non_zero_scalar, &right.non_zero_scalar);
    if let Some(operands) = left.ordered_operands.as_ref() {
        for operand in operands.iter() {
            let obj = operand.0.clone();
            let obj_string = operand.1.clone();
            new_operands.push((obj, obj_string));
        }
    }
    if let Some(operands) = right.ordered_operands.as_ref() {
        for operand in operands.iter() {
            let obj = operand.0.clone();
            let obj_string = operand.1.clone();
            new_operands.push((obj, obj_string));
        }
    }
    new_operands.sort_by(|a, b| a.1.cmp(&b.1));

    MonomialWithNonZeroScalarAndOrderedOperands::new(new_scalar, Some(new_operands))
}

fn sub_numbers_and_return_monomial(
    left: &str,
    right: &str,
) -> Option<MonomialWithNonZeroScalarAndOrderedOperands> {
    let scalar = sub_decimal_str(left, right);
    MonomialWithNonZeroScalarAndOrderedOperands::new_and_check_scalar_is_not_zero(scalar, None)
}
