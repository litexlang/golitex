use crate::prelude::*;
use crate::rational_expression::evaluate::{
    add_signed_decimal_str, mul_signed_decimal_str, sub_signed_decimal_str,
};
use crate::rational_expression::monomial::MonomialWithNonZeroScalarAndOrderedOperands;

pub fn collect_monomials_in_obj(obj: &Obj) -> Vec<MonomialWithNonZeroScalarAndOrderedOperands> {
    match obj {
        Obj::Number(number) => from_number_obj_to_monomial(number),
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
    if let Some(normalized_calculated_value) =
        Obj::from(sub.clone()).evaluate_to_normalized_decimal_number()
    {
        return from_number_obj_to_monomial(&normalized_calculated_value);
    }

    let left_monomial_collections = collect_monomials_in_obj(&sub.left);
    let right_monomial_collections = collect_monomials_in_obj(&sub.right);

    let mut processed_right_indexes: Vec<usize> =
        Vec::with_capacity(right_monomial_collections.len());
    let mut result: Vec<MonomialWithNonZeroScalarAndOrderedOperands> =
        Vec::with_capacity(left_monomial_collections.len() + right_monomial_collections.len());
    for (_, left_monomial) in left_monomial_collections.iter().enumerate() {
        let mut already_pushed = false;

        for (j, right_monomial) in right_monomial_collections.iter().enumerate() {
            if processed_right_indexes.contains(&j) {
                continue;
            }

            if left_monomial.operands_equal(right_monomial) {
                let new_scalar = sub_signed_decimal_str(
                    &left_monomial.non_zero_scalar,
                    &right_monomial.non_zero_scalar,
                );
                processed_right_indexes.push(j);
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
        if processed_right_indexes.contains(&j) {
            continue;
        }
        let negated_scalar = sub_signed_decimal_str("0", &right_monomial.non_zero_scalar);
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
    if let Some(normalized_calculated_value) =
        Obj::from(add.clone()).evaluate_to_normalized_decimal_number()
    {
        return from_number_obj_to_monomial(&normalized_calculated_value);
    }

    let left_monomial_collections = collect_monomials_in_obj(&add.left);
    let right_monomial_collections = collect_monomials_in_obj(&add.right);

    let mut processed_right_indexes: Vec<usize> =
        Vec::with_capacity(right_monomial_collections.len());
    let mut result: Vec<MonomialWithNonZeroScalarAndOrderedOperands> =
        Vec::with_capacity(left_monomial_collections.len() + right_monomial_collections.len());
    for (_, left_monomial) in left_monomial_collections.iter().enumerate() {
        let mut already_pushed = false;

        for (j, right_monomial) in right_monomial_collections.iter().enumerate() {
            if processed_right_indexes.contains(&j) {
                continue;
            }

            if left_monomial.operands_equal(right_monomial) {
                let new_scalar = add_signed_decimal_str(
                    &left_monomial.non_zero_scalar,
                    &right_monomial.non_zero_scalar,
                );
                processed_right_indexes.push(j);
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
        if processed_right_indexes.contains(&j) {
            continue;
        }
        result.push(right_monomial.clone());
    }

    result
}

fn collect_monomials_in_mul(mul: &Mul) -> Vec<MonomialWithNonZeroScalarAndOrderedOperands> {
    if let Some(normalized_calculated_value) =
        Obj::from(mul.clone()).evaluate_to_normalized_decimal_number()
    {
        return from_number_obj_to_monomial(&normalized_calculated_value);
    }

    if let Some(normalized_calculated_value) = &mul.left.evaluate_to_normalized_decimal_number() {
        let left = normalized_calculated_value.normalized_value.clone();
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

    if let Some(normalized_calculated_value) = &mul.right.evaluate_to_normalized_decimal_number() {
        let right = normalized_calculated_value.normalized_value.clone();
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
                current_scalar = add_signed_decimal_str(
                    current_scalar.as_str(),
                    current_right_monomial.non_zero_scalar.as_str(),
                );
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
    if let Some(normalized_calculated_value) =
        Obj::from(pow.clone()).evaluate_to_normalized_decimal_number()
    {
        return from_number_obj_to_monomial(&normalized_calculated_value);
    }

    // 判断 exponent 字面量是否为 0 或正整数，返回 (是否 ok, 解析出的数字)
    let (exponent_ok, exponent_value) = if let Obj::Number(num) = &*pow.exponent {
        if is_number_string_literally_integer_without_dot(num.normalized_value.clone())
            && !num.normalized_value.starts_with('-')
        {
            if let Ok(n) = num.normalized_value.parse::<i64>() {
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
        Some(vec![(Obj::from(pow.clone()), pow.to_string())]),
    ) {
        vec![m]
    } else {
        vec![]
    }
}

fn multiply_numbers_to_monomial(
    left: &str,
    right: &MonomialWithNonZeroScalarAndOrderedOperands,
) -> Option<MonomialWithNonZeroScalarAndOrderedOperands> {
    let scalar = mul_signed_decimal_str(left, right.non_zero_scalar.as_str());
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
    let new_scalar = mul_signed_decimal_str(&left.non_zero_scalar, &right.non_zero_scalar);
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

fn from_number_obj_to_monomial(
    number: &Number,
) -> Vec<MonomialWithNonZeroScalarAndOrderedOperands> {
    let number_string = number.normalized_value.clone();
    // must be calculated so that it is normalized
    let current_monomial =
        MonomialWithNonZeroScalarAndOrderedOperands::new_and_check_scalar_is_not_zero(
            number_string,
            None,
        );
    if let Some(current_monomial) = current_monomial {
        vec![current_monomial]
    } else {
        vec![]
    }
}
