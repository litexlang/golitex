use crate::ast::obj::{Add, ImaginaryUnit, Mul, Number, Obj, Pow, Sub, ArithmeticOperator, Literal};
use crate::rational_expression::decimal_arithmetic::{
    add_signed_decimal_str, evaluate_obj_to_normalized_decimal_number, mul_signed_decimal_str,
    sub_signed_decimal_str,
};
use crate::rational_expression::helper::{
    number_string_is_literal_integer_without_dot, obj_key,
};
use crate::rational_expression::monomial::MonomialWithNonZeroScalarAndOrderedOperands;
use crate::rational_expression::normalization::AlgebraicNormalizationMode;

pub fn collect_monomials_in_obj(
    obj: &Obj,
    mode: AlgebraicNormalizationMode,
) -> Vec<MonomialWithNonZeroScalarAndOrderedOperands> {
    match obj {
        Obj::Literal(Literal::Number(number)) => from_number_obj_to_monomial(number),
        Obj::ArithmeticOperator(ArithmeticOperator::Add(add)) => collect_monomials_in_add(add, mode),
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(mul)) => collect_monomials_in_mul(mul, mode),
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(pow)) => collect_monomials_in_pow(pow, mode),
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)) => collect_monomials_in_sub(sub, mode),
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(neg)) => {
            // Treat unary minus like `0 - arg` for monomial collection.
            collect_monomials_in_sub(
                &Sub {
                    left: Box::new(Obj::Literal(Literal::Number(Number {
                        normalized_value: "0".to_string(),
                    }))),
                    right: neg.arg.clone(),
                },
                mode,
            )
        }
        obj => {
            if let Some(m) =
                MonomialWithNonZeroScalarAndOrderedOperands::new_and_check_scalar_is_not_zero(
                    "1".to_string(),
                    Some(vec![(obj.clone(), obj_key(obj))]),
                )
            {
                vec![m]
            } else {
                unreachable!();
            }
        }
    }
}

fn collect_monomials_in_sub(
    sub: &Sub,
    mode: AlgebraicNormalizationMode,
) -> Vec<MonomialWithNonZeroScalarAndOrderedOperands> {
    if let Some(normalized_calculated_value) =
        evaluate_obj_to_normalized_decimal_number(&Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub.clone())))
    {
        return from_number_obj_to_monomial(&normalized_calculated_value);
    }

    let left_monomial_collections = collect_monomials_in_obj(&sub.left, mode);
    let right_monomial_collections = collect_monomials_in_obj(&sub.right, mode);

    let mut processed_right_indexes: Vec<usize> =
        Vec::with_capacity(right_monomial_collections.len());
    let mut result: Vec<MonomialWithNonZeroScalarAndOrderedOperands> =
        Vec::with_capacity(left_monomial_collections.len() + right_monomial_collections.len());
    for left_monomial in left_monomial_collections.iter() {
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

fn collect_monomials_in_add(
    add: &Add,
    mode: AlgebraicNormalizationMode,
) -> Vec<MonomialWithNonZeroScalarAndOrderedOperands> {
    if let Some(normalized_calculated_value) =
        evaluate_obj_to_normalized_decimal_number(&Obj::ArithmeticOperator(ArithmeticOperator::Add(add.clone())))
    {
        return from_number_obj_to_monomial(&normalized_calculated_value);
    }

    let left_monomial_collections = collect_monomials_in_obj(&add.left, mode);
    let right_monomial_collections = collect_monomials_in_obj(&add.right, mode);

    let mut processed_right_indexes: Vec<usize> =
        Vec::with_capacity(right_monomial_collections.len());
    let mut result: Vec<MonomialWithNonZeroScalarAndOrderedOperands> =
        Vec::with_capacity(left_monomial_collections.len() + right_monomial_collections.len());
    for left_monomial in left_monomial_collections.iter() {
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

fn collect_monomials_in_mul(
    mul: &Mul,
    mode: AlgebraicNormalizationMode,
) -> Vec<MonomialWithNonZeroScalarAndOrderedOperands> {
    if let Some(normalized_calculated_value) =
        evaluate_obj_to_normalized_decimal_number(&Obj::ArithmeticOperator(ArithmeticOperator::Mul(mul.clone())))
    {
        return from_number_obj_to_monomial(&normalized_calculated_value);
    }

    if let Some(normalized_calculated_value) =
        evaluate_obj_to_normalized_decimal_number(&mul.left)
    {
        let left = normalized_calculated_value.normalized_value.clone();
        let collected_monomials_of_right = collect_monomials_in_obj(&mul.right, mode);
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

    if let Some(normalized_calculated_value) =
        evaluate_obj_to_normalized_decimal_number(&mul.right)
    {
        let right = normalized_calculated_value.normalized_value.clone();
        let collected_monomials_of_left = collect_monomials_in_obj(&mul.left, mode);
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

    let collections_of_left = collect_monomials_in_obj(&mul.left, mode);
    let collections_of_right = collect_monomials_in_obj(&mul.right, mode);

    collect_monomials_of_mul_of_monomial_vec(collections_of_left, collections_of_right, mode)
}

fn collect_monomials_of_mul_of_monomial_vec(
    collections_of_left: Vec<MonomialWithNonZeroScalarAndOrderedOperands>,
    collections_of_right: Vec<MonomialWithNonZeroScalarAndOrderedOperands>,
    mode: AlgebraicNormalizationMode,
) -> Vec<MonomialWithNonZeroScalarAndOrderedOperands> {
    let mut collect_monomials_after_mul: Vec<MonomialWithNonZeroScalarAndOrderedOperands> =
        Vec::with_capacity(collections_of_left.len() * collections_of_right.len());
    for left in collections_of_left.iter() {
        for right in collections_of_right.iter() {
            let multiplied = multiply_two_non_zero_monomials_with_operands(left, right, mode);
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

fn collect_monomials_in_pow(
    pow: &Pow,
    mode: AlgebraicNormalizationMode,
) -> Vec<MonomialWithNonZeroScalarAndOrderedOperands> {
    if let Some(normalized_calculated_value) =
        evaluate_obj_to_normalized_decimal_number(&Obj::ArithmeticOperator(ArithmeticOperator::Pow(pow.clone())))
    {
        return from_number_obj_to_monomial(&normalized_calculated_value);
    }

    if mode == AlgebraicNormalizationMode::ComplexImaginaryUnit
        && matches!(pow.base.as_ref(), Obj::Literal(Literal::ImaginaryUnit(_)))
    {
        if let Some(exponent) = evaluate_obj_to_normalized_decimal_number(&pow.exponent) {
            if number_string_is_literal_integer_without_dot(&exponent.normalized_value) {
                if let Ok(exponent) = exponent.normalized_value.parse::<i128>() {
                    return imaginary_unit_integer_power_monomials(exponent);
                }
            }
        }
    }

    let (exponent_ok, exponent_value) = if let Obj::Literal(Literal::Number(num)) = &*pow.exponent {
        if number_string_is_literal_integer_without_dot(&num.normalized_value)
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
    let base_monomials = collect_monomials_in_obj(&pow.base, mode);
    let mut result = base_monomials.clone();
    for _ in 0..(n - 1) {
        result = collect_monomials_of_mul_of_monomial_vec(result, base_monomials.clone(), mode);
    }

    result
}

fn default_pow_fallback(pow: &Pow) -> Vec<MonomialWithNonZeroScalarAndOrderedOperands> {
    let pow_obj = Obj::ArithmeticOperator(ArithmeticOperator::Pow(pow.clone()));
    if let Some(m) = MonomialWithNonZeroScalarAndOrderedOperands::new_and_check_scalar_is_not_zero(
        "1".to_string(),
        Some(vec![(pow_obj.clone(), obj_key(&pow_obj))]),
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
    mode: AlgebraicNormalizationMode,
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
    let mut new_scalar = mul_signed_decimal_str(&left.non_zero_scalar, &right.non_zero_scalar);
    if let Some(operands) = left.ordered_operands.as_ref() {
        for operand in operands.iter() {
            new_operands.push((operand.0.clone(), operand.1.clone()));
        }
    }
    if let Some(operands) = right.ordered_operands.as_ref() {
        for operand in operands.iter() {
            new_operands.push((operand.0.clone(), operand.1.clone()));
        }
    }
    if mode == AlgebraicNormalizationMode::ComplexImaginaryUnit {
        let mut imaginary_unit_count = 0;
        new_operands.retain(|(obj, _)| {
            if matches!(obj, Obj::Literal(Literal::ImaginaryUnit(_))) {
                imaginary_unit_count += 1;
                false
            } else {
                true
            }
        });
        if (imaginary_unit_count / 2) % 2 == 1 {
            new_scalar = mul_signed_decimal_str(&new_scalar, "-1");
        }
        if imaginary_unit_count % 2 == 1 {
            let imaginary_unit = Obj::Literal(Literal::ImaginaryUnit(ImaginaryUnit));
            new_operands.push((imaginary_unit.clone(), obj_key(&imaginary_unit)));
        }
    }
    new_operands.sort_by(|a, b| a.1.cmp(&b.1));

    let ordered_operands = if new_operands.is_empty() {
        None
    } else {
        Some(new_operands)
    };
    MonomialWithNonZeroScalarAndOrderedOperands::new(new_scalar, ordered_operands)
}

fn imaginary_unit_integer_power_monomials(
    exponent: i128,
) -> Vec<MonomialWithNonZeroScalarAndOrderedOperands> {
    let (scalar, include_imaginary_unit) = match exponent.rem_euclid(4) {
        0 => ("1", false),
        1 => ("1", true),
        2 => ("-1", false),
        3 => ("-1", true),
        _ => unreachable!(),
    };
    let ordered_operands = if include_imaginary_unit {
        let imaginary_unit = Obj::Literal(Literal::ImaginaryUnit(ImaginaryUnit));
        Some(vec![(imaginary_unit.clone(), obj_key(&imaginary_unit))])
    } else {
        None
    };
    vec![MonomialWithNonZeroScalarAndOrderedOperands::new(
        scalar.to_string(),
        ordered_operands,
    )]
}

fn from_number_obj_to_monomial(
    number: &Number,
) -> Vec<MonomialWithNonZeroScalarAndOrderedOperands> {
    let number_string = number.normalized_value.clone();
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
