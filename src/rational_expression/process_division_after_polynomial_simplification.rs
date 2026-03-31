use crate::prelude::*;
use crate::rational_expression::collect_monomials::collect_monomials_in_obj;
use crate::rational_expression::monomial::MonomialWithNonZeroScalarAndOrderedOperands;

pub fn collect_rational_expression_monomials_after_denominator_clearing_process(
    left_monomials: Vec<MonomialWithNonZeroScalarAndOrderedOperands>,
    right_monomials: Vec<MonomialWithNonZeroScalarAndOrderedOperands>,
) -> (
    Vec<MonomialWithNonZeroScalarAndOrderedOperands>,
    Vec<MonomialWithNonZeroScalarAndOrderedOperands>,
) {
    // Each side is first transformed from:
    //   Vec<Monomial> (with denominators embedded in operands)
    // into:
    //   Vec<((is_left, local_index), (factors_without_denominators, denominators))>.
    //
    // For example, suppose one monomial is:
    //   4 * (a / b) * c * (d / e)
    // Then after removing denominators from that monomial we get:
    //   factors_without_denominators = [4, a, c, d]
    //   denominators = [b, e]
    // and it is stored together with its (side flag, local index).

    let extracted_left_monomials = extract_monomial_fractions_from_monomial_vec(left_monomials);
    let extracted_right_monomials = extract_monomial_fractions_from_monomial_vec(right_monomials);
    let total_fraction_entry_count =
        extracted_left_monomials.len() + extracted_right_monomials.len();

    // Collect all monomial denominator factors from left and right.
    // Each element is tagged by (is_left, local_monomial_index).
    // When rebuilding a specific monomial on a given side, we skip multiplying by
    // the denominators that originate from that same (side, local index).
    let mut all_monomial_fraction_entries: Vec<((bool, usize), (Vec<Obj>, Vec<Obj>))> =
        Vec::with_capacity(total_fraction_entry_count);
    for (local_index, pair) in extracted_left_monomials.into_iter() {
        all_monomial_fraction_entries.push(((true, local_index), pair));
    }
    for (local_index, pair) in extracted_right_monomials.into_iter() {
        all_monomial_fraction_entries.push(((false, local_index), pair));
    }

    let left_monomials_after_denominator_clearing =
        multiply_fraction_denominators_and_get_side_monomials(&all_monomial_fraction_entries, true);
    let right_monomials_after_denominator_clearing =
        multiply_fraction_denominators_and_get_side_monomials(
            &all_monomial_fraction_entries,
            false,
        );

    (
        left_monomials_after_denominator_clearing,
        right_monomials_after_denominator_clearing,
    )
}

fn multiply_fraction_denominators_and_get_side_monomials(
    all_monomial_fraction_entries: &Vec<((bool, usize), (Vec<Obj>, Vec<Obj>))>,
    target_side_is_left: bool,
) -> Vec<MonomialWithNonZeroScalarAndOrderedOperands> {
    // Build the "new" monomials for one side (left or right).
    //
    // Input type:
    //   all_monomial_fraction_entries:
    //     Vec<
    //       ((is_left, local_monomial_index), (factors_without_denominators, denominators))
    //     >
    //
    // For each entry that matches `target_side_is_left`, we rebuild that monomial as:
    //   rebuilt_monomial = multiply(entry_factors_without_denominators, all_other_denominators)
    //
    // The "skip self denominators" rule is implemented inside
    // `multiply_monomial_factors_with_all_other_denominators_except_self(...)`.
    //
    // Example:
    //   Suppose the target entry (side=left, index=0) has:
    //     factors_without_denominators = [4, a, c]
    //     denominators = [b, d]
    //
    //   And another entry contributes denominators [x, y].
    //   Then the rebuilt monomial becomes:
    //     4 * a * c * x * y
    let rebuilt_monomial_count = all_monomial_fraction_entries
        .iter()
        .filter(|((entry_is_left, _), _)| *entry_is_left == target_side_is_left)
        .count();
    let mut rebuilt_monomial_objs: Vec<Obj> = Vec::with_capacity(rebuilt_monomial_count);

    for ((entry_is_left, entry_local_index), (entry_factors, _)) in
        all_monomial_fraction_entries.iter()
    {
        // Only rebuild monomials that belong to the requested side.
        if *entry_is_left != target_side_is_left {
            continue;
        }

        let rebuilt_monomial = multiply_monomial_factors_with_all_other_denominators_except_self(
            all_monomial_fraction_entries,
            target_side_is_left,
            *entry_local_index,
            entry_factors,
        );
        rebuilt_monomial_objs.push(rebuilt_monomial);
    }

    let rebuilt_rational_expression = add_obj_list(rebuilt_monomial_objs);
    let collected_monomials = collect_monomials_in_obj(&rebuilt_rational_expression);
    collected_monomials
}

// monomial: a/b * c/d * f(e), return ([a, c, f(e)], [b, d])
fn split_monomial_into_fraction_factors_and_denominators(
    monomial: &MonomialWithNonZeroScalarAndOrderedOperands,
) -> (Vec<Obj>, Vec<Obj>) {
    let mut factors = vec![Obj::Number(Number::new(monomial.non_zero_scalar.clone()))];
    let mut denominators: Vec<Obj> = if let Some(operands) = monomial.ordered_operands.as_ref() {
        Vec::with_capacity(operands.len())
    } else {
        Vec::new()
    };
    if let Some(operands) = monomial.ordered_operands.as_ref() {
        for operand in operands {
            if let Obj::Div(div) = &operand.0 {
                let denominator_factors = flatten_mul_obj_to_factors(&div.right);
                for denominator_factor in denominator_factors {
                    denominators.push(denominator_factor);
                }
                factors.push(*div.left.clone());
            } else {
                factors.push(operand.0.clone());
            }
        }
    }

    (factors, denominators)
}

fn extract_monomial_fractions_from_monomial_vec(
    monomials: Vec<MonomialWithNonZeroScalarAndOrderedOperands>,
) -> Vec<(usize, (Vec<Obj>, Vec<Obj>))> {
    // Return format:
    //   Vec<
    //     (monomial_index,
    //       (factors_without_denominators, denominators))
    //   >
    //
    // meanings:
    // - `monomial_index` is the index of the monomial in the input `monomials` Vec.
    // - `factors_without_denominators` are the factors after stripping `Obj::Div`
    //    operands from that monomial:
    //      for each (left / right) factor, we keep `left` in factors_without_denominators
    //      and push `right` into denominators.
    // - `denominators` are the collected divisor parts (the `right` of Obj::Div).
    //
    // Example:
    //   monomial = 4 * (a / b) * c / d
    // (internally represented with Obj::Div inside `ordered_operands`)
    // becomes:
    //   (index, (factors_without_denominators=[4, a, c], denominators=[b, d])).
    let mut monomials_with_denominator_removed_and_their_denominators: Vec<(
        usize,
        (Vec<Obj>, Vec<Obj>),
    )> = Vec::with_capacity(monomials.len());

    for (index, monomial) in monomials.iter().enumerate() {
        let current = split_monomial_into_fraction_factors_and_denominators(monomial);
        monomials_with_denominator_removed_and_their_denominators.push((index, current));
    }

    monomials_with_denominator_removed_and_their_denominators
}

fn multiply_monomial_factors_with_all_other_denominators_except_self(
    all_monomial_fraction_entries: &Vec<((bool, usize), (Vec<Obj>, Vec<Obj>))>,
    target_side_is_left: bool,
    target_monomial_local_index: usize,
    entry_factors: &Vec<Obj>,
) -> Obj {
    // Rebuild one monomial by multiplying:
    // - `entry_factors` (factors_without_denominators for the target monomial)
    // - all denominators (denominators from every monomial collected in `collected_all`)
    //
    // Skip rule:
    // If the denominator entry belongs to the same side and local monomial index as
    // the target monomial, we do NOT multiply that entry's denominators again.
    // This prevents "self denominators" from being squared when rebuilding.
    let mut collected_factors = entry_factors.clone();

    for ((entry_is_left, entry_local_index), (_entry_factors, denominators)) in
        all_monomial_fraction_entries.iter()
    {
        if *entry_is_left == target_side_is_left
            && *entry_local_index == target_monomial_local_index
        {
            continue;
        }

        for denominator in denominators.iter() {
            collected_factors.push(denominator.clone());
        }
    }

    multiply_obj_list(collected_factors)
}

fn flatten_mul_obj_to_factors(obj: &Obj) -> Vec<Obj> {
    match obj {
        Obj::Mul(mul) => {
            let left_factors = flatten_mul_obj_to_factors(&mul.left);
            let right_factors = flatten_mul_obj_to_factors(&mul.right);
            let mut flattened_factors: Vec<Obj> =
                Vec::with_capacity(left_factors.len() + right_factors.len());
            for left_factor in left_factors {
                flattened_factors.push(left_factor);
            }
            for right_factor in right_factors {
                flattened_factors.push(right_factor);
            }
            flattened_factors
        }
        _ => vec![obj.clone()],
    }
}

fn multiply_obj_list(objs: Vec<Obj>) -> Obj {
    let mut objs = objs.into_iter();
    let first_obj = match objs.next() {
        Some(obj) => obj,
        None => return Obj::Number(Number::new("1".to_string())),
    };

    let mut result = first_obj;
    for obj in objs {
        result = Obj::Mul(Mul::new(result, obj));
    }

    result
}

fn add_obj_list(objs: Vec<Obj>) -> Obj {
    let mut objs = objs.into_iter();
    let first_obj = match objs.next() {
        Some(obj) => obj,
        None => return Obj::Number(Number::new("0".to_string())),
    };

    let mut result = first_obj;
    for obj in objs {
        result = Obj::Add(Add::new(result, obj));
    }

    result
}
