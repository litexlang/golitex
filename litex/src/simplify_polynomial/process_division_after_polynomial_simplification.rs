use crate::obj::{Add, Mul, Number, Obj};
use crate::simplify_polynomial::collect_monomials::collect_monomials_in_obj;
use crate::simplify_polynomial::monomial::MonomialWithNonZeroScalarAndOrderedOperands;

pub fn polynomial_equal_after_division_process(polynomial1: Vec<MonomialWithNonZeroScalarAndOrderedOperands>, polynomial2: Vec<MonomialWithNonZeroScalarAndOrderedOperands>) -> (Vec<MonomialWithNonZeroScalarAndOrderedOperands>, Vec<MonomialWithNonZeroScalarAndOrderedOperands>) {
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

    let collected_polynomial1 = remove_denominators_from_monomials(polynomial1);
    let collected_polynomial2 = remove_denominators_from_monomials(polynomial2);

    // Collect all monomial denominator factors from left and right.
    // Each element is tagged by (is_left, local_monomial_index).
    // When rebuilding a specific monomial on a given side, we skip multiplying by
    // the denominators that originate from that same (side, local index).
    let mut collected_all: Vec<((bool, usize), (Vec<Obj>, Vec<Obj>))> = vec![];
    for (local_index, pair) in collected_polynomial1.into_iter() {
        collected_all.push(((true, local_index), pair));
    }
    for (local_index, pair) in collected_polynomial2.into_iter() {
        collected_all.push(((false, local_index), pair));
    }

    let simplified_polynomial1 = multiply_collected_denominators_and_get_new_monomials(
        &collected_all,
        true,
    );
    let simplified_polynomial2 = multiply_collected_denominators_and_get_new_monomials(
        &collected_all,
        false,
    );

    (simplified_polynomial1, simplified_polynomial2)
}

fn multiply_collected_denominators_and_get_new_monomials(
    collected_all_monomials_with_denominator_removed_and_their_denominators: &Vec<((bool, usize), (Vec<Obj>, Vec<Obj>))>,
    monomial_is_left: bool,
) -> Vec<MonomialWithNonZeroScalarAndOrderedOperands> {
    // Build the "new" monomials for one side (left or right).
    //
    // Input type:
    //   collected_all_monomials_with_denominator_removed_and_their_denominators:
    //     Vec<
    //       ((is_left, local_monomial_index), (factors_without_denominators, denominators))
    //     >
    //
    // For each entry that matches `monomial_is_left`, we rebuild that monomial as:
    //   rebuilt_monomial = multiply(entry_factors_without_denominators, all_other_denominators)
    //
    // The "skip self denominators" rule is implemented inside
    // `multiply_collect_denominator_to_monomial(...)`.
    //
    // Example:
    //   Suppose the target entry (side=left, index=0) has:
    //     factors_without_denominators = [4, a, c]
    //     denominators = [b, d]
    //
    //   And another entry contributes denominators [x, y].
    //   Then the rebuilt monomial becomes:
    //     4 * a * c * x * y
    let mut rebuilt_monomial_objs: Vec<Obj> = vec![];

    for ((entry_is_left, entry_local_index), (entry_factors, _)) in collected_all_monomials_with_denominator_removed_and_their_denominators.iter() {
        // Only rebuild monomials that belong to the requested side.
        if *entry_is_left != monomial_is_left {
            continue;
        }

        let rebuilt_monomial = multiply_collect_denominator_to_monomial(
            collected_all_monomials_with_denominator_removed_and_their_denominators,
            monomial_is_left,
            *entry_local_index,
            entry_factors,
        );
        rebuilt_monomial_objs.push(rebuilt_monomial);
    }

    let rebuilt_polynomial = add_objs(rebuilt_monomial_objs);
    let simplified_monomials = collect_monomials_in_obj(&rebuilt_polynomial);
    simplified_monomials
}

// monomial: a/b * c/d * f(e), return ([a, c, f(e)], [b, d])
fn remove_denominators_from_monomial(monomial: &MonomialWithNonZeroScalarAndOrderedOperands) -> (Vec<Obj>, Vec<Obj>) {
    let mut factors = vec![Obj::Number(Number::new(monomial.non_zero_scalar.clone()))];
    let mut denominators: Vec<Obj> = vec![];
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

fn remove_denominators_from_monomials(
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
    let mut monomials_with_denominator_removed_and_their_denominators: Vec<(usize, (Vec<Obj>, Vec<Obj>))> = vec![];

    for (index, monomial) in monomials.iter().enumerate() {
        let current = remove_denominators_from_monomial(monomial);
        monomials_with_denominator_removed_and_their_denominators.push((index, current));
    }

    monomials_with_denominator_removed_and_their_denominators
}

fn multiply_collect_denominator_to_monomial(
    collected_all_monomials_with_denominator_removed_and_their_denominators: &Vec<((bool, usize), (Vec<Obj>, Vec<Obj>))>,
    monomial_is_left: bool,
    monomial_local_index: usize,
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
        collected_all_monomials_with_denominator_removed_and_their_denominators.iter()
    {
        if *entry_is_left == monomial_is_left && *entry_local_index == monomial_local_index {
            continue;
        }

        for denominator in denominators.iter() {
            collected_factors.push(denominator.clone());
        }
    }

    multiply_objs(collected_factors)
}

fn flatten_mul_obj_to_factors(obj: &Obj) -> Vec<Obj> {
    match obj {
        Obj::Mul(mul) => {
            let mut flattened_factors: Vec<Obj> = vec![];
            let left_factors = flatten_mul_obj_to_factors(&mul.left);
            for left_factor in left_factors {
                flattened_factors.push(left_factor);
            }
            let right_factors = flatten_mul_obj_to_factors(&mul.right);
            for right_factor in right_factors {
                flattened_factors.push(right_factor);
            }
            flattened_factors
        }
        _ => vec![obj.clone()],
    }
}

fn multiply_objs(objs: Vec<Obj>) -> Obj {
    let mut objs = objs.into_iter();
    let first_obj = match objs.next() {
        Some(obj) => obj,
        None => return Obj::Number(Number::new("1".to_string())),
    };

    let mut result = first_obj;
    for obj in objs {
        let can_be_calculated = result.can_be_calculated() && obj.can_be_calculated();
        result = Obj::Mul(Mul::new(result, obj, can_be_calculated));
    }

    result
}

fn add_objs(objs: Vec<Obj>) -> Obj {
    let mut objs = objs.into_iter();
    let first_obj = match objs.next() {
        Some(obj) => obj,
        None => return Obj::Number(Number::new("0".to_string())),
    };

    let mut result = first_obj;
    for obj in objs {
        let can_be_calculated = result.can_be_calculated() && obj.can_be_calculated();
        result = Obj::Add(Add::new(result, obj, can_be_calculated));
    }

    result
}
