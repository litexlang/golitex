use crate::obj::Obj;
use crate::simplify_polynomial::collect_monomials::collect_monomials_in_obj;
use crate::simplify_polynomial::monomial::MonomialWithNonZeroScalarAndOrderedOperands;
use crate::simplify_polynomial::process_division_after_polynomial_simplification::polynomial_equal_after_division_process;

pub fn two_objs_equal_by_polynomial_simplification_and_division_process(left: &Obj, right: &Obj) -> bool {
    let left_monomials = collect_monomials_in_obj(left);
    let right_monomials = collect_monomials_in_obj(right);

    if monomial_vectors_are_equal(left_monomials.clone(), right_monomials.clone()) {
        return true;
    }

    let (left_monomials_after_division, right_monomials_after_division) = polynomial_equal_after_division_process(left_monomials, right_monomials);
    monomial_vectors_are_equal(left_monomials_after_division, right_monomials_after_division)
}

fn sort_monomials(monomials: Vec<MonomialWithNonZeroScalarAndOrderedOperands>) -> Vec<MonomialWithNonZeroScalarAndOrderedOperands> {
    let mut result = monomials;
    result.sort_by(|a, b| a.key().cmp(&b.key()));
    result
}

fn monomial_vectors_are_equal(
    left_monomials: Vec<MonomialWithNonZeroScalarAndOrderedOperands>,
    right_monomials: Vec<MonomialWithNonZeroScalarAndOrderedOperands>,
) -> bool {
    if left_monomials.len() != right_monomials.len() {
        return false;
    }

    let sorted_left = sort_monomials(left_monomials);
    let sorted_right = sort_monomials(right_monomials);

    for (left_monomial, right_monomial) in sorted_left.iter().zip(sorted_right.iter()) {
        if left_monomial.non_zero_scalar != right_monomial.non_zero_scalar {
            return false;
        }
        if left_monomial.key() != right_monomial.key() {
            return false;
        }
    }

    true
}