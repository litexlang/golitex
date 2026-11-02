use super::*;

fn add(a: RingExpression, b: RingExpression) -> RingExpression {
    RingExpression::Add(a.into(), b.into())
}
fn mul(a: RingExpression, b: RingExpression) -> RingExpression {
    RingExpression::Mul(a.into(), b.into())
}
fn neg(a: RingExpression) -> RingExpression {
    RingExpression::Neg(a.into())
}
fn atom(index: usize) -> RingExpression {
    RingExpression::Atom(index)
}
fn normalize(expression: &RingExpression) -> RingNormalizationCertificate {
    normalize_ring_expression(
        expression,
        &mut RingNormalizationBudget::new(RingNormalizationLimits::new()),
    )
    .expect("small expression must normalize")
}

#[test]
fn square_difference_has_the_same_integer_polynomial() {
    let left = mul(add(atom(0), atom(1)), add(atom(0), neg(atom(1))));
    let right = add(mul(atom(0), atom(0)), neg(mul(atom(1), atom(1))));
    let left = normalize(&left);
    let right = normalize(&right);
    assert_eq!(left.polynomial(), right.polynomial());
    assert_eq!(left.polynomial().unwrap().terms.len(), 2);
}

#[test]
fn unrelated_atoms_and_false_identities_stay_different() {
    assert_ne!(
        normalize(&mul(atom(0), atom(0))).polynomial(),
        normalize(&atom(0)).polynomial()
    );
    assert_ne!(
        normalize(&atom(0)).polynomial(),
        normalize(&RingExpression::One).polynomial()
    );
    assert_ne!(
        normalize(&add(atom(0), atom(0))).polynomial(),
        normalize(&RingExpression::Zero).polynomial()
    );
}

fn evaluate_expression(expression: &RingExpression, values: &[i128], modulus: i128) -> i128 {
    let value = match expression {
        RingExpression::Zero => 0,
        RingExpression::One => 1,
        RingExpression::Atom(atom) => values[*atom],
        RingExpression::Add(a, b) => {
            evaluate_expression(a, values, modulus) + evaluate_expression(b, values, modulus)
        }
        RingExpression::Mul(a, b) => {
            evaluate_expression(a, values, modulus) * evaluate_expression(b, values, modulus)
        }
        RingExpression::Neg(a) => -evaluate_expression(a, values, modulus),
    };
    value.rem_euclid(modulus)
}

fn evaluate_polynomial(polynomial: &RingPolynomial, values: &[i128], modulus: i128) -> i128 {
    let mut result = 0;
    for (monomial, coefficient) in &polynomial.terms {
        let mut value = coefficient.rem_euclid(modulus);
        for (atom, exponent) in monomial {
            for _ in 0..*exponent {
                value = (value * values[*atom]).rem_euclid(modulus);
            }
        }
        result = (result + value).rem_euclid(modulus);
    }
    result
}

#[test]
fn normalized_polynomials_preserve_values_in_finite_rings_including_zero_ring() {
    let mut expressions = vec![RingExpression::Zero, RingExpression::One, atom(0), atom(1)];
    // Deterministic varied trees; the oracle evaluates syntax directly rather
    // than duplicating coefficient collection or monomial merging.
    for i in 0..80 {
        let a = expressions[(i * 7 + 1) % expressions.len()].clone();
        let b = expressions[(i * 11 + 2) % expressions.len()].clone();
        let next = match i % 3 {
            0 => add(a, b),
            1 => mul(a, b),
            _ => neg(a),
        };
        expressions.push(next);
    }
    for expression in &expressions {
        let certificate = normalize(expression);
        for modulus in 1..=5 {
            for a in 0..modulus {
                for b in 0..modulus {
                    assert_eq!(
                        evaluate_expression(expression, &[a, b], modulus),
                        evaluate_polynomial(certificate.polynomial().unwrap(), &[a, b], modulus)
                    );
                }
            }
        }
    }
}

#[test]
fn certificate_validation_rejects_mutated_results_sources_and_children() {
    let expression = mul(add(atom(0), RingExpression::One), atom(1));
    let original = normalize(&expression);
    let limits = RingNormalizationLimits::new();
    assert!(check_ring_normalization_certificate(
        &expression,
        &original,
        limits
    ));
    let mut bad = original.clone();
    bad.nodes[bad.root].polynomial.terms.insert(Vec::new(), 17);
    assert!(!check_ring_normalization_certificate(
        &expression,
        &bad,
        limits
    ));
    let mut bad = original.clone();
    bad.nodes[bad.root].operation = RingNormalizationOperation::Mul(bad.root, bad.root);
    assert!(!check_ring_normalization_certificate(
        &expression,
        &bad,
        limits
    ));
    assert!(!check_ring_normalization_certificate(
        &atom(0),
        &original,
        limits
    ));
    let mut bad = original.clone();
    bad.nodes.push(original.nodes[0].clone());
    assert!(!check_ring_normalization_certificate(
        &expression,
        &bad,
        limits
    ));
}

#[test]
fn bounded_normalization_declines_expansion_depth_work_and_large_coefficients() {
    let mut limits = RingNormalizationLimits::new();
    limits.max_monomials = 2;
    let expression = mul(add(atom(0), atom(1)), add(atom(2), atom(3)));
    assert!(
        normalize_ring_expression(&expression, &mut RingNormalizationBudget::new(limits)).is_none()
    );
    limits = RingNormalizationLimits::new();
    limits.max_depth = 1;
    assert!(
        normalize_ring_expression(&expression, &mut RingNormalizationBudget::new(limits)).is_none()
    );
    limits = RingNormalizationLimits::new();
    limits.max_work = 0;
    assert!(normalize_ring_expression(
        &RingExpression::One,
        &mut RingNormalizationBudget::new(limits)
    )
    .is_none());
    let mut huge = add(RingExpression::One, RingExpression::One);
    for _ in 0..7 {
        huge = mul(huge.clone(), huge);
    }
    assert!(normalize_ring_expression(
        &huge,
        &mut RingNormalizationBudget::new(RingNormalizationLimits::new())
    )
    .is_none());
}
