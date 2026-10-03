//! Bounded exact factorization shared by rational logs and numeric radicals.

// Trial division proves the residual prime only after passing its square root.
// Exhaustion declines the calculation; it never assumes a large residual prime.
pub(crate) fn factor_positive_integer(mut value: i128) -> Option<Vec<(i128, i128)>> {
    if value <= 0 {
        return None;
    }
    let mut factors = Vec::new();
    let mut divisor = 2;
    while divisor <= value / divisor {
        if divisor > 10_000 {
            return None;
        }
        let mut exponent = 0;
        while value % divisor == 0 {
            value /= divisor;
            exponent += 1;
        }
        if exponent != 0 {
            factors.push((divisor, exponent));
        }
        divisor = if divisor == 2 { 3 } else { divisor + 2 };
    }
    if value > 1 {
        factors.push((value, 1));
    }
    Some(factors)
}
