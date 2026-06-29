// Integers strictly above 0 are at least 1 (uses Z and order on R).

pub const FUNDAMENTAL_NUMBER_PROPERTIES: &str = r#"
know:
    forall x Z, y Z:
        y < x
        =>:
            y + 1 <= x

    forall x Z, y Z:
        x < y
        =>:
            x <= y - 1

    forall x Z, y Z:
        y <= x < y + 1
        =>:
            x = y

    forall x Q:
        exist p, q Z st {q > 0, x = p / q}

    forall x Q:
        exist p Z, q Z_nz st {x = p / q}

    forall x, y R:
        x < y
        =>:
            exist z Q st {x < z < y}

    forall a, b Z:
        closed_range(a, b) = {x Z: a <= x <= b}

    forall a, b Z:
        range(a, b) = {x Z: a <= x < b}

    forall a, b Z:
        b != 0
        a % b = 0
        =>:
            exist k Z st {a = k * b}

    forall a, b N_pos:
        exist k N_pos st {a = k * b}

    # Litex evaluates `1 % 1 = 0`. For modulus `k` in `N_pos` with `k >= 2`, the remainder of 1 is 1.
    forall k N_pos:
        k >= 2 or k != 1
        =>:
            1 % k = 1

# Rational representation by integer numerator and nonzero integer denominator.
# Example: `forall q Q: exist a Z, b Z_nz st {q = a / b}`.
thm rational_as_integer_ratio:
    prove:
        forall x Q:
            exist p Z, q Z_nz st {x = p / q}
    exist p Z, q Z_nz st {x = p / q}
"#;
