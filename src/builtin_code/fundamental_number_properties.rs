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

    forall x, y R:
        x < y
        =>:
            exist z Q st {x < z < y}

    forall a, b Z:
        closed_range(a, b) = {x Z: a <= x <= b}

    forall a, b Z:
        range(a, b) = {x Z: a <= x < b}
"#;
