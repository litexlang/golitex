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
"#;
