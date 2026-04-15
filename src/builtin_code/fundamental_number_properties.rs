// Integers strictly above 0 are at least 1 (uses Z and order on R).

pub const FUNDAMENTAL_NUMBER_PROPERTIES: &str = r#"
know:
    forall x Z:
        0 < x
        =>:
            1 <= x
"#;
