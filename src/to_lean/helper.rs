pub(super) fn lean_generic_carrier_name(index: u64) -> String {
    if index == 0 {
        "α".to_string()
    } else {
        format!("α{}", index)
    }
}
