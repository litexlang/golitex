pub(super) const TO_LEAN_DEFAULT_UNIVERSE: &str = "u";
pub(super) const TO_LEAN_GENERIC_CARRIER_PREFIX: &str = "α";
pub(super) const TO_LEAN_OBJECT_CLASS: &str = "LitexObject";
pub(super) const TO_LEAN_IS_SET: &str = "litexIsSet";
pub(super) const TO_LEAN_IS_NONEMPTY_SET: &str = "litexIsNonemptySet";
pub(super) const TO_LEAN_IS_FINITE_SET: &str = "litexIsFiniteSet";

pub(super) fn lean_generic_carrier_name(index: u64) -> String {
    if index == 0 {
        TO_LEAN_GENERIC_CARRIER_PREFIX.to_string()
    } else {
        format!("{}{}", TO_LEAN_GENERIC_CARRIER_PREFIX, index)
    }
}

pub(super) fn lean_generic_object_binder(carrier: &str) -> String {
    format!(
        "{{{} : Type {}}} [{} {}]",
        carrier, TO_LEAN_DEFAULT_UNIVERSE, TO_LEAN_OBJECT_CLASS, carrier
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generic_carrier_names_follow_the_shared_prefix() {
        assert_eq!(lean_generic_carrier_name(0), "α");
        assert_eq!(lean_generic_carrier_name(1), "α1");
        assert_eq!(lean_generic_carrier_name(12), "α12");
    }

    #[test]
    fn generic_object_binder_uses_the_shared_output_contract() {
        assert_eq!(
            lean_generic_object_binder("α"),
            "{α : Type u} [LitexObject α]"
        );
        assert_eq!(
            lean_generic_object_binder("α1"),
            "{α1 : Type u} [LitexObject α1]"
        );
    }
}
