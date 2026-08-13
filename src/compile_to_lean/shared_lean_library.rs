pub(super) const LITEX_LEAN_ABI_VERSION: u32 = 1;

/// Imports the shared target ABI and pins generated output to its ABI version.
pub(super) fn generated_import_header() -> String {
    format!(
        "import Litex.BuiltinRules\n\nexample : Litex.abiVersion = {LITEX_LEAN_ABI_VERSION} := rfl"
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    const CORE_SOURCE: &str = include_str!("../../lean/Litex/Core.lean");
    const BUILTIN_RULES_SOURCE: &str = include_str!("../../lean/Litex/BuiltinRules.lean");
    const LAKEFILE: &str = include_str!("../../lean/lakefile.toml");

    #[test]
    fn shared_library_owns_one_object_abi_and_real_builtin_theorems() {
        assert!(CORE_SOURCE.contains("def abiVersion : Nat := 1"));
        assert!(CORE_SOURCE.contains("axiom Object : Type"));
        assert!(CORE_SOURCE.contains("axiom In : Object → Object → Prop"));
        assert!(CORE_SOURCE.contains("axiom IsSet : Object → Prop"));
        assert!(CORE_SOURCE.contains("def IsNonemptySet (s : Object) : Prop :="));
        assert!(CORE_SOURCE.contains("def IsFiniteSet (s : Object) : Prop :="));
        assert!(CORE_SOURCE.contains("axiom Applicable : Object → List Object → Prop"));
        assert!(!CORE_SOURCE.contains("namespace BuiltinRules"));

        assert!(BUILTIN_RULES_SOURCE.starts_with("import Litex.Core"));
        assert!(BUILTIN_RULES_SOURCE.contains("theorem notEqualSymmetry"));
        assert!(BUILTIN_RULES_SOURCE.contains("theorem numeralInN"));
        assert!(BUILTIN_RULES_SOURCE.contains("theorem numeralInC"));
        assert!(BUILTIN_RULES_SOURCE.contains("theorem realSubClosure"));
        assert!(!BUILTIN_RULES_SOURCE.contains("axiom notEqualSymmetry"));
    }

    #[test]
    fn generated_header_imports_shared_library_without_repeating_it() {
        let header = generated_import_header();
        assert_eq!(
            header,
            "import Litex.BuiltinRules\n\nexample : Litex.abiVersion = 1 := rfl"
        );
        assert!(!header.contains("import Mathlib"));
        assert!(!header.contains("axiom Object"));
        assert!(!header.contains("theorem notEqualSymmetry"));
    }

    #[test]
    fn checked_in_generated_file_header_matches_the_emitter() {
        assert_eq!(
            include_str!("current_generated_file_header.lean").trim_end(),
            generated_import_header()
        );
    }

    #[test]
    fn compiler_and_shared_core_agree_on_abi_version() {
        assert!(CORE_SOURCE.contains(&format!("def abiVersion : Nat := {LITEX_LEAN_ABI_VERSION}")));
        assert!(generated_import_header()
            .contains(&format!("Litex.abiVersion = {LITEX_LEAN_ABI_VERSION}")));
    }

    #[test]
    fn rust_and_lean_packages_share_a_release_version() {
        assert!(LAKEFILE.contains(&format!("version = \"{}\"", env!("CARGO_PKG_VERSION"))));
    }

    #[test]
    fn litex_object_design_has_exactly_ten_representative_examples() {
        let design = include_str!("litex_object_design.md");
        let example_count = design
            .lines()
            .filter(|line| line.starts_with("### Example "))
            .count();
        assert_eq!(example_count, 10);
    }
}
