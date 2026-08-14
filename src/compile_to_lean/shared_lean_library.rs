pub(super) const RULES_NAMESPACE_NAME: &str = "Rules";

pub(super) fn rules_namespace() -> String {
    format!("Litex.{RULES_NAMESPACE_NAME}")
}

pub(super) fn rule_theorem_name(theorem_name: &str) -> String {
    format!("{}.{theorem_name}", rules_namespace())
}

/// Imports the shared target ABI without adding declarations to generated files.
pub(super) fn generated_import_header() -> String {
    format!("import {}", rules_namespace())
}

#[cfg(test)]
mod tests {
    use super::*;

    const CORE_SOURCE: &str = include_str!("../../lean/Litex/Core.lean");
    const RULES_SOURCE: &str = include_str!("../../lean/Litex/Rules.lean");
    const LAKEFILE: &str = include_str!("../../lean/lakefile.toml");

    #[test]
    fn shared_library_owns_one_object_abi_and_real_builtin_theorems() {
        assert!(CORE_SOURCE.contains("def abiVersion : Nat := 9"));
        assert!(CORE_SOURCE.contains("axiom Object : Type"));
        assert!(CORE_SOURCE.contains("axiom In : Object → Object → Prop"));
        assert!(CORE_SOURCE.contains("def IsSet (_ : Object) : Prop := True"));
        assert!(!CORE_SOURCE.contains("axiom IsSet"));
        assert!(CORE_SOURCE.contains("theorem everyObjectIsSet"));
        assert!(CORE_SOURCE.contains("def IsNonemptySet (s : Object) : Prop :="));
        assert!(CORE_SOURCE.contains("def IsFiniteSet (s : Object) : Prop :="));
        assert!(CORE_SOURCE.contains("axiom Applicable : Object → List Object → Prop"));
        assert!(CORE_SOURCE.contains("axiom apply : Object → List Object → Object"));
        assert!(CORE_SOURCE.contains("axiom functionObjectApplicableLength"));
        assert!(CORE_SOURCE.contains("axiom functionObjectApplicableRequirements"));
        assert!(CORE_SOURCE.contains("In (functionObject spec body) (FnSet spec)"));
        assert!(!CORE_SOURCE.contains("functionObject spec body closed"));
        assert!(CORE_SOURCE.contains("axiom add : Object → Object → Object"));
        assert!(CORE_SOURCE.contains("axiom inRPos_iff"));
        assert!(CORE_SOURCE.contains("axiom inNPos_iff"));
        assert!(CORE_SOURCE.contains("theorem isSetR : IsSet R"));
        assert!(CORE_SOURCE.contains("axiom div : Object → Object → Object"));
        assert!(CORE_SOURCE.contains("axiom listSet : List Object → Object"));
        assert!(!CORE_SOURCE.contains(&format!("namespace {RULES_NAMESPACE_NAME}")));

        assert!(RULES_SOURCE.starts_with("import Litex.Core"));
        assert!(RULES_SOURCE.contains("namespace Litex.Rules"));
        assert!(RULES_SOURCE.contains("theorem notEqualSymmetry"));
        assert!(RULES_SOURCE.contains("theorem numeralInN"));
        assert!(RULES_SOURCE.contains("theorem numeralInNPos"));
        assert!(RULES_SOURCE.contains("theorem numeralInC"));
        assert!(RULES_SOURCE.contains("theorem positiveRealMembership"));
        assert!(RULES_SOURCE.contains("theorem realSetNonempty"));
        assert!(RULES_SOURCE.contains("theorem complexAddClosure"));
        assert!(RULES_SOURCE.contains("theorem complexSubClosure"));
        assert!(RULES_SOURCE.contains("theorem complexMulClosure"));
        assert!(RULES_SOURCE.contains("theorem complexDivClosure"));
        assert!(RULES_SOURCE.contains("theorem realSubClosure"));
        assert!(RULES_SOURCE.contains("theorem realDivClosure"));
        assert!(!RULES_SOURCE.contains("axiom notEqualSymmetry"));
    }

    #[test]
    fn generated_header_imports_shared_library_without_repeating_it() {
        let header = generated_import_header();
        assert_eq!(RULES_NAMESPACE_NAME, "Rules");
        assert_eq!(rules_namespace(), "Litex.Rules");
        assert_eq!(rule_theorem_name("numeralInR"), "Litex.Rules.numeralInR");
        assert_eq!(header, "import Litex.Rules");
        assert!(!header.contains("abiVersion"));
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
