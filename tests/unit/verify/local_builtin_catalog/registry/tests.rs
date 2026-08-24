use super::*;
use std::collections::HashSet;

impl RegisteredLocalBuiltinRule {
    pub fn semantic_fingerprint(&self) -> &RuleFingerprint {
        let RuleSourceRef::LocalBuiltin {
            semantic_fingerprint,
            ..
        } = &self.schema.source
        else {
            unreachable!("local builtin registry contained a non-builtin source")
        };
        semantic_fingerprint
    }

    pub fn lean_theorem_name(&self) -> &str {
        self._lean_theorem_name
    }
}

#[test]
fn generated_catalog_parses_as_restricted_forall_schemas() {
    std::thread::Builder::new()
        .name("local-builtin-catalog-parse".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let rules = registered_local_builtin_rules().expect("compile generated catalog");
            assert_eq!(rules.len(), GENERATED_LOCAL_BUILTIN_RULES.len());
            let mut ids = HashSet::new();
            let mut fingerprints = HashSet::new();
            for rule in rules {
                assert!(ids.insert(rule.id().as_str().to_string()));
                assert!(fingerprints.insert(rule.semantic_fingerprint().as_hex().to_string()));
                assert_eq!(
                    rule.lean_theorem_name(),
                    rule.id().as_str().replace('.', "_")
                );
            }
        })
        .expect("spawn catalog parser")
        .join()
        .expect("catalog parser panicked");
}
