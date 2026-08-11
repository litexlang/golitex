use crate::prelude::*;
use crate::verify::rule_schema::{
    compile_local_builtin_schema, CompiledRuleSchema, RuleFingerprint, RuleId, RuleSourceRef,
};
use std::cell::RefCell;

pub(super) struct GeneratedLocalBuiltinRuleSource {
    pub id: &'static str,
    pub semantic_fingerprint: &'static str,
    pub litex_source: &'static str,
    pub lean_theorem_name: &'static str,
}

include!("generated_catalog.rs");

#[derive(Clone)]
pub(crate) struct RegisteredLocalBuiltinRule {
    schema: CompiledRuleSchema,
    _lean_theorem_name: &'static str,
}

impl RegisteredLocalBuiltinRule {
    pub fn id(&self) -> &RuleId {
        let RuleSourceRef::LocalBuiltin { rule_id, .. } = &self.schema.source else {
            unreachable!("local builtin registry contained a non-builtin source")
        };
        rule_id
    }

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

    pub fn schema(&self) -> &CompiledRuleSchema {
        &self.schema
    }

    #[cfg(test)]
    pub fn lean_theorem_name(&self) -> &str {
        self._lean_theorem_name
    }
}

fn registry_error(message: String) -> RuntimeError {
    RuntimeError::from(UnknownRuntimeError(RuntimeErrorStruct::new_with_just_msg(
        message,
    )))
}

fn compile_registered_local_builtin_rules() -> Result<Vec<RegisteredLocalBuiltinRule>, RuntimeError>
{
    GENERATED_LOCAL_BUILTIN_RULES
        .iter()
        .map(|source| {
            let id = RuleId::new(source.id).map_err(registry_error)?;
            let fingerprint =
                RuleFingerprint::from_hex(source.semantic_fingerprint).map_err(registry_error)?;
            let schema = compile_local_builtin_schema(source.litex_source, id, fingerprint)?;
            Ok(RegisteredLocalBuiltinRule {
                schema,
                _lean_theorem_name: source.lean_theorem_name,
            })
        })
        .collect()
}

thread_local! {
    static COMPILED_RULES: RefCell<Option<Result<Vec<RegisteredLocalBuiltinRule>, String>>> =
        const { RefCell::new(None) };
}

pub(crate) fn registered_local_builtin_rules(
) -> Result<Vec<RegisteredLocalBuiltinRule>, RuntimeError> {
    COMPILED_RULES.with(|cache| {
        if cache.borrow().is_none() {
            let compiled = compile_registered_local_builtin_rules()
                .map_err(|error| format!("failed to compile local builtin catalog: {error:?}"));
            *cache.borrow_mut() = Some(compiled);
        }
        match cache.borrow().as_ref().expect("catalog cache initialized") {
            Ok(rules) => Ok(rules.clone()),
            Err(message) => Err(registry_error(message.clone())),
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

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
}
