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
pub struct RegisteredLocalBuiltinRule {
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

    pub fn schema(&self) -> &CompiledRuleSchema {
        &self.schema
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
        .map(compile_registered_local_builtin_rule)
        .collect()
}

fn compile_registered_local_builtin_rule(
    source: &GeneratedLocalBuiltinRuleSource,
) -> Result<RegisteredLocalBuiltinRule, RuntimeError> {
    let id = RuleId::new(source.id).map_err(registry_error)?;
    let fingerprint =
        RuleFingerprint::from_hex(source.semantic_fingerprint).map_err(registry_error)?;
    let schema = compile_local_builtin_schema(source.litex_source, id, fingerprint)?;
    Ok(RegisteredLocalBuiltinRule {
        schema,
        _lean_theorem_name: source.lean_theorem_name,
    })
}

/// Read the generated semantic fingerprint without parsing the Litex schema.
/// Result consumers use this narrow metadata lookup to reject stale
/// certificates without rebuilding the verifier catalog.
pub fn registered_local_builtin_fingerprint_by_id(
    rule_id: &RuleId,
) -> Result<Option<RuleFingerprint>, RuntimeError> {
    GENERATED_LOCAL_BUILTIN_RULES
        .iter()
        .find(|source| source.id == rule_id.as_str())
        .map(|source| {
            RuleFingerprint::from_hex(source.semantic_fingerprint).map_err(registry_error)
        })
        .transpose()
}

thread_local! {
    static COMPILED_RULES: RefCell<Option<Result<Vec<RegisteredLocalBuiltinRule>, String>>> =
        const { RefCell::new(None) };
}

pub fn registered_local_builtin_rules() -> Result<Vec<RegisteredLocalBuiltinRule>, RuntimeError> {
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
#[path = "../../../tests/unit/verify/local_builtin_catalog/registry/tests.rs"]
mod tests;
