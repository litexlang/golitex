use crate::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct RuleId(String);

impl RuleId {
    pub fn new(value: impl Into<String>) -> Result<Self, String> {
        let value = value.into();
        let valid = !value.is_empty()
            && value.split('.').all(|part| {
                !part.is_empty()
                    && part
                        .chars()
                        .next()
                        .is_some_and(|ch| ch.is_ascii_lowercase())
                    && part
                        .chars()
                        .all(|ch| ch.is_ascii_lowercase() || ch.is_ascii_digit() || ch == '_')
            });
        if !valid {
            return Err(format!("invalid local builtin RuleId `{value}`"));
        }
        Ok(Self(value))
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RuleFingerprint(String);

impl RuleFingerprint {
    pub fn from_hex(value: impl Into<String>) -> Result<Self, String> {
        let value = value.into();
        if value.len() != 64 || !value.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return Err(format!("invalid local builtin fingerprint `{value}`"));
        }
        Ok(Self(value.to_ascii_lowercase()))
    }

    pub fn as_hex(&self) -> &str {
        &self.0
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuleSourceRef {
    KnownForall {
        source_fact_id: crate::common::fact_id::FactId,
        conclusion_index: usize,
    },
    LocalBuiltin {
        rule_id: RuleId,
        semantic_fingerprint: RuleFingerprint,
    },
}

#[derive(Clone)]
pub struct RuleVariable {
    pub(crate) binding: SymbolBinding,
    pub(crate) param_type: ParamType,
}

#[derive(Clone)]
pub struct CompiledRuleSchema {
    pub(crate) source: RuleSourceRef,
    pub(crate) variables: Vec<RuleVariable>,
    pub(crate) parameter_requirements: Vec<AtomicFact>,
    pub(crate) premises: Vec<QuantifierFreeFact>,
    pub(crate) conclusion: AtomicFact,
    pub(crate) head_key: super::AtomicFactHead,
}
