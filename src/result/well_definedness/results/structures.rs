//! Structure argument, field, and equivalent-fact checks.

use crate::prelude::*;
use std::fmt;

pub struct SuccessVerifyStructureWellDefinedResult {
    pub structure_name: String,
    pub header_arguments: Vec<SuccessVerifyStructureHeaderArgumentResult>,
    pub header_domains: Vec<SuccessVerifyFactForObjWellDefinedResult>,
    pub fields: Vec<SuccessVerifyStructureFieldResult>,
    pub equivalent_facts: Vec<SuccessVerifyStructureEquivalentFactResult>,
}

pub struct SuccessVerifyStructureHeaderArgumentResult {
    pub argument_index: usize,
    pub argument: Obj,
    pub expected_type: ParamType,
    pub verification: SuccessVerifyFactForObjWellDefinedResult,
}

#[derive(Debug)]
pub struct SuccessVerifyStructureFieldResult {
    pub field_index: usize,
    pub field_name: String,
    pub carrier: SuccessVerifyChildObjWellDefinedResult,
    pub premise: SuccessVerifyBinderPremiseResult,
}

#[derive(Debug)]
pub struct SuccessVerifyStructureEquivalentFactResult {
    pub fact_index: usize,
    pub proposition: Fact,
    pub well_definedness: Box<SuccessVerifyFactWellDefinedResult>,
    pub store: SuccessStoreFactResult,
}

impl fmt::Debug for SuccessVerifyStructureWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyStructureWellDefinedResult")
            .field("structure_name", &self.structure_name)
            .field("header_arguments", &self.header_arguments)
            .field("header_domains", &self.header_domains)
            .field("fields", &self.fields)
            .field("equivalent_facts", &self.equivalent_facts)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyStructureHeaderArgumentResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyStructureHeaderArgumentResult")
            .field("argument_index", &self.argument_index)
            .field("argument", &self.argument.to_string())
            .field("expected_type", &self.expected_type.to_string())
            .field("verification", &self.verification)
            .finish()
    }
}
