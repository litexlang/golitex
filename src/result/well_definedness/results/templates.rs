//! Template instance reuse, creation, domain, and header checks.

use crate::prelude::*;
use std::fmt;

#[derive(Debug)]
pub enum SuccessTemplateInstantiationResult {
    Reused(Box<SuccessReusedTemplateInstanceResult>),
    Created(Box<SuccessCreatedTemplateInstanceResult>),
}

pub struct SuccessReusedTemplateInstanceResult {
    pub application: InstantiatedTemplateObj,
}

pub struct SuccessCreatedTemplateInstanceResult {
    pub application: InstantiatedTemplateObj,
    pub template_argument_results: Vec<SuccessVerifyTemplateHeaderArgumentResult>,
    pub template_domain_results: Vec<SuccessVerifyTemplateDomainResult>,
    pub surface_equality: SuccessStoreFactResult,
    pub body_statement_result: Box<SuccessStmtResult>,
    pub public_value_equalities: Vec<SuccessStoreFactResult>,
    pub supplemental_stores: Vec<SuccessStoreFactResult>,
    pub registered_set_builder: Option<SetBuilder>,
}

pub struct SuccessVerifyTemplateHeaderArgumentResult {
    pub argument_index: usize,
    pub argument: Obj,
    pub expected_type: ParamType,
    pub verification: SuccessVerifyFactForObjWellDefinedResult,
}

#[derive(Debug)]
pub struct SuccessVerifyTemplateDomainResult {
    pub domain_index: usize,
    pub proof: SuccessVerifyFactForObjWellDefinedResult,
    pub store: SuccessStoreFactResult,
}

impl fmt::Debug for SuccessCreatedTemplateInstanceResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessCreatedTemplateInstanceResult")
            .field("application", &self.application.to_string())
            .field("template_argument_results", &self.template_argument_results)
            .field("template_domain_results", &self.template_domain_results)
            .field("surface_equality", &self.surface_equality)
            .field("body_statement_result", &self.body_statement_result)
            .field("public_value_equalities", &self.public_value_equalities)
            .field("supplemental_stores", &self.supplemental_stores)
            .field(
                "registered_set_builder",
                &self
                    .registered_set_builder
                    .as_ref()
                    .map(ToString::to_string),
            )
            .finish()
    }
}

impl fmt::Debug for SuccessReusedTemplateInstanceResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessReusedTemplateInstanceResult")
            .field("application", &self.application.to_string())
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyTemplateHeaderArgumentResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyTemplateHeaderArgumentResult")
            .field("argument_index", &self.argument_index)
            .field("argument", &self.argument.to_string())
            .field("expected_type", &self.expected_type.to_string())
            .field("verification", &self.verification)
            .finish()
    }
}
