//! Proofs selected by definition expansion.

use crate::prelude::*;
use std::fmt;

pub struct SuccessVerifyByDefinitionResult {
    pub prop: String,
    /// Exact concrete predicate definition selected by execution. Builtin
    /// definitions use `None` and are lowered by their own typed evidence.
    pub definition: Option<DefPropStmt>,
    pub arguments: Vec<String>,
    pub definition_clauses: Vec<String>,
    pub stored_fact: String,
    pub concrete_user_prop: bool,
    pub definition_clause_facts: Vec<Fact>,
    pub argument_verification: Option<Box<SuccessVerifyArgsSatisfyParamDefResult>>,
    pub clause_checks: Vec<StmtResult>,
}

impl fmt::Debug for SuccessVerifyByDefinitionResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByDefinitionResult")
            .field("prop", &self.prop)
            .field(
                "definition",
                &self.definition.as_ref().map(ToString::to_string),
            )
            .field("arguments", &self.arguments)
            .field("definition_clauses", &self.definition_clauses)
            .field("stored_fact", &self.stored_fact)
            .field("concrete_user_prop", &self.concrete_user_prop)
            .field("definition_clause_facts", &self.definition_clause_facts)
            .field("argument_verification", &self.argument_verification)
            .field("clause_checks", &self.clause_checks)
            .finish()
    }
}

impl SuccessVerifyByDefinitionResult {
    pub fn new(
        prop: String,
        definition: Option<DefPropStmt>,
        arguments: Vec<String>,
        definition_clauses: Vec<String>,
        stored_fact: String,
        concrete_user_prop: bool,
        definition_clause_facts: Vec<Fact>,
        argument_verification: Option<SuccessVerifyArgsSatisfyParamDefResult>,
        clause_checks: Vec<StmtResult>,
    ) -> Self {
        SuccessVerifyByDefinitionResult {
            prop,
            definition,
            arguments,
            definition_clauses,
            stored_fact,
            concrete_user_prop,
            definition_clause_facts,
            argument_verification: argument_verification.map(Box::new),
            clause_checks,
        }
    }
}
