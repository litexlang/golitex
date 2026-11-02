//! Replay the selected original empty complete-domain graph certificate.
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_domain::FunctionDomainEmptyProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_empty_function_graph::EmptyFunctionGraphBuiltinRuleProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_function_graph_empty(
        &self,
        goal: &EqualFact,
        proof: &EmptyFunctionGraphBuiltinRuleProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (function, reverse) = match (&goal.left, &goal.right) {
            (function, Obj::SetFormer(SetFormer::ListSet(empty))) if empty.list.is_empty() => {
                (function, false)
            }
            (Obj::SetFormer(SetFormer::ListSet(empty)), function) if empty.list.is_empty() => {
                (function, true)
            }
            _ => return Err(LeanCompileError::unsupported("FnGraphEmpty/Endpoints")),
        };
        let signature = match &proof.domain_empty {
            FunctionDomainEmptyProof::ParameterCarrier(p) => &p.signature,
            FunctionDomainEmptyProof::GuardExclusion(p) => &p.signature,
        };
        if signature != &proof.source.signature {
            return Err(LeanCompileError::unsupported(
                "FnGraphEmpty/OriginalSignature",
            ));
        }
        let member = self.compile_complete_domain_member(function, &proof.source, position)?;
        let formed = SourcePosition::new(
            Some(position),
            SourceOwner::CompleteDomainSource(&proof.source),
            usize::MAX,
        );
        let compiled = self.compile_complete_domain_signature(&proof.source, &formed)?;
        let function = self.compile_object_reference(function, &formed)?;
        let empty = self.compile_complete_function_empty_domain(
            &proof.source,
            &proof.domain_empty,
            &compiled,
            position,
            &formed,
        )?;
        let term = format!(
            "(Litex.functionGraphEmptyOfDomainEmpty {function} {compiled} {member} {empty})"
        );
        Ok(if reverse {
            format!("({term}).symm")
        } else {
            term
        })
    }
}
