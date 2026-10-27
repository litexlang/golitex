//! Automatic function-space membership shares the explicit theorem's replay.
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_strategy::result::FunctionSetMembershipStrategySingleStep;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_function_set_strategy(
        &self,
        fact: &AtomicFact,
        proof: &FunctionSetMembershipStrategySingleStep,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::InFact(member) = fact else {
            return Err(LeanCompileError::unsupported("FunctionSetStrategy/Subject"));
        };
        self.validate_function_carrier_signature(&member.set, &proof.domain.target)?;
        ensure_object(&member.element, &proof.domain.function_wd)?;
        ensure_object(
            &Obj::FunctionSpace(FunctionSpace::FnSet(proof.domain.target.clone())),
            &proof.domain.target_wd,
        )?;
        if proof.requirement_facts.len() != proof.proof_of_requirement_facts.len() {
            return Err(LeanCompileError::unsupported("FunctionSetStrategy/Stages"));
        }
        let scope = SourcePosition::new(
            Some(position),
            SourceOwner::FunctionDomainWD(&proof.domain),
            0,
        );
        let function = self.compile_wd(&proof.domain.function_wd, &scope)?;
        let target = self.compile_wd(
            &proof.domain.target_wd,
            &SourcePosition { before: 1, ..scope },
        )?;
        let mut lines = vec![
            format!("let _membership_function := {function}"),
            format!("let _membership_target := {target}"),
        ];
        let (comparisons, equality) =
            self.compile_function_domain_match(&proof.domain, position)?;
        lines.extend(comparisons);
        let completed = SourcePosition {
            before: usize::MAX,
            ..scope
        };
        let search = SourcePosition {
            parent: Some(&completed),
            ..*position
        };
        let mut references = Vec::new();
        for (index, (fact, checked)) in proof
            .requirement_facts
            .iter()
            .zip(&proof.proof_of_requirement_facts)
            .enumerate()
        {
            if source_subject(checked)? != *fact {
                return Err(LeanCompileError::unsupported("FunctionSetStrategy/Premise"));
            }
            let compiled = self.compile_verify(checked, &search.atomic_search_prior(index)?)?;
            let name = format!("h_{}", fact.fact_id().value());
            lines.push(format!("have {name} : {} := {}", compiled.0, compiled.1));
            references.push(name);
        }
        let body = self.compile_builtin_function_membership(
            member,
            &proof.domain,
            &equality,
            &proof.requirement_facts,
            &references,
            &search,
        )?;
        lines.push(format!("exact {body}"));
        Ok(format!(
            "(by\n  {})",
            lines.join("\n").replace('\n', "\n  ")
        ))
    }
}
