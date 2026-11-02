use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::{
    ExecHaveObjByExistFactsStmtResult, ExecObtainObjFromAtomicFactStmtResult,
    ExecObtainObjFromExistFactStmtResult, ObtainExistVerifySuccess,
};
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    /// Preserve the canonical witness carrier and every existential proof
    /// binder. The ordinary body dispatcher checks the original existence WD.
    pub(super) fn compile_template_obtain_raw_value(
        &self,
        body: &ExecStmtResult,
        output_index: usize,
        position: &SourcePosition<'_>,
        bindings: &HashMap<IdentifierId, String>,
    ) -> Result<String, LeanCompileError> {
        let source = match body {
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::HaveObjByExistFacts(
                    ExecHaveObjByExistFactsStmtResult::Success(p),
                ),
            )) => {
                let ExistShapedFact::Exist(source) = &p.verify_exist.fact else {
                    return Err(LeanCompileError::unsupported("Template/RawWitnessBody"));
                };
                if source.typed_parameters != p.statement.param_def
                    || source.facts != p.statement.facts
                {
                    return Err(LeanCompileError::unsupported("Template/RawWitnessSubject"));
                }
                source
            }
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::ObtainObjFromExistFact(
                    ExecObtainObjFromExistFactStmtResult::Success(p),
                ),
            )) => {
                let source = match &p.verify_exist {
                    ObtainExistVerifySuccess::Exist(proof) => &proof.fact,
                    ObtainExistVerifySuccess::ExistUnique(proof) => &proof.fact,
                };
                if source != &p.statement.fact {
                    return Err(LeanCompileError::unsupported("Template/RawWitnessSubject"));
                }
                source.plain()
            }
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::ObtainObjFromAtomicFact(
                    ExecObtainObjFromAtomicFactStmtResult::Success(p),
                ),
            )) => p.projected_exist.plain(),
            _ => return Err(LeanCompileError::unsupported("Template/RawWitnessBody")),
        };
        if output_index >= source.typed_parameters.ordered_param_ids().len() {
            return Err(LeanCompileError::unsupported("Template/RawWitnessArity"));
        }
        // Select a joint witness in the same order as ordinary obtain replay.
        // Each suffix retains all later binders and clauses, so components are
        // never chosen from independent existential projections.
        let mut remaining = source.clone();
        let mut captured = bindings.clone();
        let mut definitions = Vec::new();
        for index in 0..=output_index {
            let parameter = &remaining.typed_parameters.groups[0].params[0];
            let id = parameter.id;
            let predicate =
                self.compile_exist_raw_witness_predicate(&remaining, position, &captured)?;
            let value = format!("(Litex.obtainedValue (M := M) {predicate})");
            if output_index == 0 {
                return Ok(value);
            }
            let name = format!("_template_witness_i{}", id.value());
            definitions.push(format!("let {name} := {value}"));
            if index == output_index {
                return Ok(format!("({}; {name})", definitions.join("; ")));
            }
            captured.insert(id, name);
            remaining.typed_parameters.groups[0].params.remove(0);
            if remaining.typed_parameters.groups[0].params.is_empty() {
                remaining.typed_parameters.groups.remove(0);
            }
        }
        unreachable!()
    }
}
