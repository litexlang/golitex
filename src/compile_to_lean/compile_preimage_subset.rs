use super::compile_function_preimage::preimage_parts;
use super::source_position::SourcePosition;
use super::{LeanCompileError,LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::subset::FunctionPreimageSubsetOfInputCarrierBuiltinRuleProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_preimage_subset(
        &self,
        fact: &SubsetFact,
        proof: &FunctionPreimageSubsetOfInputCarrierBuiltinRuleProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (_, _, set_target) = preimage_parts(&fact.left)?;
        let (hf, checked) = self.compile_preimage_construction(
            &fact.left,
            &proof.construction,
            &position.atomic_search_prior(0)?,
        )?;
        let complete = position.atomic_search_prior(1)?;
        let EqualFactSearchedProof::ByTheyAreTheSame(p) = &proof.carrier_match else {
            return Err(LeanCompileError::unsupported("PreimageSubset/CarrierMatch"));
        };
        let same = self.compile_identity(
            &proof.construction.builder.param_set,
            &fact.right,
            p,
            &complete,
        )?;
        let signature = &proof.construction.source.signature;
        let sig = self.compile_fn_signature(signature, &complete)?;
        let root = self.compile_object_reference(&fact.left, &complete)?;
        let target = self.compile_object_reference(&fact.right, &complete)?;
        let law = if set_target {
            "preimageSetMembers"
        } else {
            "preimageMembers"
        };
        let (lines, _, _) =
            self.compile_preimage_domain_parts(signature, "_preimage_input", &complete)?;
        Ok(format!("(by\n  let _preimage := {root}\n  let _preimage_builder := {checked}\n  change Litex.Subset _preimage {target}\n  intro _preimage_input _preimage_member\n  have _preimage_domain := ((Litex.{law} _preimage {sig} {hf} _preimage_input).mp _preimage_member).1\n  {}\n  exact Eq.mp (congrArg (M.mem _preimage_input) {same}) _preimage_base)",lines.join("\n  ")))
    }
}
