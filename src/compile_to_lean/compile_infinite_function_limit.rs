//! The two infinity markers carry no point WD; retain their exact direction.
use super::compile_function_limit::infinite_direction;
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_limit::FunctionConvergenceProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactSearchedProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::FunctionLimitApproachRealProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    FunctionLimitApproachWellDefinedProof, FunctionLimitObjWellDefinedProof,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_infinite_function_limit_wd(
        &self,
        object: &FunctionLimit,
        proof: &FunctionLimitObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let direction = infinite_direction(&object.approach)?;
        if !matches!(
            (&object.approach, &proof.approach_wd, &proof.approach_real),
            (
                LimitApproach::AtPositiveInfinity,
                FunctionLimitApproachWellDefinedProof::AtPositiveInfinity,
                FunctionLimitApproachRealProof::AtPositiveInfinity
            ) | (
                LimitApproach::AtNegativeInfinity,
                FunctionLimitApproachWellDefinedProof::AtNegativeInfinity,
                FunctionLimitApproachRealProof::AtNegativeInfinity
            )
        ) {
            return Err(LeanCompileError::unsupported(
                "FunctionLimit/InfinityMarkers",
            ));
        }
        ensure_object(&object.function, &proof.function_wd)?;
        let function = self.compile_wd(&proof.function_wd, position)?;
        let domain =
            self.compile_real_function_domain(&object.function, &proof.function_domain, position)?;
        let convergence = match &proof.convergence {
            FunctionConvergenceProof::Candidate(p) => {
                let AtomicFact::HasFunctionLimitFact(f) = &p.fact else {
                    return Err(LeanCompileError::unsupported("FunctionLimit/Candidate"));
                };
                if f.function.ir() != object.function.ir() || f.approach != object.approach {
                    return Err(LeanCompileError::unsupported(
                        "FunctionLimit/CandidateSubject",
                    ));
                }
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(citation) =
                    p.searched_proof.as_ref()
                else {
                    return Err(LeanCompileError::unsupported(
                        "FunctionLimit/CandidateCitation",
                    ));
                };
                let known = self.compile_known_atomic(citation, &p.fact, position)?;
                format!("(Litex.infiniteFunctionConvergentOfCandidate .{direction} _function {} {known})", self.compile_object_reference(&f.value, position)?)
            }
            FunctionConvergenceProof::Existence { fact, proof } => {
                super::compile_function_limit_definition::validate_limit_existence(
                    &object.function,
                    &object.approach,
                    fact,
                )?;
                if source_subject(proof)? != *fact {
                    return Err(LeanCompileError::unsupported(
                        "FunctionLimit/ExistenceSubject",
                    ));
                }
                let (ty, term) = self.compile_verify(proof, position)?;
                format!("(Litex.infiniteFunctionConvergentOfExistence .{direction} _function (show {ty} from {term}))")
            }
        };
        Ok(format!("(let _function := {function}; Litex.infiniteFunctionLimit .{direction} _function {domain} {convergence})"))
    }
}
