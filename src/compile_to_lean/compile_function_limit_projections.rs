//! Eliminate a recorded candidate using its own domain and WD prefix.
use super::compile_function_limit::{finite_side, infinite_direction};
use super::compile_function_limit_definition::{
    signature_domain_matches, validate_accumulation_clause, validate_control_clause,
};
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("FunctionLimitProjection/{stage}"))
}

impl LitexToLeanCompiler {
    pub(super) fn compile_function_limit_projection(
        &self,
        goal: &Fact,
        requirements: &[Fact],
        checked: &VerifyFactResult,
        candidate_index: usize,
        epsilon: Option<&Obj>,
        references: &[String],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let VerifyFactResult::AtomicExceptEquality(checked) = checked else {
            return Err(invalid("CandidateProof"));
        };
        let VerifyAtomicExceptEqualityFactResult::Success(checked) = checked.as_ref() else {
            return Err(invalid("CandidateProof"));
        };
        let AtomicFact::HasFunctionLimitFact(candidate) = &checked.fact else {
            return Err(invalid("Candidate"));
        };
        let domain = if let Some(epsilon) = epsilon {
            let Fact::ExistFact(exists) = goal else {
                return Err(invalid("ControlExistence"));
            };
            let [QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(subset))] =
                exists.facts.as_slice()
            else {
                return Err(invalid("ControlInclusion"));
            };
            let Obj::SetFormer(SetFormer::SetBuilder(neighborhood)) = &subset.left else {
                return Err(invalid("ControlNeighborhood"));
            };
            let domain = neighborhood.param_set.as_ref();
            validate_control_clause(candidate, domain, epsilon, exists)?;
            domain
        } else {
            validate_accumulation_clause(candidate, goal)?
        };
        let Fact::AtomicFact(AtomicFact::InFact(member)) = &requirements[0] else {
            return Err(invalid("FunctionMembership"));
        };
        let Obj::FunctionSpace(FunctionSpace::FnSet(signature_source)) = &member.set else {
            return Err(invalid("Signature"));
        };
        if !signature_domain_matches(domain, signature_source) {
            return Err(invalid("EffectiveDomain"));
        }
        let signature = format!(
            "({}).val",
            self.compile_object_reference(&member.set, position)?
        );
        let (view, equality) = self.compile_verified_limit_domain_view(
            &candidate.function,
            domain,
            signature_source,
            &signature,
            &references[0],
            position,
        )?;
        let function = self.compile_object_reference(&candidate.function, position)?;
        let value = self.compile_object_reference(&candidate.value, position)?;
        let (prefix, arguments, finite) = if candidate.approach.point().is_some() {
            let (side, point) = finite_side(&candidate.approach)?;
            (
                "finite",
                format!(
                    ".{side} {function} {} {value} _domain",
                    self.compile_object_reference(point, position)?
                ),
                true,
            )
        } else {
            (
                "infinite",
                format!(
                    ".{} {function} {value} _domain",
                    infinite_direction(&candidate.approach)?
                ),
                false,
            )
        };
        let proof = &references[candidate_index];
        let (extra, body) = if let Some(epsilon) = epsilon {
            let epsilon = self.compile_object_reference(epsilon, position)?;
            let member = &references[candidate_index + 1];
            (format!("  have _control_real_domain : Litex.RealFunctionValue M (Litex.denote {function}) := by\n    refine ⟨_signature, _member, ?_, {}⟩\n    intro x hx\n    exact {} x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1\n", references[2], references[1]),
                format!("  obtain ⟨_limit_threshold, _limit_threshold_member, _limit_control⟩ := Litex.{prefix}FunctionLimitControl {arguments} _control_real_domain {equality} {proof} {epsilon} {member}\n  refine ⟨_limit_threshold, _limit_threshold_member, ?_⟩\n  exact _limit_control"))
        } else {
            let result = if finite {
                "⟨_limit_input, _limit_input_member, _limit_positive, _limit_near⟩"
            } else {
                "⟨_limit_input, _limit_input_member, _limit_beyond⟩"
            };
            (String::new(), format!("  intro _Host _rep _limit_radius _limit_radius_member\n  obtain {result} := Litex.{prefix}FunctionLimitAccumulation {arguments} {equality} {proof} _limit_radius _limit_radius_member\n  exact {result}"))
        };
        Ok(format!("(by\n{view}\n{extra}{body}\n)"))
    }
}
