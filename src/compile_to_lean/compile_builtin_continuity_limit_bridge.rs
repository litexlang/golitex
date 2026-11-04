//! Replay the checked continuity/limit bridge and its independent hypotheses.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::multivariable::helper as schema;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    PredicateDomainProof, PredicateDomainRequirementProof,
};
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
};

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("ContinuityLimitBridge/{stage}"))
}
fn candidate<'a>(
    fact: &'a Fact,
    predicate: &str,
    args: &[Obj],
) -> Result<&'a MultivariableAnalysisRelation, LeanCompileError> {
    let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(f)) = fact else {
        return Err(invalid("PositiveCandidate"));
    };
    let r = &f.relation;
    if r.predicate_name() != predicate
        || r.argument_refs().len() != args.len()
        || !r
            .argument_refs()
            .iter()
            .zip(args)
            .all(|(a, b)| a.ir() == b.ir())
    {
        return Err(invalid("CandidateArguments"));
    }
    Ok(r)
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_continuity_limit_bridge(
        &self,
        call: &TheoremCall,
        builtin: &BuiltinThmApplication,
        derivation: &TheoremDerivationProof,
        type_proofs: &[VerifyFactResult],
        type_stores: &[StoreFactAndInferResult],
        function_domain: Option<&BuiltinFunctionDomainProof>,
        dom_proofs: &[VerifyFactResult],
        dom_stores: &[StoreFactAndInferResult],
        conclusions_wd: &[FactWellDefinedProof],
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, String, Vec<Fact>), LeanCompileError> {
        use BuiltinTheoremId::*;
        let (forward, vector, law) = match builtin.theorem {
            MultiContinuousAtLimit => (true, false, "scalarContinuityToMultivariableLimit"),
            MultiLimitAtContinuous => (false, false, "scalarMultivariableLimitToContinuity"),
            VectorContinuousAtLimit => (true, true, "vectorContinuityToMultivariableLimit"),
            VectorLimitAtContinuous => (false, true, "vectorMultivariableLimitToContinuity"),
            _ => return Err(invalid("Identity")),
        };
        let base = 4 + usize::from(vector);
        let count = base + 3;
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || args.len() != builtin.theorem.arity()
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("OriginalStages"));
        }
        let cont = if vector {
            "is_vector_continuous_at"
        } else {
            "is_multi_continuous_at"
        };
        let limit = if vector {
            "has_vector_limit_at"
        } else {
            "has_multi_limit_at"
        };
        let index = base + usize::from(forward);
        let r = candidate(
            &builtin.requirements[index],
            if forward { cont } else { limit },
            args,
        )?;
        let mut expected = args.clone();
        let at_point = schema::apply(&args[0], vec![args[1].clone()]);
        if forward {
            expected.push(at_point.clone());
        } else {
            expected.pop();
        }
        let output = candidate(
            &builtin.conclusions[0],
            if forward { limit } else { cont },
            &expected,
        )?;
        let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(rules))) =
            &dom_stores[index].infer
        else {
            return Err(invalid("OriginalInference"));
        };
        let [InferMultivariableAnalysisFactResult::Definition(infer)] = rules.as_slice() else {
            return Err(invalid("OriginalInference"));
        };
        if infer.source_fact_id != builtin.requirements[index].fact_id()
            || infer.derived.len() != if forward { 1 } else { 3 }
        {
            return Err(invalid("OriginalInferenceIdentity"));
        }
        let source = infer
            .function_domain
            .as_ref()
            .ok_or_else(|| invalid("OriginalCompleteDomain"))?;
        let domain =
            schema::actual_domain(&source.signature).ok_or_else(|| invalid("ActualDomain"))?;
        let req = &builtin.requirements;
        super::compile_multivariable_limit_context::validate_limit_context(
            args,
            &req[..base],
            source,
            vector.then(|| &args[3]),
        )?;
        if forward {
            super::compile_builtin_derivative_schema::validate_context(
                r,
                &req[..base + 1],
                source,
            )?;
            let protected: Vec<_> = args.iter().chain([&domain, &at_point]).collect();
            super::compile_multivariable_scalar_limit::validate_accumulation(
                &req[base + 2],
                &domain,
                &args[1],
                &args[2],
                &protected,
            )?;
        } else {
            let mut context = req[..base].to_vec();
            context.push(req[base + 1].clone());
            super::compile_builtin_derivative_schema::validate_context(output, &context, source)?;
            if !matches!(&req[base+2],Fact::AtomicFact(AtomicFact::EqualFact(eq))
                if eq.left.ir()==at_point.ir() && eq.right.ir()==args.last().unwrap().ir())
            {
                return Err(invalid("OriginalPointValueEquality"));
            }
        }
        let Fact::AtomicFact(atomic) = &builtin.conclusions[0] else {
            unreachable!()
        };
        let FactWellDefinedProof::AtomicExceptEquality(wd) = &conclusions_wd[0] else {
            return Err(invalid("OriginalFormation"));
        };
        let PredicateDomainProof::MultivariableAnalysis(capture) = &wd
            .as_detailed()
            .map_err(|_| invalid("DetailedFormation"))?
            .predicate_domain
        else {
            return Err(invalid("OriginalFormationDomain"));
        };
        if capture.requirements.len()!=base+1 || !req[..base].iter()
            .zip(&capture.requirements[..base]).all(|(a,b)|
                crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::quantifier_free_source_facts_alpha_equal(a,&b.requirement)) {
            return Err(invalid("OriginalFormationContext"));
        }
        let last = &capture.requirements[base];
        let value_member = if forward {
            let carrier = schema::value_carrier(output);
            if !matches!(&last.requirement,Fact::AtomicFact(AtomicFact::InFact(m))
                if m.element.ir()==at_point.ir() && m.set.ir()==carrier.ir())
            {
                return Err(invalid("OriginalPointValueCarrier"));
            }
            let PredicateDomainRequirementProof::Verified(proof) = &last.result else {
                return Err(invalid("OriginalPointValueProof"));
            };
            if source_subject(proof)? != last.requirement {
                return Err(invalid("OriginalPointValueSubject"));
            }
            Some(last.requirement.fact_id())
        } else {
            if !crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::quantifier_free_source_facts_alpha_equal(&req[base+1],&last.requirement) {
                return Err(invalid("OriginalFormationPointDomain"));
            }
            None
        };
        let mut definitions = Vec::new();
        for (i, ((fact, proof), stored)) in req.iter().zip(dom_proofs).zip(dom_stores).enumerate() {
            if source_subject(proof)? != *fact {
                return Err(invalid("OriginalProofSubject"));
            }
            let prior = SourcePosition {
                before: i,
                ..*position
            };
            let compiled = self.compile_verify(proof, &prior)?;
            self.validate_store(&stored.store, fact)?;
            definitions.push(self.emit_internal_fact(fact, &compiled, &prior)?);
            definitions.extend(self.compile_stored_inferences(
                stored,
                fact,
                &(compiled.0, format!("h_{}", fact.fact_id().value())),
                &SourcePosition {
                    before: i + 1,
                    ..*position
                },
            )?);
        }
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], &builtin.conclusions[0], &formed)?;
        let bindings = self.compile_atomic_wd_locals(wd, atomic, &formed)?;
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::AtomicWDLocals(wd, expected.len()),
            usize::MAX,
        );
        let objects = args
            .iter()
            .map(|o| self.compile_object_reference(o, &scope))
            .collect::<Result<Vec<_>, _>>()?;
        let raw = objects
            .iter()
            .map(|o| format!("(Litex.denote {o})"))
            .collect::<Vec<_>>()
            .join(" ");
        let (view, equal) = self.compile_multivariable_limit_view(&args[0], source, &scope)?;
        let hc = format!("h_{}", req[index].fact_id().value());
        let proof = if forward {
            format!("(by\n{view}\n  apply Litex.{law} {raw} h_{} {hc}\n  intro radius h_radius\n  obtain ⟨input,hi,hpos,hclose⟩ := h_{} (Litex.semanticObject radius (M.member_isSet h_radius)) h_radius\n  exact ⟨input,{equal} ▸ hi,hpos,hclose⟩\n)",value_member.unwrap().value(),req[base+2].fact_id().value())
        } else {
            let function = self.compile_euclidean_limit_function_context(
                args,
                &req[..base],
                source,
                vector.then(|| &args[3]),
                &scope,
            )?;
            format!("(by\n{view}\n{function}\n  exact Litex.{law} {raw} _multivariable_real (Litex.inNPos_natural {} h_{}) h_{} {hc} h_{}\n)",objects[2],req[0].fact_id().value(),req[base-1].fact_id().value(),req[base+2].fact_id().value())
        };
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        let proof = Self::scope_equal_wd_proof(statement.clone(), proof, &bindings);
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}
