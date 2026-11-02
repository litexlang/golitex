//! Replay the two original section/remainder clauses, including their formation.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    PredicateDomainProof, PredicateDomainRequirementProof,
};
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
};
use std::collections::HashMap;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("RemainderDefinition/{stage}"))
}
fn relation(f: &Fact) -> Result<&MultivariableAnalysisRelation, LeanCompileError> {
    let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(f)) = f else {
        return Err(invalid("PositiveCandidate"));
    };
    Ok(&f.relation)
}
fn clauses<'a>(
    r: &MultivariableAnalysisRelation,
    domain: &Obj,
    facts: &'a [Fact],
) -> Result<Option<&'a Obj>, LeanCompileError> {
    match r {
        MultivariableAnalysisRelation::PartialDerivativeAt(r) => {
            super::compile_partial_derivative::clauses(r, domain, facts).map(Some)
        }
        MultivariableAnalysisRelation::ScalarDifferentialAt(r) => {
            super::compile_scalar_differential::validate_differential_clauses(
                &r.function,
                &r.point,
                &r.dimension,
                None,
                &r.value,
                domain,
                facts,
            )?;
            Ok(None)
        }
        MultivariableAnalysisRelation::TotalDerivativeAt(r) => {
            super::compile_scalar_differential::validate_differential_clauses(
                &r.function,
                &r.point,
                &r.input_dimension,
                Some(&r.output_dimension),
                &r.value,
                domain,
                facts,
            )?;
            Ok(None)
        }
        _ => Err(invalid("Family")),
    }
}
impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_remainder_definition(
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
        let (fold, predicate, law, context) = match builtin.theorem {
            PartialAtFromDefinition => (
                true,
                "has_partial_derivative_at",
                "partialDerivativeOfClauses",
                6,
            ),
            PartialAtToDefinition => (
                false,
                "has_partial_derivative_at",
                "partialDerivativeClauses",
                6,
            ),
            ScalarDifferentialAtFromDefinition => (
                true,
                "has_scalar_differential_at",
                "scalarDifferentialOfClauses",
                5,
            ),
            ScalarDifferentialAtToDefinition => (
                false,
                "has_scalar_differential_at",
                "scalarDifferentialClauses",
                5,
            ),
            TotalDerivativeAtFromDefinition => (
                true,
                "has_total_derivative_at",
                "totalDifferentialOfClauses",
                6,
            ),
            TotalDerivativeAtToDefinition => (
                false,
                "has_total_derivative_at",
                "totalDifferentialClauses",
                6,
            ),
            _ => return Err(invalid("Identity")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let count = context + if fold { 2 } else { 1 };
        let outputs = if fold { 1 } else { 2 };
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
            || builtin.conclusions.len() != outputs
            || conclusions_wd.len() != outputs
        {
            return Err(invalid("OriginalStages"));
        }
        let r = relation(if fold {
            &builtin.conclusions[0]
        } else {
            &builtin.requirements[context]
        })?;
        if r.predicate_name() != predicate
            || r.argument_refs().len() != args.len()
            || !r
                .argument_refs()
                .iter()
                .zip(args)
                .all(|(a, b)| a.ir() == b.ir())
        {
            return Err(invalid("OriginalArguments"));
        }
        let mut value_member = None;
        let source = if fold {
            let FactWellDefinedProof::AtomicExceptEquality(wd) = &conclusions_wd[0] else {
                return Err(invalid("OriginalFormation"));
            };
            let PredicateDomainProof::MultivariableAnalysis(capture) = &wd
                .as_detailed()
                .map_err(|_| invalid("DetailedFormation"))?
                .predicate_domain
            else {
                return Err(invalid("OriginalDomain"));
            };
            if capture.requirements.len()!=context+1||!builtin.requirements[..context].iter().zip(&capture.requirements[..context]).all(|(a,b)|crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::quantifier_free_source_facts_alpha_equal(a,&b.requirement)){return Err(invalid("OriginalContext"));}
            let member = &capture.requirements[context];
            let carrier =
                crate::execute::execute_fact_stmt::multivariable::helper::value_carrier(r);
            if !matches!(&member.requirement,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==args.last().unwrap().ir()&&f.set.ir()==carrier.ir())
            {
                return Err(invalid("ValueCarrier"));
            }
            let PredicateDomainRequirementProof::Verified(proof) = &member.result else {
                return Err(invalid("ValueProof"));
            };
            if source_subject(proof)? != member.requirement {
                return Err(invalid("ValueProofSubject"));
            }
            value_member = Some(proof);
            &capture.function_domain
        } else {
            let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(
                rules,
            ))) = &dom_stores[context].infer
            else {
                return Err(invalid("OriginalInference"));
            };
            let [InferMultivariableAnalysisFactResult::Definition(capture)] = rules.as_slice()
            else {
                return Err(invalid("OriginalInference"));
            };
            if capture.source_fact_id != builtin.requirements[context].fact_id()
                || capture.derived.len() != 3
            {
                return Err(invalid("OriginalInferenceIdentity"));
            }
            capture
                .function_domain
                .as_ref()
                .ok_or_else(|| invalid("OriginalCompleteDomain"))?
        };
        super::compile_builtin_derivative_schema::validate_context(
            r,
            &builtin.requirements[..context],
            source,
        )?;
        let domain = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
            &source.signature,
        )
        .ok_or_else(|| invalid("ActualDomain"))?;
        let quotient = clauses(
            r,
            &domain,
            if fold {
                &builtin.requirements[context..]
            } else {
                &builtin.conclusions
            },
        )?;
        let mut definitions = Vec::new();
        for (index, ((fact, checked), store)) in builtin
            .requirements
            .iter()
            .zip(dom_proofs)
            .zip(dom_stores)
            .enumerate()
        {
            if source_subject(checked)? != *fact {
                return Err(invalid("OriginalProofSubject"));
            }
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let compiled = self.compile_verify(checked, &prior)?;
            self.validate_store(&store.store, fact)?;
            definitions.push(self.emit_internal_fact(fact, &compiled, &prior)?);
            definitions.extend(self.compile_stored_inferences(
                store,
                fact,
                &(compiled.0, format!("h_{}", fact.fact_id().value())),
                &SourcePosition {
                    before: index + 1,
                    ..*position
                },
            )?);
        }
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        for (f, w) in builtin.conclusions.iter().zip(conclusions_wd) {
            self.compile_fact_wd(w, f, &formed)?;
        }
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let raw = args
            .iter()
            .map(|o| self.compile_function_raw_expression_bound(o, &scope, &HashMap::new()))
            .collect::<Result<Vec<_>, _>>()?;
        let all = raw.join(" ");
        let point = &raw[1];
        let n = &raw[2];
        let value = raw.last().unwrap();
        let (view, equal) = self.compile_multivariable_limit_view(&args[0], source, &scope)?;
        let original = format!("h_{}", builtin.requirements[context].fact_id().value());
        let statements = builtin
            .conclusions
            .iter()
            .zip(conclusions_wd)
            .map(|(f, w)| self.compile_formed_fact_proposition(w, f, &formed))
            .collect::<Result<Vec<_>, _>>()?;
        let partial = if let MultivariableAnalysisRelation::PartialDerivativeAt(r) = r {
            Some(r)
        } else {
            None
        };
        let quotient_data = if let Some(r) = partial {
            let q = quotient.ok_or_else(|| invalid("Quotient"))?;
            let matching = self.partial_quotient_match(r, q, &equal, &scope)?;
            let Obj::FunctionSpace(FunctionSpace::AnonymousFn(q)) = q else {
                return Err(invalid("QuotientLiteral"));
            };
            let q = self.compile_function_literal_value(
                q,
                &scope,
                &self.partial_raw_bindings(r, &scope)?,
            )?;
            Some((q, matching))
        } else {
            None
        };
        let proof = if let Some(member) = value_member {
            let FactWellDefinedProof::AtomicExceptEquality(wd) = &conclusions_wd[0] else {
                unreachable!()
            };
            let stage = SourcePosition::new(
                Some(&formed),
                SourceOwner::AtomicWD(wd),
                args.len() + context,
            );
            let member = self.compile_verify(member, &stage)?.1;
            let second = format!("h_{}", builtin.requirements[context + 1].fact_id().value());
            if let Some((q, matching)) = &quotient_data {
                let axis = &raw[3];
                format!("(by\n{view}\n{matching}\n  have _original_limit : Litex.HasFiniteFunctionLimitValue M .both {q} (M.number 0) {value} := {second}\n  apply Litex.{law} {all} {member}\n  · obtain ⟨radius,hr,hcontrol⟩ := {original}\n    refine ⟨radius,hr,?_⟩\n    intro h hR hsmall\n    have h_source := ((Litex.SetSemantics.sep_members _ _ _).mp (hcontrol h ((Litex.SetSemantics.sep_members _ _ _).mpr ⟨hR,hR,hsmall⟩))).2.2\n    exact (congrArg (fun D => M.mem (Litex.coordinatePathValue {point} {n} {axis} h) D) {equal}).mp h_source\n  · exact (congrArg (fun q => Litex.HasFiniteFunctionLimitValue M .both q (M.number 0) {value}) _partial_quotient_match).mp _original_limit\n)")
            } else {
                format!("(by\n{view}\n  apply Litex.{law} {all} {member}\n  · obtain ⟨radius,hr,hcontrol⟩ := {original}\n    refine ⟨radius,hr,?_⟩\n    intro input hi hclose\n    exact {equal} ▸ hcontrol input ((Litex.SetSemantics.sep_members _ _ _).mpr ⟨hi,hi,hclose⟩)\n  · intro epsilon h_epsilon\n    obtain ⟨delta,hd,hcontrol⟩ := {second} (Litex.semanticObject epsilon (M.member_isSet h_epsilon)) h_epsilon\n    refine ⟨delta,hd,?_⟩\n    intro input hi hpos hclose\n    have hi : M.mem input _multivariable_source_domain := {equal}.symm ▸ hi\n    have good := hcontrol input ((Litex.SetSemantics.sep_members _ _ _).mpr ⟨hi,hi,hpos,hclose⟩)\n    exact ((Litex.SetSemantics.sep_members _ _ _).mp good).2.2\n)")
            }
        } else {
            let begin = format!("(by\n{view}\n  have _clauses := Litex.{law} {all} {original}\n");
            let (first, second) = if let Some((q, matching)) = &quotient_data {
                let function = self.compile_object_reference(&args[0], &scope)?;
                let first=format!("{begin}  obtain ⟨radius,hr,hcontrol⟩ := _clauses.1\n  refine ⟨radius,hr,?_⟩\n  change ∀ h : M.Value, M.mem h _ → M.mem h _\n  intro h h_near\n  obtain ⟨hR,_,hsmall⟩ := (Litex.SetSemantics.sep_members _ _ _).mp h_near\n  apply (Litex.SetSemantics.sep_members _ _ _).mpr\n  have h_member := hcontrol h hR hsmall\n  have h_member : M.mem _ (Litex.FunctionSemantics.domainValue (Litex.denote {function})) := h_member\n  rw [← {equal}] at h_member\n  exact ⟨hR,hR,h_member⟩\n)");
                let second=format!("(by\n{view}\n{matching}\n  change Litex.HasFiniteFunctionLimitValue M .both {q} (M.number 0) {value}\n  exact (congrArg (fun q => Litex.HasFiniteFunctionLimitValue M .both q (M.number 0) {value}) _partial_quotient_match).mpr (Litex.{law} {all} {original}).2\n)");
                (first, second)
            } else {
                let first=format!("{begin}  obtain ⟨radius,hr,hcontrol⟩ := _clauses.1\n  refine ⟨radius,hr,?_⟩\n  change ∀ input : M.Value, M.mem input _ → M.mem input _\n  intro input h_near\n  obtain ⟨hi,_,hclose⟩ := (Litex.SetSemantics.sep_members _ _ _).mp h_near\n  exact (congrArg (fun D => M.mem input D) {equal}).mpr (hcontrol input hi hclose)\n)");
                let second=format!("{begin}  intro _Host _rep epsilon h_epsilon\n  obtain ⟨delta,hd,hcontrol⟩ := _clauses.2 (Litex.denote epsilon) h_epsilon\n  refine ⟨delta,hd,?_⟩\n  change ∀ input : M.Value, M.mem input _ → M.mem input _\n  intro input h_near\n  obtain ⟨hi,_,hpos,hclose⟩ := (Litex.SetSemantics.sep_members _ _ _).mp h_near\n  apply (Litex.SetSemantics.sep_members _ _ _).mpr\n  exact ⟨hi,hi,hcontrol input ({equal} ▸ hi) hpos hclose⟩\n)");
                (first, second)
            };
            format!(
                "(And.intro (show {} from {first}) (show {} from {second}))",
                statements[0], statements[1]
            )
        };
        let statement = conjunction_proposition(statements)?;
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}
