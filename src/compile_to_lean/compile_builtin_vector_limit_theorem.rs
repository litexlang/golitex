//! Explicit vector-limit schemas consume the original domain and stage captures.
use super::compile_multivariable_limit_context::validate_limit_context;
use super::compile_multivariable_scalar_limit::{validate_clauses, vector_carrier};
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

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("VectorLimitTheorem/{stage}"))
}
fn candidate(fact: &Fact, args: &[Obj], value: &Obj) -> Result<(), LeanCompileError> {
    if matches!(fact,Fact::AtomicFact(f) if super::compile_multivariable_vector_limit::parts(f).is_some_and(|(r,negative)| !negative && r.function.ir()==args[0].ir() && r.point.ir()==args[1].ir() && r.input_dimension.ir()==args[2].ir() && r.output_dimension.ir()==args[3].ir() && r.value.ir()==value.ir()))
    {
        Ok(())
    } else {
        Err(invalid("Candidate"))
    }
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_vector_limit_theorem(
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
        let (arity, count, outputs) = match builtin.theorem {
            VectorLimitAtFromDefinition => (5, 7, 1),
            VectorLimitAtToDefinition => (5, 6, 2),
            VectorLimitAtExists => (5, 6, 1),
            VectorLimitAtUnique => (6, 7, 1),
            VectorLimitAtSelected => (4, 6, 1),
            _ => return Err(invalid("Id")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || args.len() != arity
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != outputs
            || conclusions_wd.len() != outputs
        {
            return Err(invalid("OriginalStages"));
        }
        let source = if matches!(
            builtin.theorem,
            VectorLimitAtFromDefinition | VectorLimitAtSelected
        ) {
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
            if capture.requirements.len()!=6 || !builtin.requirements[..5].iter().zip(&capture.requirements[..5]).all(|(a,b)|
                crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::quantifier_free_source_facts_alpha_equal(a,&b.requirement)) {
                return Err(invalid("OriginalContext"));
            }
            &capture.function_domain
        } else {
            candidate(&builtin.requirements[5], args, &args[4])?;
            let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(
                rules,
            ))) = &dom_stores[5].infer
            else {
                return Err(invalid("OriginalInference"));
            };
            let [InferMultivariableAnalysisFactResult::Definition(capture)] = rules.as_slice()
            else {
                return Err(invalid("OriginalInference"));
            };
            if capture.source_fact_id != builtin.requirements[5].fact_id()
                || capture.derived.len() != 3
            {
                return Err(invalid("OriginalInferenceIdentity"));
            }
            capture
                .function_domain
                .as_ref()
                .ok_or_else(|| invalid("OriginalCompleteDomain"))?
        };
        validate_limit_context(args, &builtin.requirements[..5], source, Some(&args[3]))?;
        let domain = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
            &source.signature,
        )
        .ok_or_else(|| invalid("ActualDomain"))?;
        match builtin.theorem {
            VectorLimitAtFromDefinition => {
                candidate(&builtin.conclusions[0], args, &args[4])?;
                validate_clauses(
                    &args[0],
                    &args[1],
                    &args[2],
                    Some(&args[3]),
                    &args[4],
                    &domain,
                    &builtin.requirements[5..],
                )?;
            }
            VectorLimitAtToDefinition => validate_clauses(
                &args[0],
                &args[1],
                &args[2],
                Some(&args[3]),
                &args[4],
                &domain,
                &builtin.conclusions,
            )?,
            VectorLimitAtExists => super::compile_multivariable_vector_limit::existence(
                &args[0],
                &args[1],
                &args[2],
                &args[3],
                &builtin.conclusions[0],
            )?,
            VectorLimitAtUnique => {
                candidate(&builtin.requirements[6], args, &args[5])?;
                if !matches!(&builtin.conclusions[0],Fact::AtomicFact(AtomicFact::EqualFact(eq)) if eq.left.ir()==args[4].ir()&&eq.right.ir()==args[5].ir())
                {
                    return Err(invalid("UniqueConclusion"));
                }
            }
            VectorLimitAtSelected => {
                super::compile_multivariable_vector_limit::existence(
                    &args[0],
                    &args[1],
                    &args[2],
                    &args[3],
                    &builtin.requirements[5],
                )?;
                let Fact::AtomicFact(goal) = &builtin.conclusions[0] else {
                    return Err(invalid("SelectedConclusion"));
                };
                let (r, false) = super::compile_multivariable_vector_limit::parts(goal)
                    .ok_or_else(|| invalid("SelectedConclusion"))?
                else {
                    return Err(invalid("SelectedNegative"));
                };
                let Obj::LimitOperator(LimitOperator::MultivariableVector(selector)) = &r.value
                else {
                    return Err(invalid("SelectedObject"));
                };
                if selector.function.ir() != args[0].ir()
                    || selector.point.ir() != args[1].ir()
                    || selector.input_dimension.ir() != args[2].ir()
                    || selector.output_dimension.ir() != args[3].ir()
                {
                    return Err(invalid("SelectedArguments"));
                }
                candidate(&builtin.conclusions[0], args, &r.value)?;
            }
            _ => unreachable!(),
        }
        let mut definitions = Vec::new();
        for (index, ((requirement, checked), store)) in builtin
            .requirements
            .iter()
            .zip(dom_proofs)
            .zip(dom_stores)
            .enumerate()
        {
            if source_subject(checked)? != *requirement {
                return Err(invalid("OriginalProofSubject"));
            }
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let compiled = self.compile_verify(checked, &prior)?;
            self.validate_store(&store.store, requirement)?;
            definitions.push(self.emit_internal_fact(requirement, &compiled, &prior)?);
            definitions.extend(self.compile_stored_inferences(
                store,
                requirement,
                &(compiled.0, format!("h_{}", requirement.fact_id().value())),
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
        for (fact, wd) in builtin.conclusions.iter().zip(conclusions_wd) {
            self.compile_fact_wd(wd, fact, &formed)?;
        }
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
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
        let proof=match builtin.theorem {
            VectorLimitAtExists => format!("(by\n  obtain ⟨value,hv,hc⟩ := Litex.multivariableVectorExistsOfCandidate {raw} h_{}\n  exact ⟨value,hv,hc⟩\n)",builtin.requirements[5].fact_id().value()),
            VectorLimitAtSelected => format!("(by\n  apply Litex.multivariableVectorLimitValueSelected {raw}\n  obtain ⟨value,hv,hc⟩ := h_{}\n  exact ⟨Litex.denote value,hc⟩\n)",builtin.requirements[5].fact_id().value()),
            VectorLimitAtUnique => {
                let (view,_)=self.compile_multivariable_limit_view(&args[0],source,&scope)?;
                let function=self.compile_euclidean_limit_function_context(args,&builtin.requirements[..5],source,Some(&args[3]),&scope)?;
                format!("(by\n{view}\n{function}\n  exact Litex.multivariableVectorLimitUnique {raw} (Litex.inNPos_natural {} h_{}) _multivariable_real h_{} h_{}\n)",objects[3],builtin.requirements[2].fact_id().value(),builtin.requirements[5].fact_id().value(),builtin.requirements[6].fact_id().value())
            }
            VectorLimitAtFromDefinition => {
                let FactWellDefinedProof::AtomicExceptEquality(wd)=&conclusions_wd[0] else { unreachable!() };
                let PredicateDomainProof::MultivariableAnalysis(capture)=&wd.as_detailed().map_err(|_|invalid("DetailedFormation"))?.predicate_domain else { unreachable!() };
                let value=&capture.requirements[5];
                if !matches!(&value.requirement,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==args[4].ir()&&vector_carrier(&f.set,&args[3])) { return Err(invalid("OriginalValueCarrier")); }
                let PredicateDomainRequirementProof::Verified(checked)=&value.result else { return Err(invalid("OriginalValueProof")); };
                if source_subject(checked)?!=value.requirement { return Err(invalid("OriginalValueProofSubject")); }
                let hv=self.compile_verify(checked,&scope)?.1;
                let (view,equal)=self.compile_multivariable_limit_view(&args[0],source,&scope)?;
                format!("(by\n{view}\n  apply Litex.multivariableVectorLimitOfClauses {raw} {hv}\n  · intro radius h_radius\n    obtain ⟨input,hi,hpos,hclose⟩ := h_{} (Litex.semanticObject radius (M.member_isSet h_radius)) h_radius\n    exact ⟨input,{equal} ▸ hi,hpos,hclose⟩\n  · intro epsilon h_epsilon\n    obtain ⟨delta,hd,hcontrol⟩ := h_{} (Litex.semanticObject epsilon (M.member_isSet h_epsilon)) h_epsilon\n    refine ⟨delta,hd,?_⟩\n    intro input hi hpos hclose\n    have hi : M.mem input _multivariable_source_domain := {equal}.symm ▸ hi\n    have hgood := hcontrol input ((Litex.SetSemantics.sep_members _ _ _).mpr ⟨hi,hi,hpos,hclose⟩)\n    exact ((Litex.SetSemantics.sep_members _ _ _).mp hgood).2.2\n)",builtin.requirements[5].fact_id().value(),builtin.requirements[6].fact_id().value())
            }
            VectorLimitAtToDefinition => {
                let mut clauses=Vec::new();
                for (index,wd) in conclusions_wd.iter().enumerate() {
                    let scope=SourcePosition::new(Some(&formed),SourceOwner::FactWD(wd),usize::MAX);
                    let statement=self.compile_formed_fact_proposition(wd,&builtin.conclusions[index],&formed)?;
                    let (view,equal)=self.compile_multivariable_limit_view(&args[0],source,&scope)?;
                    let head=format!("(by\n{view}\n  have _clauses := Litex.multivariableVectorLimitClauses {raw} h_{}\n",builtin.requirements[5].fact_id().value());
                    let body=if index==0 {
                        format!("  intro _Host _rep radius h_radius\n  obtain ⟨input,hi,hpos,hclose⟩ := _clauses.1 (Litex.denote radius) h_radius\n  exact ⟨input,(congrArg (fun D => M.mem (Litex.denote input) D) {equal}).mpr hi,hpos,hclose⟩\n)")
                    } else {
                        format!("  intro _Host _rep epsilon h_epsilon\n  obtain ⟨delta,hd,hcontrol⟩ := _clauses.2 (Litex.denote epsilon) h_epsilon\n  refine ⟨delta,hd,?_⟩\n  change ∀ input : M.Value, M.mem input _ → M.mem input _\n  intro input h_input\n  obtain ⟨hi,_,hpos,hclose⟩ := (Litex.SetSemantics.sep_members _ _ _).mp h_input\n  apply (Litex.SetSemantics.sep_members _ _ _).mpr\n  exact ⟨hi,hi,hcontrol input ((congrArg (fun D => M.mem input D) {equal}).mp hi) hpos hclose⟩\n)")
                    };
                    clauses.push(format!("(show {statement} from {head}{body})"));
                }
                format!("(And.intro {} {})",clauses[0],clauses[1])
            }
            _ => unreachable!(),
        };
        let statements = builtin
            .conclusions
            .iter()
            .zip(conclusions_wd)
            .map(|(f, w)| self.compile_formed_fact_proposition(w, f, &formed))
            .collect::<Result<Vec<_>, _>>()?;
        Ok((
            definitions,
            format!(
                "(show {} from {proof})",
                conjunction_proposition(statements)?
            ),
            builtin.conclusions.clone(),
        ))
    }
}
