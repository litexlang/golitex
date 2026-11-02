use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_multivariable_definition(
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
        if builtin.theorem != BuiltinTheoremId::MultiLimitAtFromDefinition
            || !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
        {
            return Err(invalid("Contract"));
        }
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let (
            [function, point, dimension, value],
            [_, _, _, _, _, _],
            [_, _, _, _, _, _],
            [_, _, _, _, _, _],
            [Fact::AtomicFact(goal)],
            [FactWellDefinedProof::AtomicExceptEquality(wd)],
        ) = (
            args.as_slice(),
            builtin.requirements.as_slice(),
            dom_proofs,
            dom_stores,
            builtin.conclusions.as_slice(),
            conclusions_wd,
        )
        else {
            return Err(invalid("Stages"));
        };
        let (r, false) = super::compile_multivariable_scalar_limit::parts(goal)
            .ok_or_else(|| invalid("ScalarConclusion"))?
        else {
            return Err(invalid("PositiveConclusion"));
        };
        if args != &builtin.arguments
            || r.function.ir() != function.ir()
            || r.point.ir() != point.ir()
            || r.dimension.ir() != dimension.ir()
            || r.value.ir() != value.ir()
        {
            return Err(invalid("OriginalArguments"));
        }
        let PredicateDomainProof::MultivariableAnalysis(capture) = &wd
            .as_detailed()
            .map_err(|_| invalid("DetailedWD"))?
            .predicate_domain
        else {
            return Err(invalid("OriginalDomainCapture"));
        };
        if capture.requirements.len()!=5 || !builtin.requirements[..4].iter()
            .zip(&capture.requirements[..4]).all(|(a,b)|
                crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::quantifier_free_source_facts_alpha_equal(a,&b.requirement)) {
            return Err(invalid("OriginalContext"));
        }
        let domain = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
            &capture.function_domain.signature,
        )
        .ok_or_else(|| invalid("Signature"))?;
        super::compile_multivariable_scalar_limit::validate_clauses(
            function,
            point,
            dimension,
            None,
            value,
            &domain,
            &builtin.requirements[4..],
        )?;
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
            before: 6,
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], &builtin.conclusions[0], &formed)?;
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let (view, equal) =
            self.compile_multivariable_limit_view(function, &capture.function_domain, &scope)?;
        let objects =
            [function, point, dimension, value].map(|o| self.compile_object_reference(o, &scope));
        let [f, p, n, v] = objects;
        let raw = [f?, p?, n?, v?]
            .map(|s| format!("(Litex.denote {s})"))
            .join(" ");
        let real = self.compile_real_membership_certificate(value, &scope)?;
        let acc = format!("h_{}", builtin.requirements[4].fact_id().value());
        let eps = format!("h_{}", builtin.requirements[5].fact_id().value());
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        let proof=format!("(by\n{view}\n  apply Litex.multivariableScalarLimitOfClauses {raw} {real}\n  · intro radius h_radius\n    obtain ⟨input,hi,hpos,hclose⟩ := {acc} (Litex.semanticObject radius (M.member_isSet h_radius)) h_radius\n    exact ⟨input,{equal} ▸ hi,hpos,hclose⟩\n  · intro epsilon h_epsilon\n    obtain ⟨delta,hd,hcontrol⟩ := {eps} (Litex.semanticObject epsilon (M.member_isSet h_epsilon)) h_epsilon\n    refine ⟨delta,hd,?_⟩\n    intro input hi hpos hclose\n    have hi : M.mem input _multivariable_source_domain := {equal}.symm ▸ hi\n    have _good := hcontrol input ((Litex.SetSemantics.sep_members _ _ _).mpr ⟨hi,hi,hpos,hclose⟩)\n    exact ((Litex.SetSemantics.sep_members _ _ _).mp _good).2.2\n)");
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::new(&format!("MultivariableDefinition/{stage}"),
        "A Euclidean definition theorem requires the original complete function-domain capture, ordered context and exact defining clauses/formation.")
}
