//! Replay the two inclusions recorded for equality of complete function domains.

use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_domain::{
    function_domains_alpha_equal, FunctionDomainComparisonProof, FunctionDomainMatchProof,
};
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    /// The declarations retain the original fact IDs so pointwise call WD can
    /// cite the inclusions that the executor published inside fn_extension.
    pub(super) fn compile_function_domain_match(
        &self,
        proof: &FunctionDomainMatchProof,
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, String), LeanCompileError> {
        let source = &proof.source.signature;
        let target = &proof.target;
        match &proof.comparison {
            FunctionDomainComparisonProof::AlphaEquivalent => {
                if !function_domains_alpha_equal(source, target) {
                    return Err(LeanCompileError::unsupported("FunctionDomain/AlphaSubject"));
                }
                Ok((Vec::new(), "(by rfl)".into()))
            }
            FunctionDomainComparisonProof::MutualInclusion {
                forward,
                forward_proof,
                reverse,
                reverse_proof,
            } => {
                let scope =
                    SourcePosition::new(Some(position), SourceOwner::FunctionDomainWD(proof), 0);
                let mut declarations = Vec::new();
                let mut arrows = Vec::new();
                for (index, (from, to, fact, checked)) in [
                    (source, target, forward, forward_proof.as_ref()),
                    (target, source, reverse, reverse_proof.as_ref()),
                ]
                .into_iter()
                .enumerate()
                {
                    if source_subject(checked)? != *fact {
                        return Err(LeanCompileError::unsupported("FunctionDomain/ProofSubject"));
                    }
                    validate_inclusion(from, to, fact)?;
                    let prior = scope.function_domain_comparison_prior(index)?;
                    let (proposition, evidence) = self.compile_verify(checked, &prior)?;
                    let name = format!("h_{}", fact.fact_id().value());
                    declarations.push(format!("have {name} : {proposition} := {evidence}"));
                    arrows.push(self.compile_function_domain_inclusion(from, to, &name, &prior)?);
                }
                let s = self.compile_fn_signature(source, position)?;
                let t = self.compile_fn_signature(target, position)?;
                Ok((declarations, format!("(Litex.SetSemantics.ext ({s}).domain ({t}).domain ({s}).domain_isSet ({t}).domain_isSet (fun x => ⟨fun hx => {} x hx, fun hx => {} x hx⟩))", arrows[0], arrows[1])))
            }
        }
    }

    fn compile_function_domain_inclusion(
        &self,
        from: &FnSet,
        to: &FnSet,
        cited: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (mut lines, values, guards) =
            self.compile_preimage_domain_parts(from, "_preimage_input", position)?;
        let mut arguments = Vec::new();
        let mut applied = Vec::new();
        for (index, value) in values.iter().enumerate() {
            let member = if values.len() == 1 {
                "_preimage_base".to_string()
            } else {
                format!("(Litex.FiniteFunction.coordinate_mem_number _preimage_base ({index} : Fin {}) ({} : ℂ) (by norm_num))", values.len(), index + 1)
            };
            let object = format!("(Litex.semanticObject {value} (M.member_isSet {member}))");
            applied.push(format!("{object} {member}"));
            arguments.push(object);
        }
        applied.extend(guards);
        lines.push(format!(
            "have _domain_target := {cited} {}",
            applied.join(" ")
        ));
        let count = values.len() + to.dom_facts.len();
        let obligations = (0..count)
            .map(|i| conjunction_projection("_domain_target", i, count))
            .collect::<Vec<_>>();
        let (packed, member) =
            self.compile_complete_input(to, &arguments, &obligations, position)?;
        let target = self.compile_fn_signature(to, position)?;
        let source = self.compile_fn_signature(from, position)?;
        let repack = self.compile_preimage_repack(&values, "_preimage_base");
        let raw_packed = if values.len() == 1 {
            values[0].clone()
        } else {
            format!(
                "(Litex.FiniteFunction.tupleValue (M := M) ![{}])",
                values.join(", ")
            )
        };
        lines.push(format!(
            "have _repack : _preimage_input = {packed} := (show _preimage_input = {raw_packed} from {repack})"
        ));
        lines.push(format!(
            "exact Eq.mpr (congrArg (fun x => M.mem x ({target}).domain) _repack) {member}"
        ));
        Ok(format!(
            "(show ∀ x : M.Value, M.mem x ({source}).domain → M.mem x ({target}).domain from by\n  intro _preimage_input _preimage_domain\n  {}\n)",
            lines.join("\n  ")
        ))
    }
}

fn validate_inclusion(from: &FnSet, to: &FnSet, fact: &Fact) -> Result<(), LeanCompileError> {
    let bad = || LeanCompileError::unsupported("FunctionDomain/InclusionSubject");
    let Fact::ForallFact(fact) = fact else {
        return Err(bad());
    };
    let from_params = from
        .set_bound_parameters
        .groups
        .iter()
        .flat_map(|g| g.params.iter().map(move |p| (p, g.param_type.as_ref())))
        .collect::<Vec<_>>();
    let to_params = to
        .set_bound_parameters
        .groups
        .iter()
        .flat_map(|g| g.params.iter().map(move |p| (p, g.param_type.as_ref())))
        .collect::<Vec<_>>();
    let actual = fact
        .typed_parameters
        .groups
        .iter()
        .flat_map(|g| g.params.iter().map(move |p| (p, &g.param_type)))
        .collect::<Vec<_>>();
    if from_params.is_empty()
        || from_params.len() != to_params.len()
        || from_params.len() != actual.len()
        || fact.dom_facts.len() != from.dom_facts.len()
        || fact.then_facts.len() != to_params.len() + to.dom_facts.len()
    {
        return Err(bad());
    }
    let from_map = from_params
        .iter()
        .zip(&actual)
        .map(|((p, _), (a, _))| (p.id, Obj::Identifier(IdentifierObj::from_bound_name(a))))
        .collect::<HashMap<_, _>>();
    let to_map = to_params
        .iter()
        .zip(&actual)
        .map(|((p, _), (a, _))| (p.id, Obj::Identifier(IdentifierObj::from_bound_name(a))))
        .collect::<HashMap<_, _>>();
    if from_map.len() != actual.len()
        || to_map.len() != actual.len()
        || actual
            .iter()
            .map(|(p, _)| p.id)
            .collect::<std::collections::HashSet<_>>()
            .len()
            != actual.len()
    {
        return Err(bad());
    }
    for ((_, carrier), (_, ty)) in from_params.iter().zip(&actual) {
        if !matches!(ty, ParamType::Obj(a) if instantiated_object_matches(carrier, a, &from_map)) {
            return Err(bad());
        }
    }
    for (expected, actual) in from.dom_facts.iter().zip(&fact.dom_facts) {
        if !instantiated_fact_matches(
            &crate::instantiate::quantifier_free_fact_to_fact(expected.clone()),
            actual,
            &from_map,
        ) {
            return Err(bad());
        }
    }
    for (index, (parameter, carrier)) in to_params.iter().enumerate() {
        if !matches!(&fact.then_facts[index], ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(a))
            if a.element.ir()==to_map[&parameter.id].ir() && instantiated_object_matches(carrier,&a.set,&to_map))
        {
            return Err(bad());
        }
    }
    for (expected, actual) in to.dom_facts.iter().zip(&fact.then_facts[to_params.len()..]) {
        if !instantiated_fact_matches(
            &crate::instantiate::quantifier_free_fact_to_fact(expected.clone()),
            &actual.clone().into(),
            &to_map,
        ) {
            return Err(bad());
        }
    }
    Ok(())
}
