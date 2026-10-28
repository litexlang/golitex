use super::compile_classified_negation::quantifier_free_terms;
use crate::compile_to_lean::helper::{
    instantiated_fact_matches, quantified_parameter_substitution,
};
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_by_stmt::ExecByContraStmtSuccess;
use crate::prelude::*;
use std::collections::HashSet;

/// Validate the producer's exact classification: every candidate satisfying P
/// has another candidate satisfying P with at least one different component.
pub(super) fn validate_unique_negation(
    source: &PlainExistFact,
    negative: &ForallFact,
) -> Result<(), LeanCompileError> {
    let fail = || LeanCompileError::unsupported("By/UniqueNegationSubject");
    let [ExistOrAndChainAtomicFact::ExistFact(other)] = negative.then_facts.as_slice() else {
        return Err(fail());
    };
    let parameters: Vec<_> = source
        .typed_parameters
        .groups
        .iter()
        .flat_map(|g| &g.params)
        .collect();
    if parameters.is_empty()
        || source.fact_id == negative.fact_id
        || source.fact_id == other.fact_id
        || negative.fact_id == other.fact_id
        || source.typed_parameters != negative.typed_parameters
        || negative.dom_facts
            != source
                .facts
                .iter()
                .cloned()
                .map(crate::instantiate::quantifier_free_fact_to_fact)
                .collect::<Vec<_>>()
        || other.facts.len() != source.facts.len() + 1
    {
        return Err(fail());
    }
    let substitution = quantified_parameter_substitution(
        &source.typed_parameters,
        &other.typed_parameters,
        &Default::default(),
    )
    .ok_or_else(fail)?;
    // Fresh alternative binders cannot capture either source binders or free
    // inputs, including references inside dependent carriers and body clauses.
    let mut used: HashSet<_> = parameters.iter().map(|p| p.id).collect();
    for group in &source.typed_parameters.groups {
        if let ParamType::Obj(carrier) = &group.param_type {
            crate::instantiate::collect_free_plain_ids(carrier, &HashSet::new(), &mut used);
        }
    }
    for clause in &source.facts {
        let fact = crate::instantiate::quantifier_free_fact_to_fact(clause.clone());
        for atom in quantifier_free_terms(&fact)?.iter().flatten() {
            for object in atomic_fact_args_ref(atom) {
                crate::instantiate::collect_free_plain_ids(object, &HashSet::new(), &mut used);
            }
        }
    }
    if other
        .typed_parameters
        .groups
        .iter()
        .flat_map(|g| &g.params)
        .any(|p| !used.insert(p.id))
    {
        return Err(fail());
    }
    for (original, actual) in source.facts.iter().zip(&other.facts) {
        if !instantiated_fact_matches(
            &crate::instantiate::quantifier_free_fact_to_fact(original.clone()),
            &crate::instantiate::quantifier_free_fact_to_fact(actual.clone()),
            &substitution,
        ) {
            return Err(fail());
        }
    }
    let differences = quantifier_free_terms(&crate::instantiate::quantifier_free_fact_to_fact(
        other.facts.last().unwrap().clone(),
    ))?;
    if differences.len() != parameters.len()
        || differences.iter().zip(parameters).any(|(term, p)| {
            !matches!(term.as_slice(), [AtomicFact::NotEqualFact(ne)]
            if Some(&ne.left) == substitution.get(&p.id)
                && ne.right == Obj::Identifier(IdentifierObj::from_bound_name(p)))
        })
    {
        return Err(fail());
    }
    Ok(())
}

impl LitexToLeanCompiler {
    pub(super) fn compile_unique_contra_bridge(
        &self,
        proof: &ExecByContraStmtSuccess,
        denied_goal: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (
            Fact::ExistUniqueFact(source),
            Fact::ForallFact(reverse),
            FactWellDefinedProof::ForallFact(formation),
        ) = (
            &proof.goal,
            &proof.reverse_assumption,
            &proof.reverse_assumption_wd,
        )
        else {
            return Err(LeanCompileError::unsupported("By/UniqueNegationFormation"));
        };
        validate_unique_negation(source, reverse)?;
        let scope =
            SourcePosition::new(Some(position), SourceOwner::ForallWD(reverse, formation), 0);
        let (_, introductions, definitions) =
            self.compile_canonical_forall_head(reverse, formation, &scope)?;
        let parameters: Vec<_> = source
            .typed_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .collect();
        let (_, unique_arguments) = self.unique_signature(source, position)?;
        let mut witness = Vec::new();
        for (p, store) in parameters.iter().zip(
            &formation
                .detailed_ref()
                .introduced_params
                .defined_params
                .store_and_infer_results,
        ) {
            let value = format!("_value_i{}", p.id.value());
            witness.push(format!(
                "(Litex.semanticObject (Litex.denote {value}) (Litex.isSet {value}))"
            ));
            witness.push(format!("h_{}", store.primary_fact_id().value()));
        }
        witness.extend(
            reverse
                .dom_facts
                .iter()
                .map(|f| format!("h_{}", f.fact_id().value())),
        );
        if source.facts.is_empty() {
            witness.push("True.intro".into());
        }
        let mut steps = vec![
            "classical".to_string(),
            format!("intro {}", introductions.join(" ")),
        ];
        steps.extend(definitions);
        steps.extend([
            "apply Classical.byContradiction".into(),
            "intro _no_alternative".into(),
            format!("apply {denied_goal}"),
            "constructor".into(),
            format!("· exact ⟨{}⟩", witness.join(", ")),
            format!("· intro {}", unique_arguments.join(" ")),
        ]);
        let mut equalities = Vec::new();
        for side in ["left", "right"] {
            let mut alternative = Vec::new();
            for p in &parameters {
                alternative.extend([
                    format!("_unique_{side}_i{}", p.id.value()),
                    format!("_member_{side}_i{}", p.id.value()),
                ]);
            }
            alternative.extend((0..source.facts.len()).map(|i| format!("_body_{side}_{i}")));
            for (index, p) in parameters.iter().enumerate() {
                let equality = format!("_same_{side}_i{}", p.id.value());
                equalities.push(equality.clone());
                let mut different = "_different".to_string();
                if index + 1 < parameters.len() {
                    different = format!("(Or.inl {different})");
                }
                for _ in 0..index {
                    different = format!("(Or.inr {different})");
                }
                let mut other = alternative.clone();
                other.push(different);
                steps.push(format!("  have {equality} : Litex.denote _unique_{side}_i{} = Litex.denote _value_i{} := by\n    apply Classical.byContradiction\n    intro _different\n    apply _no_alternative\n    exact ⟨{}⟩", p.id.value(), p.id.value(), other.join(", ")));
            }
        }
        steps.push(format!("  simp only [{}]", equalities.join(", ")));
        Ok(format!(
            "(by\n  {})",
            steps.join("\n").replace('\n', "\n  ")
        ))
    }
}
