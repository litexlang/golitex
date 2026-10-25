//! Real Euclidean multivariable predicates. Actual function signatures remain authoritative.
pub(crate) mod definition;
pub(crate) mod expression;
pub(crate) mod helper;
pub(crate) mod selector;
pub(crate) mod strategy;
use super::function_domain::{function_domains_alpha_equal, CompleteFunctionDomainProof};
use crate::prelude::*;
use helper::*;

impl Runtime {
    pub(crate) fn multivariable_signature_requirements(
        &mut self,
        relation: &MultivariableAnalysisRelation,
        state: VerifyState,
    ) -> RuntimeResult<Option<(CompleteFunctionDomainProof, Vec<Fact>)>> {
        let args = relation.argument_refs();
        let function = args[0];
        let point = args[1];
        let n = input_dimension(relation);
        let output = function_output_dimension(relation);
        let mut selected: Option<CompleteFunctionDomainProof> = None;
        for source in self.complete_function_domains(function, state)? {
            if actual_domain(&source.signature).is_none() {
                return Ok(None);
            }
            if let Some(previous) = &selected {
                if !function_domains_alpha_equal(&previous.signature, &source.signature) {
                    return Ok(None);
                }
            } else {
                selected = Some(source);
            }
        }
        let Some(source) = selected else {
            return Ok(None);
        };
        let domain = actual_domain(&source.signature).unwrap();
        let input_set = source
            .signature
            .set_bound_parameters
            .groups
            .iter()
            .find(|g| !g.params.is_empty())
            .unwrap()
            .param_type
            .as_ref()
            .clone();
        let mut requirements = vec![
            member(self, n.clone(), positive_natural()),
            self.multivariable_carrier_requirement(input_set, vector(n.clone())),
        ];
        let codomain = match &output {
            Some(m) => {
                requirements.push(member(self, m.clone(), positive_natural()));
                vector(m.clone())
            }
            None => real(),
        };
        requirements.push(self.multivariable_carrier_requirement(
            source.signature.ret_set.as_ref().clone(),
            codomain,
        ));
        requirements.push(member(self, point.clone(), vector(n.clone())));
        if !is_limit(relation) {
            requirements.push(member(self, point.clone(), domain));
        }
        match relation {
            MultivariableAnalysisRelation::PartialDerivativeAt(x) => {
                requirements.push(member(self, x.coordinate.clone(), indices(n.clone())))
            }
            MultivariableAnalysisRelation::SecondPartialDerivativeAt(x) => {
                requirements.push(member(self, x.first_coordinate.clone(), indices(n.clone())));
                requirements.push(member(self, x.second_coordinate.clone(), indices(n)));
            }
            _ => {}
        }
        Ok(Some((source, requirements)))
    }
    pub(crate) fn multivariable_domain_requirements(
        &mut self,
        relation: &MultivariableAnalysisRelation,
        state: VerifyState,
    ) -> RuntimeResult<Option<(CompleteFunctionDomainProof, Vec<Fact>)>> {
        let Some((source, mut requirements)) =
            self.multivariable_signature_requirements(relation, state)?
        else {
            return Ok(None);
        };
        if let Some(candidate) = value(relation) {
            requirements.push(member(self, candidate.clone(), value_carrier(relation)));
        }
        Ok(Some((source, requirements)))
    }
    pub(crate) fn store_multivariable_definition(
        &mut self,
        fact: &MultivariableAnalysisFact,
        state: VerifyState,
    ) -> RuntimeResult<Vec<crate::store_fact_and_infer::StoreInferredFactResult>> {
        let mut result = Vec::new();
        for clause in self
            .multivariable_defining_clauses(&fact.relation, state)?
            .unwrap_or_default()
        {
            result.push(self.store_inferred_fact(&clause)?);
        }
        if value(&fact.relation).is_some() {
            let existence = self.multivariable_candidate_existence(&fact.relation);
            result.push(self.store_inferred_fact(&existence)?);
        }
        Ok(result)
    }
    pub(crate) fn multivariable_candidate_existence(
        &mut self,
        relation: &MultivariableAnalysisRelation,
    ) -> Fact {
        let chosen = self.fresh_internal_param();
        let selected = identifier(&chosen);
        let mut args: Vec<_> = relation.argument_refs().into_iter().cloned().collect();
        *args.last_mut().unwrap() = selected;
        let candidate = relation_fact(self, relation.with_arguments(&args));
        exists(self, chosen, value_carrier(relation), vec![candidate])
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/execute/multivariable_calculus.rs"]
mod multivariable_calculus_tests;

impl Runtime {
    pub(crate) fn multivariable_carrier_requirement(&mut self, source: Obj, target: Obj) -> Fact {
        if let (Some(left), Some(right)) = (
            self.function_space_signature(&source),
            self.function_space_signature(&target),
        ) {
            if super::fn_sets_alpha_equal(&left, &right) {
                return equal(
                    self,
                    Obj::FunctionSpace(FunctionSpace::FnSet(left)),
                    Obj::FunctionSpace(FunctionSpace::FnSet(right)),
                );
            }
        }
        subset(self, source, target)
    }
}
