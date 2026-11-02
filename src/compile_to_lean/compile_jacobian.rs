//! Jacobian matrices: replay the original coordinate-partial evidence.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainProof;
use crate::execute::execute_fact_stmt::multivariable::selector::{
    JacobianAtWellDefinedProof, MultivariableSelectorSelectionProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    PredicateDomainRequirementProof, PredicateDomainWellDefinedProof,
};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferMultivariableAnalysisFactResult};
use std::collections::HashMap;
impl LitexToLeanCompiler {
    pub(super) fn compile_jacobian_wd(
        &self,
        object: &JacobianAt,
        proof: &JacobianAtWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let args = [
            object.function.as_ref(),
            object.point.as_ref(),
            object.input_dimension.as_ref(),
            object.output_dimension.as_ref(),
        ];
        let stages = &proof.stages;
        if stages.argument_well_defined.len() != 4 {
            return Err(invalid("WDArguments"));
        }
        let mut binders = Vec::new();
        let mut certified_arguments = Vec::new();
        for (i, (arg, child)) in args.iter().zip(&stages.argument_well_defined).enumerate() {
            ensure_object(arg, child)?;
            let compiled = self.compile_wd(
                child,
                &SourcePosition {
                    before: i,
                    ..*position
                },
            )?;
            binders.push(format!("let _multivariable_arg_{i} := {}", compiled));
            certified_arguments.push(format!("({compiled})"));
        }
        let mut lines = self.compile_jacobian_domain(
            args[0],
            args[1],
            args[2],
            args[3],
            None,
            &stages.function_domain,
            &stages.domains,
            position,
        )?;
        let selected = match &stages.selection {
            MultivariableSelectorSelectionProof::Candidate(c) => {
                let (q, negative) = parts(&c.fact).ok_or_else(|| invalid("CandidateKind"))?;
                if negative
                    || q.function.ir() != args[0].ir()
                    || q.point.ir() != args[1].ir()
                    || q.input_dimension.ir() != args[2].ir()
                    || q.output_dimension.ir() != args[3].ir()
                {
                    return Err(invalid("CandidateSubject"));
                }
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) =
                    c.searched_proof.as_ref()
                else {
                    return Err(invalid("CandidateCitation"));
                };
                let term = self.compile_known_atomic(known, &c.fact, position)?;
                let value = self.compile_function_raw_expression_bound(
                    &q.value,
                    position,
                    &HashMap::new(),
                )?;
                format!("(Litex.jacobianExistsOfCandidate (Litex.denote _multivariable_arg_0) (Litex.denote _multivariable_arg_1) (Litex.denote _multivariable_arg_2) (Litex.denote _multivariable_arg_3) {value} {term})")
            }
            MultivariableSelectorSelectionProof::Existence { fact, proof } => {
                existence(args[0], args[1], args[2], args[3], fact)?;
                if source_subject(proof)? != *fact {
                    return Err(invalid("ExistenceProof"));
                }
                let (ty, term) = self.compile_verify(proof, position)?;
                format!("(by\n  have _original_jacobian_exists : {ty} := {term}\n  obtain ⟨v,hv,hc⟩ := _original_jacobian_exists\n  exact ⟨v,hv,hc⟩\n)")
            }
        };
        lines.push(format!(
            "exact ⟨h_{},h_{},_multivariable_real,h_{},_jacobian_point_domain,{selected}⟩",
            stages.domains[0].requirement.fact_id().value(),
            stages.domains[2].requirement.fact_id().value(),
            stages.domains[4].requirement.fact_id().value()
        ));
        Ok(format!(
            "({}; @Litex.Obj.mk M _ (Litex.jacobianRepresentation (M := M)) (Litex.JacobianObj.mk {}) (by\n  {}\n))",
            binders.join("; "),
            certified_arguments.join(" "),
            lines.join("\n").replace('\n', "\n  ")
        ))
    }
    pub(super) fn compile_jacobian_equality(
        &self,
        fact: &EqualFact,
        proof:&crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_multivariable::MultivariableEqualityProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_multivariable::MultivariableEqualityProof as P;
        let P::SelectedValue(proof) = proof else {
            return Err(invalid("EqualityRoute"));
        };
        let (selected, value, obj, reverse) = match (&fact.left, &fact.right) {
            (s @ Obj::DerivativeOperator(DerivativeOperator::Jacobian(o)), v) => (s, v, o, false),
            (v, s @ Obj::DerivativeOperator(DerivativeOperator::Jacobian(o))) => (s, v, o, true),
            _ => return Err(invalid("SelectedSubject")),
        };
        let (candidate, negative) =
            parts(&proof.candidate.fact).ok_or_else(|| invalid("EqualityCandidate"))?;
        if negative
            || candidate.function.ir() != obj.function.ir()
            || candidate.point.ir() != obj.point.ir()
            || candidate.input_dimension.ir() != obj.input_dimension.ir()
            || candidate.output_dimension.ir() != obj.output_dimension.ir()
        {
            return Err(invalid("EqualityCandidateSubject"));
        }
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) =
            proof.candidate.searched_proof.as_ref()
        else {
            return Err(invalid("EqualityCitation"));
        };
        let h = self.compile_known_atomic(known, &proof.candidate.fact, position)?;
        let q = EqualFact {
            fact_id: fact.fact_id,
            left: candidate.value.clone(),
            right: value.clone(),
            line_file: None,
        };
        let eq = self.compile_equality_search(&q, &proof.value_equality, position)?;
        let selected = self.compile_object_reference(selected, position)?;
        let raw = self.compile_function_raw_expression_bound(
            &candidate.value,
            position,
            &HashMap::new(),
        )?;
        let term = format!("((Litex.jacobianEqCandidate {selected} {raw} {h}).trans {eq})");
        Ok(if reverse {
            format!("{term}.symm")
        } else {
            term
        })
    }
}

impl LitexToLeanCompiler {
    pub(super) fn compile_jacobian_domain(
        &self,
        f: &Obj,
        p: &Obj,
        n: &Obj,
        m: &Obj,
        value: Option<&Obj>,
        source: &CompleteFunctionDomainProof,
        requirements: &[PredicateDomainWellDefinedProof],
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let domain = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
            &source.signature,
        )
        .ok_or_else(|| invalid("Signature"))?;
        if requirements.len() != 6 + usize::from(value.is_some()) {
            return Err(invalid("DomainStages"));
        }
        let args = 4 + usize::from(value.is_some());
        let mut lines = self.compile_multivariable_limit_domain(
            f,
            p,
            n,
            Some(m),
            None,
            source,
            &requirements[..5],
            args,
            position,
        )?;
        for (i, r) in requirements.iter().enumerate().skip(5) {
            let valid = match (i, &r.requirement) {
                (5, Fact::AtomicFact(AtomicFact::InFact(q))) => {
                    q.element.ir() == p.ir() && q.set.ir() == domain.ir()
                }
                (6, Fact::AtomicFact(AtomicFact::InFact(q))) => {
                    value.is_some_and(|v| q.element.ir() == v.ir())
                        && q.set.ir() == matrix_set(m, n).ir()
                }
                _ => false,
            };
            if !valid {
                return Err(invalid("RequirementSubject"));
            }
            let PredicateDomainRequirementProof::Verified(proof) = &r.result else {
                return Err(invalid("RequirementCapture"));
            };
            if source_subject(proof)? != r.requirement {
                return Err(invalid("RequirementProof"));
            }
            let (ty, term) = self.compile_verify(
                proof,
                &SourcePosition {
                    before: args + i,
                    ..*position
                },
            )?;
            lines.push(format!(
                "have h_{} : {ty} := {term}",
                r.requirement.fact_id().value()
            ));
        }
        let f = self.compile_object_reference(f, position)?;
        let p = self.compile_object_reference(p, position)?;
        lines.push(format!("have _jacobian_point_domain : M.mem (Litex.denote {p}) (Litex.FunctionSemantics.domainValue (Litex.denote {f})) := (_multivariable_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _multivariable_signature.domain_isSet _multivariable_member).symm) ▸ h_{}",requirements[5].requirement.fact_id().value()));
        Ok(lines)
    }

    pub(super) fn compile_jacobian_inferences(
        &self,
        infer: &InferAtomicFactResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (InferAtomicFactResult::MultivariableAnalysisFact(rules), Fact::AtomicFact(a)) =
            (infer, seed)
        else {
            return Err(invalid("InferenceFamily"));
        };
        let (r, negative) = parts(a).ok_or_else(|| invalid("InferencePredicate"))?;
        let [InferMultivariableAnalysisFactResult::Definition(p)] = rules.as_slice() else {
            return Err(invalid("InferenceRule"));
        };
        if negative
            || p.source_fact_id != seed.fact_id()
            || p.derived.len() != if p.function_domain.is_some() { 2 } else { 1 }
        {
            return Err(invalid("InferenceIdentity"));
        }
        let facts = p
            .derived
            .iter()
            .map(|s| {
                let f = self.resolve_fact(s.primary_fact_id(), position)?;
                self.validate_store(&s.store, &f)?;
                Ok(f)
            })
            .collect::<Result<Vec<_>, LeanCompileError>>()?;
        let values = [
            &r.function,
            &r.point,
            &r.input_dimension,
            &r.output_dimension,
            &r.value,
        ]
        .into_iter()
        .map(|o| self.compile_function_raw_expression_bound(o, position, &HashMap::new()))
        .collect::<Result<Vec<_>, _>>()?;
        let mut lines = Vec::new();
        if let Some(source) = &p.function_domain {
            let domain = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
                &source.signature,
            )
            .ok_or_else(|| invalid("InferenceSignature"))?;
            validate_clauses(r, &domain, &facts[..1])?;
            let (view, equal) =
                self.compile_multivariable_limit_view(&r.function, source, position)?;
            let ty = self.compile_coordinate_clause_value_proposition(&facts[0], position)?;
            let [f, point, n, _, value] = values.as_slice() else {
                unreachable!()
            };
            let term=format!("(by\n{view}\n  intro row h_row col h_col\n  have h_partial := ({}).2 (Litex.denote row) h_row (Litex.denote col) h_col\n  exact (congrArg (fun D => Litex.HasPartialDerivativeAtValue M (Litex.componentFunctionValue {f} D (Litex.denote row)) {point} {n} (Litex.denote col) (Litex.FunctionSemantics.callValue {value} (Litex.FiniteFunction.pack2 (Litex.denote row) (Litex.denote col)))) {equal}.symm).mp h_partial\n)",compiled.1);
            lines.push(self.emit_internal_fact(&facts[0], &(ty, term), position)?);
        }
        let target = facts.last().unwrap();
        existence(
            &r.function,
            &r.point,
            &r.input_dimension,
            &r.output_dimension,
            target,
        )?;
        let ty = self.compile_function_raw_predicate(target, position, &HashMap::new())?;
        let term = format!(
            "(by obtain ⟨v,hv,hc⟩ := Litex.jacobianExistsOfCandidate {} {}; exact ⟨v,hv,hc⟩)",
            values.join(" "),
            compiled.1
        );
        lines.push(self.emit_internal_fact(target, &(ty, term), position)?);
        Ok(lines)
    }

    pub(super) fn compile_jacobian_definition(
        &self,
        r: &JacobianAtRelation,
        proof: &crate::execute::execute_fact_stmt::multivariable::definition::JacobianAtRelationDefinitionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let domain = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
            &proof.function_domain.signature,
        )
        .ok_or_else(|| invalid("DefinitionSignature"))?;
        validate_clauses(r, &domain, &proof.requirement_facts)?;
        let [child] = proof.proof_of_requirement_facts.as_slice() else {
            return Err(invalid("DefinitionProofCount"));
        };
        if source_subject(child)? != proof.requirement_facts[0] {
            return Err(invalid("DefinitionProofSubject"));
        }
        let (ty, term) = self.compile_verify(child, &position.atomic_search_prior(0)?)?;
        let member = position
            .with_visible_membership(
                &r.value,
                &matrix_set(&r.output_dimension, &r.input_dimension),
                &mut |p, at| self.compile_verify(p, at).map(|v| v.1),
            )?
            .ok_or_else(|| invalid("DefinitionValueMembership"))?;
        let (view, equal) =
            self.compile_multivariable_limit_view(&r.function, &proof.function_domain, position)?;
        let values = [&r.function, &r.point, &r.input_dimension, &r.value]
            .into_iter()
            .map(|o| self.compile_function_raw_expression_bound(o, position, &HashMap::new()))
            .collect::<Result<Vec<_>, _>>()?;
        let [f, point, n, value] = values.as_slice() else {
            unreachable!()
        };
        Ok(format!("(by\n{view}\n  have _jacobian_clause : {ty} := {term}\n  refine ⟨{member},?_⟩\n  intro row h_row col h_col\n  have h_partial := _jacobian_clause (Litex.semanticObject row (M.member_isSet h_row)) h_row (Litex.semanticObject col (M.member_isSet h_col)) h_col\n  exact (congrArg (fun D => Litex.HasPartialDerivativeAtValue M (Litex.componentFunctionValue {f} D row) {point} {n} col (Litex.FunctionSemantics.callValue {value} (Litex.FiniteFunction.pack2 row col))) {equal}).mp h_partial\n)"))
    }
}

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("JacobianAt/{stage}"))
}

pub(super) fn matrix_set(rows: &Obj, cols: &Obj) -> Obj {
    Obj::SetFormer(SetFormer::MatrixSet(MatrixSet {
        set: Box::new(Obj::StandardSet(StandardSet::R)),
        rows: Box::new(rows.clone()),
        cols: Box::new(cols.clone()),
    }))
}

pub(super) fn validate_clauses(
    r: &JacobianAtRelation,
    domain: &Obj,
    facts: &[Fact],
) -> Result<(), LeanCompileError> {
    use crate::execute::execute_fact_stmt::multivariable::helper::{apply, indices};
    let [Fact::ForallFact(q)] = facts else {
        return Err(invalid("DefinitionClauses"));
    };
    let [row, col] = q.typed_parameters.groups.as_slice() else {
        return Err(invalid("DefinitionBinders"));
    };
    if !q.dom_facts.is_empty()
        || row.params.len() != 1
        || col.params.len() != 1
        || row.param_type != ParamType::Obj(indices(r.output_dimension.clone()))
        || col.param_type != ParamType::Obj(indices(r.input_dimension.clone()))
        || row.params[0].id == col.params[0].id
    {
        return Err(invalid("DefinitionDomains"));
    }
    let row_obj = Obj::Identifier(IdentifierObj::from_bound_name(&row.params[0]));
    let col_obj = Obj::Identifier(IdentifierObj::from_bound_name(&col.params[0]));
    let [ExistOrAndChainAtomicFact::AtomicFact(a)] = q.then_facts.as_slice() else {
        return Err(invalid("DefinitionConclusion"));
    };
    let (p, negative) =
        super::compile_partial_derivative::parts(a).ok_or_else(|| invalid("DefinitionPartial"))?;
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(component)) = &p.function else {
        return Err(invalid("DefinitionComponent"));
    };
    let [input] = component.body.set_bound_parameters.groups.as_slice() else {
        return Err(invalid("DefinitionComponentParameters"));
    };
    if input.params.len() != 1
        || input.param_type.ir() != domain.ir()
        || !component.body.dom_facts.is_empty()
        || component.body.ret_set.as_ref() != &Obj::StandardSet(StandardSet::R)
    {
        return Err(invalid("DefinitionComponentDomain"));
    }
    let input_obj = Obj::Identifier(IdentifierObj::from_bound_name(&input.params[0]));
    let body = apply(&apply(&r.function, vec![input_obj]), vec![row_obj.clone()]);
    let value = apply(&r.value, vec![row_obj, col_obj.clone()]);
    let ids = [row.params[0].id, col.params[0].id, input.params[0].id];
    if ids[2] == ids[0]
        || ids[2] == ids[1]
        || [
            &r.function,
            &r.point,
            &r.input_dimension,
            &r.output_dimension,
            &r.value,
            domain,
        ]
        .iter()
        .any(|o| ids.iter().any(|id| contains_parameter(o, *id)))
    {
        return Err(invalid("DefinitionCapture"));
    }
    if negative
        || p.point.ir() != r.point.ir()
        || p.dimension.ir() != r.input_dimension.ir()
        || p.coordinate.ir() != col_obj.ir()
        || p.value.ir() != value.ir()
        || component.equal_to.ir() != body.ir()
    {
        return Err(invalid("DefinitionSubject"));
    }
    Ok(())
}
pub(super) fn parts(fact: &AtomicFact) -> Option<(&JacobianAtRelation, bool)> {
    match fact {
        AtomicFact::MultivariableAnalysisFact(f) => {
            if let MultivariableAnalysisRelation::JacobianAt(p) = &f.relation {
                Some((p, false))
            } else {
                None
            }
        }
        AtomicFact::NotMultivariableAnalysisFact(f) => {
            if let MultivariableAnalysisRelation::JacobianAt(p) = &f.relation {
                Some((p, true))
            } else {
                None
            }
        }
        _ => None,
    }
}
fn existence(f: &Obj, p: &Obj, n: &Obj, m: &Obj, fact: &Fact) -> Result<(), LeanCompileError> {
    let Fact::ExistFact(e) = fact else {
        return Err(invalid("Existence"));
    };
    let v = parameter(&e.typed_parameters, &matrix_set(m, n))?;
    if [f, p, n, m].iter().any(|o| contains_parameter(o, v.id)) {
        return Err(invalid("ExistenceCapture"));
    }
    if !matches!(e.facts.as_slice(),[QuantifierFreeFact::AtomicFact(a)] if parts(a).is_some_and(|(r,negative)|!negative&&r.function.ir()==f.ir()&&r.point.ir()==p.ir()&&r.input_dimension.ir()==n.ir()&&r.output_dimension.ir()==m.ir()&&r.value.ir()==Obj::Identifier(IdentifierObj::from_bound_name(v)).ir()))
    {
        return Err(invalid("ExistenceCandidate"));
    }
    Ok(())
}
