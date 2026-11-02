//! Hessian matrices: replay ordered second partials without assuming symmetry.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainProof;
use crate::execute::execute_fact_stmt::multivariable::selector::{
    HessianAtWellDefinedProof, MultivariableSelectorSelectionProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    PredicateDomainRequirementProof, PredicateDomainWellDefinedProof,
};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferMultivariableAnalysisFactResult};
use std::collections::HashMap;
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("HessianAt/{stage}"))
}
pub(super) fn parts(fact: &AtomicFact) -> Option<(&HessianAtRelation, bool)> {
    match fact {
        AtomicFact::MultivariableAnalysisFact(f) => {
            if let MultivariableAnalysisRelation::HessianAt(p) = &f.relation {
                Some((p, false))
            } else {
                None
            }
        }
        AtomicFact::NotMultivariableAnalysisFact(f) => {
            if let MultivariableAnalysisRelation::HessianAt(p) = &f.relation {
                Some((p, true))
            } else {
                None
            }
        }
        _ => None,
    }
}
fn existence(f: &Obj, p: &Obj, n: &Obj, fact: &Fact) -> Result<(), LeanCompileError> {
    let Fact::ExistFact(e) = fact else {
        return Err(invalid("Existence"));
    };
    let v = parameter(&e.typed_parameters, &matrix_set(n))?;
    if [f, p, n].iter().any(|o| contains_parameter(o, v.id)) {
        return Err(invalid("ExistenceCapture"));
    }
    if !matches!(e.facts.as_slice(),[QuantifierFreeFact::AtomicFact(a)] if parts(a).is_some_and(|(r,negative)|!negative&&r.function.ir()==f.ir()&&r.point.ir()==p.ir()&&r.dimension.ir()==n.ir()&&r.value.ir()==Obj::Identifier(IdentifierObj::from_bound_name(v)).ir()))
    {
        return Err(invalid("ExistenceCandidate"));
    }
    Ok(())
}
impl LitexToLeanCompiler {
    pub(super) fn compile_hessian_wd(
        &self,
        object: &HessianAt,
        proof: &HessianAtWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let args = [
            object.function.as_ref(),
            object.point.as_ref(),
            object.dimension.as_ref(),
        ];
        let stages = &proof.stages;
        if stages.argument_well_defined.len() != 3 {
            return Err(invalid("WDArguments"));
        }
        let mut binders = Vec::new();
        for (i, (arg, child)) in args.iter().zip(&stages.argument_well_defined).enumerate() {
            ensure_object(arg, child)?;
            binders.push(format!(
                "let _multivariable_arg_{i} := {}",
                self.compile_wd(
                    child,
                    &SourcePosition {
                        before: i,
                        ..*position
                    }
                )?
            ));
        }
        let mut lines = self.compile_hessian_domain(
            args[0],
            args[1],
            args[2],
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
                    || q.dimension.ir() != args[2].ir()
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
                format!("(Litex.hessianExistsOfCandidate (Litex.denote _multivariable_arg_0) (Litex.denote _multivariable_arg_1) (Litex.denote _multivariable_arg_2) {value} {term})")
            }
            MultivariableSelectorSelectionProof::Existence { fact, proof } => {
                existence(args[0], args[1], args[2], fact)?;
                if source_subject(proof)? != *fact {
                    return Err(invalid("ExistenceProof"));
                }
                let (ty, term) = self.compile_verify(proof, position)?;
                format!("(by obtain ⟨v,hv,hc⟩ := (show {ty} from {term}); exact ⟨v,hv,hc⟩)")
            }
        };
        lines.push(format!(
            "exact ⟨h_{},_multivariable_real,h_{},_hessian_point_domain,{selected}⟩",
            stages.domains[0].requirement.fact_id().value(),
            stages.domains[3].requirement.fact_id().value()
        ));
        Ok(format!(
            "({}; @Litex.Obj.mk M _ (Litex.hessianRepresentation (M := M)) (Litex.HessianObj.mk _multivariable_arg_0 _multivariable_arg_1 _multivariable_arg_2) (by\n  {}\n))",
            binders.join("; "),
            lines.join("\n").replace('\n', "\n  ")
        ))
    }
    pub(super) fn compile_hessian_equality(
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
            (s @ Obj::DerivativeOperator(DerivativeOperator::Hessian(o)), v) => (s, v, o, false),
            (v, s @ Obj::DerivativeOperator(DerivativeOperator::Hessian(o))) => (s, v, o, true),
            _ => return Err(invalid("SelectedSubject")),
        };
        let (candidate, negative) =
            parts(&proof.candidate.fact).ok_or_else(|| invalid("EqualityCandidate"))?;
        if negative
            || candidate.function.ir() != obj.function.ir()
            || candidate.point.ir() != obj.point.ir()
            || candidate.dimension.ir() != obj.dimension.ir()
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
        let term = format!("((Litex.hessianEqCandidate {selected} {raw} {h}).trans {eq})");
        Ok(if reverse {
            format!("{term}.symm")
        } else {
            term
        })
    }
}

fn matrix_set(n: &Obj) -> Obj {
    super::compile_jacobian::matrix_set(n, n)
}
fn index_set(n: &Obj) -> Obj {
    Obj::SetFormer(SetFormer::ClosedRange(ClosedRange {
        start: Box::new(Obj::Literal(Literal::Number(Number {
            normalized_value: "1".into(),
        }))),
        end: Box::new(n.clone()),
    }))
}
fn validate_clauses(r: &HessianAtRelation, facts: &[Fact]) -> Result<(), LeanCompileError> {
    use crate::execute::execute_fact_stmt::multivariable::helper::apply;
    let [Fact::ForallFact(f)] = facts else {
        return Err(invalid("DefinitionClauses"));
    };
    let parameters = f
        .typed_parameters
        .groups
        .iter()
        .flat_map(|g| g.params.iter().map(move |p| (p, &g.param_type)))
        .collect::<Vec<_>>();
    let [(row, row_carrier), (col, col_carrier)] = parameters.as_slice() else {
        return Err(invalid("DefinitionBinders"));
    };
    if !f.dom_facts.is_empty()
        || **row_carrier != ParamType::Obj(index_set(&r.dimension))
        || **col_carrier != ParamType::Obj(index_set(&r.dimension))
        || row.id == col.id
    {
        return Err(invalid("DefinitionDomains"));
    }
    if [&r.function, &r.point, &r.dimension, &r.value]
        .iter()
        .any(|o| contains_parameter(o, row.id) || contains_parameter(o, col.id))
    {
        return Err(invalid("DefinitionCapture"));
    }
    let [ExistOrAndChainAtomicFact::AtomicFact(a)] = f.then_facts.as_slice() else {
        return Err(invalid("DefinitionConclusion"));
    };
    let (p, negative) = super::compile_second_partial::parts(a)
        .ok_or_else(|| invalid("DefinitionSecondPartial"))?;
    let row = Obj::Identifier(IdentifierObj::from_bound_name(row));
    let col = Obj::Identifier(IdentifierObj::from_bound_name(col));
    if negative
        || p.function.ir() != r.function.ir()
        || p.point.ir() != r.point.ir()
        || p.dimension.ir() != r.dimension.ir()
        || p.first_coordinate.ir() != row.ir()
        || p.second_coordinate.ir() != col.ir()
        || p.value.ir() != apply(&r.value, vec![row, col]).ir()
    {
        return Err(invalid("DefinitionSubject"));
    }
    Ok(())
}

impl LitexToLeanCompiler {
    pub(super) fn compile_hessian_domain(
        &self,
        f: &Obj,
        p: &Obj,
        n: &Obj,
        value: Option<&Obj>,
        source: &CompleteFunctionDomainProof,
        requirements: &[PredicateDomainWellDefinedProof],
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let domain = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
            &source.signature,
        )
        .ok_or_else(|| invalid("Signature"))?;
        if requirements.len() != 5 + usize::from(value.is_some()) {
            return Err(invalid("DomainStages"));
        }
        let args = 3 + usize::from(value.is_some());
        let mut lines = self.compile_multivariable_limit_domain(
            f,
            p,
            n,
            None,
            None,
            source,
            &requirements[..4],
            args,
            position,
        )?;
        for (i, r) in requirements.iter().enumerate().skip(4) {
            let valid = match (i, &r.requirement) {
                (4, Fact::AtomicFact(AtomicFact::InFact(q))) => {
                    q.element.ir() == p.ir() && q.set.ir() == domain.ir()
                }
                (5, Fact::AtomicFact(AtomicFact::InFact(q))) => {
                    value.is_some_and(|v| q.element.ir() == v.ir())
                        && q.set.ir() == matrix_set(n).ir()
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
        lines.push(format!("have _hessian_point_domain : M.mem (Litex.denote {p}) (Litex.FunctionSemantics.domainValue (Litex.denote {f})) := (_multivariable_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _multivariable_signature.domain_isSet _multivariable_member).symm) ▸ h_{}",requirements[4].requirement.fact_id().value()));
        Ok(lines)
    }
    pub(super) fn compile_hessian_inferences(
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
            .map(|store| {
                let f = self.resolve_fact(store.primary_fact_id(), position)?;
                self.validate_store(&store.store, &f)?;
                Ok(f)
            })
            .collect::<Result<Vec<_>, LeanCompileError>>()?;
        let mut lines = Vec::new();
        if p.function_domain.is_some() {
            validate_clauses(r, &facts[..1])?;
            let ty = self.compile_function_raw_predicate(&facts[0], position, &HashMap::new())?;
            let term = format!(
                "(by intro row h_row col h_col; exact ({}).2 row h_row col h_col)",
                compiled.1
            );
            lines.push(self.emit_internal_fact(&facts[0], &(ty, term), position)?);
        }
        let target = facts.last().unwrap();
        existence(&r.function, &r.point, &r.dimension, target)?;
        let ty = self.compile_function_raw_predicate(target, position, &HashMap::new())?;
        let args = [&r.function, &r.point, &r.dimension, &r.value]
            .into_iter()
            .map(|o| self.compile_function_raw_expression_bound(o, position, &HashMap::new()))
            .collect::<Result<Vec<_>, _>>()?
            .join(" ");
        let term = format!(
            "(by obtain ⟨v,hv,hc⟩ := Litex.hessianExistsOfCandidate {args} {}; exact ⟨v,hv,hc⟩)",
            compiled.1
        );
        lines.push(self.emit_internal_fact(target, &(ty, term), position)?);
        Ok(lines)
    }
    pub(super) fn compile_hessian_definition(
        &self,
        r: &HessianAtRelation,
        proof:&crate::execute::execute_fact_stmt::multivariable::definition::HessianAtRelationDefinitionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        validate_clauses(r, &proof.requirement_facts)?;
        let [child] = proof.proof_of_requirement_facts.as_slice() else {
            return Err(invalid("DefinitionProofCount"));
        };
        if source_subject(child)? != proof.requirement_facts[0] {
            return Err(invalid("DefinitionProofSubject"));
        }
        let (ty, proof) = self.compile_verify(child, &position.atomic_search_prior(0)?)?;
        let member = position
            .with_visible_membership(&r.value, &matrix_set(&r.dimension), &mut |p, at| {
                self.compile_verify(p, at).map(|v| v.1)
            })?
            .ok_or_else(|| invalid("DefinitionValueMembership"))?;
        Ok(format!("(by\n  have _hessian_clause : {ty} := {proof}\n  refine ⟨{member},?_⟩\n  intro row h_row col h_col\n  exact _hessian_clause (Litex.semanticObject row (M.member_isSet h_row)) h_row (Litex.semanticObject col (M.member_isSet h_col)) h_col\n)"))
    }
}
