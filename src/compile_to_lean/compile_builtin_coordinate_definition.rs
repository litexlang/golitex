//! Coordinate definitions consume the original clauses and their ordered evidence.
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
    LeanCompileError::unsupported(&format!("CoordinateDefinition/{stage}"))
}
fn relation(fact: &Fact) -> Result<&MultivariableAnalysisRelation, LeanCompileError> {
    let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(f)) = fact else {
        return Err(invalid("PositiveCandidate"));
    };
    Ok(&f.relation)
}
fn clauses(
    r: &MultivariableAnalysisRelation,
    domain: &Obj,
    facts: &[Fact],
) -> Result<(), LeanCompileError> {
    match r {
        MultivariableAnalysisRelation::GradientAt(r) => {
            super::compile_gradient::validate_clauses(r, facts)
        }
        MultivariableAnalysisRelation::HessianAt(r) => {
            super::compile_hessian::validate_clauses(r, facts)
        }
        MultivariableAnalysisRelation::JacobianAt(r) => {
            super::compile_jacobian::validate_clauses(r, domain, facts)
        }
        MultivariableAnalysisRelation::DivergenceAt(r) => {
            super::compile_divergence::validate_clauses(r, domain, facts)
        }
        MultivariableAnalysisRelation::LaplacianAt(r) => {
            super::compile_laplacian::validate_clauses(r, facts)
        }
        MultivariableAnalysisRelation::CurlAt(r) => {
            super::compile_curl::validate_clauses(r, domain, facts)
        }
        _ => Err(invalid("Family")),
    }
}

impl LitexToLeanCompiler {
    // All stored coordinate universals use the same semantic-object convention
    // as original source forall citations; their bodies retain native predicates.
    pub(super) fn compile_coordinate_clause_value_proposition(
        &self,
        fact: &Fact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Fact::ForallFact(f) = fact else {
            return Err(invalid("ClauseForall"));
        };
        if !f.dom_facts.is_empty() || f.then_facts.len() != 1 {
            return Err(invalid("ClauseBody"));
        }
        let mut bound = HashMap::new();
        let mut heads = Vec::new();
        for group in &f.typed_parameters.groups {
            let ParamType::Obj(carrier) = &group.param_type else {
                return Err(invalid("ClauseCarrier"));
            };
            for parameter in &group.params {
                let set = self.compile_function_raw_expression_bound(carrier, position, &bound)?;
                let name = format!("_coordinate_i{}", parameter.id.value());
                heads.push(format!("∀ ({name} : Litex.Obj (M := M) M.Value), M.mem (Litex.denote {name}) ({set}) →"));
                bound.insert(parameter.id, format!("(Litex.denote {name})"));
            }
        }
        if heads.is_empty() {
            return Err(invalid("ClauseBinders"));
        }
        let body =
            self.compile_function_raw_predicate(&f.then_facts[0].clone().into(), position, &bound)?;
        Ok(format!("{} ({body})", heads.join(" ")))
    }
    pub(super) fn compile_builtin_coordinate_definition(
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
            GradientAtFromDefinition => {
                (true, "has_gradient_at", "gradientOfCoordinatePartials", 5)
            }
            GradientAtToDefinition => (false, "has_gradient_at", "gradientCoordinatePartials", 5),
            HessianAtFromDefinition => (true, "has_hessian_at", "hessianOfOrderedPartials", 5),
            HessianAtToDefinition => (false, "has_hessian_at", "hessianOrderedPartials", 5),
            JacobianAtFromDefinition => (true, "has_jacobian_at", "jacobianOfComponentPartials", 6),
            JacobianAtToDefinition => (false, "has_jacobian_at", "jacobianComponentPartials", 6),
            DivergenceAtFromDefinition => {
                (true, "has_divergence_at", "divergenceOfDiagonalPartials", 6)
            }
            DivergenceAtToDefinition => {
                (false, "has_divergence_at", "divergenceDiagonalPartials", 6)
            }
            LaplacianAtFromDefinition => {
                (true, "has_laplacian_at", "laplacianOfDiagonalPartials", 5)
            }
            LaplacianAtToDefinition => (false, "has_laplacian_at", "laplacianDiagonalPartials", 5),
            CurlAtFromDefinition => (true, "has_curl_at", "curlOfCoordinatePartials", 6),
            CurlAtToDefinition => (false, "has_curl_at", "curlCoordinatePartials", 6),
            _ => return Err(invalid("Identity")),
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
            || args.len() != builtin.theorem.arity()
            || builtin.requirements.len() != context + 1
            || dom_proofs.len() != context + 1
            || dom_stores.len() != context + 1
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("OriginalStages"));
        }
        let r = relation(if fold {
            &builtin.conclusions[0]
        } else {
            &builtin.requirements[context]
        })?;
        if r.predicate_name() != predicate
            || !r
                .argument_refs()
                .iter()
                .zip(args)
                .all(|(a, b)| a.ir() == b.ir())
        {
            return Err(invalid("OriginalArguments"));
        }
        let mut original_value_member = None;
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
            if capture.requirements.len()!=context+1 || !builtin.requirements[..context].iter().zip(&capture.requirements[..context]).all(|(a,b)| crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::quantifier_free_source_facts_alpha_equal(a,&b.requirement)) {
                return Err(invalid("OriginalContext"));
            }
            let member = &capture.requirements[context];
            let expected =
                crate::execute::execute_fact_stmt::multivariable::helper::value_carrier(r);
            if !matches!(&member.requirement, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==args.last().unwrap().ir() && f.set.ir()==expected.ir())
            {
                return Err(invalid("ValueCarrier"));
            }
            let PredicateDomainRequirementProof::Verified(proof) = &member.result else {
                return Err(invalid("ValueMembershipCapture"));
            };
            if source_subject(proof)? != member.requirement {
                return Err(invalid("ValueMembershipSubject"));
            }
            original_value_member = Some(proof);
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
                || capture.derived.len() != 2
            {
                return Err(invalid("OriginalInferenceIdentity"));
            }
            capture
                .function_domain
                .as_ref()
                .ok_or_else(|| invalid("OriginalCompleteDomain"))?
        };
        let domain = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
            &source.signature,
        )
        .ok_or_else(|| invalid("ActualDomain"))?;
        clauses(
            r,
            &domain,
            if fold {
                &builtin.requirements[context..]
            } else {
                &builtin.conclusions
            },
        )?;
        super::compile_builtin_derivative_schema::validate_context(
            r,
            &builtin.requirements[..context],
            source,
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
            before: context + 1,
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], &builtin.conclusions[0], &formed)?;
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let raw_arguments = args
            .iter()
            .map(|a| {
                self.compile_object_reference(a, &scope)
                    .map(|a| format!("(Litex.denote {a})"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let raw = raw_arguments.join(" ");
        let original = format!("h_{}", builtin.requirements[context].fact_id().value());
        let hessian = matches!(r, MultivariableAnalysisRelation::HessianAt(_));
        let proof = if matches!(
            r,
            MultivariableAnalysisRelation::DivergenceAt(_)
                | MultivariableAnalysisRelation::LaplacianAt(_)
        ) {
            let divergence = matches!(r, MultivariableAnalysisRelation::DivergenceAt(_));
            let (view, equal) = if divergence {
                self.compile_multivariable_limit_view(&args[0], source, &scope)?
            } else {
                (String::new(), String::new())
            };
            let f = &raw_arguments[0];
            let point = &raw_arguments[1];
            let n = &raw_arguments[2];
            if let Some(member) = original_value_member {
                let FactWellDefinedProof::AtomicExceptEquality(wd) = &conclusions_wd[0] else {
                    unreachable!()
                };
                let stage = SourcePosition::new(
                    Some(&formed),
                    SourceOwner::AtomicWD(wd),
                    args.len() + context,
                );
                let member = self.compile_verify(member, &stage)?.1;
                let finish = if divergence {
                    format!("  exact (congrArg (fun D => Litex.HasPartialDerivativeAtValue M (Litex.componentFunctionValue {f} D k) {point} {n} k (Litex.FunctionSemantics.callValue (Litex.denote diagonal) k)) {equal}).mp h_partial")
                } else {
                    "  exact h_partial".to_string()
                };
                format!("(by\n{view}\n  apply Litex.{law} {raw} {member}\n  obtain ⟨diagonal,h_diagonal,h_parts,h_sum⟩ := {original}\n  refine ⟨diagonal,h_diagonal,?_,h_sum⟩\n  intro k h_k\n  have h_partial := ((Litex.SetSemantics.sep_members _ _ _).mp (h_parts k h_k)).2.2\n{finish}\n)")
            } else {
                let partial = if divergence {
                    format!("((congrArg (fun D => Litex.HasPartialDerivativeAtValue M (Litex.componentFunctionValue {f} D k) {point} {n} k (Litex.FunctionSemantics.callValue (Litex.denote diagonal) k)) {equal}).mpr (h_parts k h_k))")
                } else {
                    "(h_parts k h_k)".to_string()
                };
                format!("(by\n{view}\n  obtain ⟨diagonal,h_diagonal,h_parts,h_sum⟩ := Litex.{law} {raw} {original}\n  refine ⟨diagonal,h_diagonal,?_,h_sum⟩\n  change ∀ k : M.Value, M.mem k _ → M.mem k _\n  intro k h_k\n  exact (Litex.SetSemantics.sep_members _ _ _).mpr ⟨h_k,h_k,{partial}⟩\n)")
            }
        } else if matches!(r, MultivariableAnalysisRelation::CurlAt(_)) {
            let (view, equal) = self.compile_multivariable_limit_view(&args[0], source, &scope)?;
            let f = &raw_arguments[0];
            let point = &raw_arguments[1];
            let value = &raw_arguments[2];
            if let Some(member) = original_value_member {
                let FactWellDefinedProof::AtomicExceptEquality(wd) = &conclusions_wd[0] else {
                    unreachable!()
                };
                let stage = SourcePosition::new(
                    Some(&formed),
                    SourceOwner::AtomicWD(wd),
                    args.len() + context,
                );
                let member = self.compile_verify(member, &stage)?.1;
                format!("(by\n{view}\n  apply Litex.{law} {raw} {member}\n  exact (congrArg (fun D => Litex.CurlDefinitionValue M {f} D {point} {value}) {equal}).mp {original}\n)")
            } else {
                format!("(by\n{view}\n  exact (congrArg (fun D => Litex.CurlDefinitionValue M {f} D {point} {value}) {equal}).mpr (Litex.{law} {raw} {original})\n)")
            }
        } else if matches!(r, MultivariableAnalysisRelation::JacobianAt(_)) {
            let (view, equal) = self.compile_multivariable_limit_view(&args[0], source, &scope)?;
            let f = &raw_arguments[0];
            let point = &raw_arguments[1];
            let n = &raw_arguments[2];
            let value = &raw_arguments[4];
            if let Some(member) = original_value_member {
                let FactWellDefinedProof::AtomicExceptEquality(wd) = &conclusions_wd[0] else {
                    unreachable!()
                };
                let stage = SourcePosition::new(
                    Some(&formed),
                    SourceOwner::AtomicWD(wd),
                    args.len() + context,
                );
                let member = self.compile_verify(member, &stage)?.1;
                format!("(by\n{view}\n  apply Litex.{law} {raw} {member}\n  intro row h_row col h_col\n  have h_partial := {original} (Litex.semanticObject row (M.member_isSet h_row)) h_row (Litex.semanticObject col (M.member_isSet h_col)) h_col\n  exact (congrArg (fun D => Litex.HasPartialDerivativeAtValue M (Litex.componentFunctionValue {f} D row) {point} {n} col (Litex.FunctionSemantics.callValue {value} (Litex.FiniteFunction.pack2 row col))) {equal}).mp h_partial\n)")
            } else {
                format!("(by\n{view}\n  have _coordinates := Litex.{law} {raw} {original}\n  intro _Row _row_rep row h_row _Col _col_rep col h_col\n  have h_partial := _coordinates (Litex.denote row) h_row (Litex.denote col) h_col\n  exact (congrArg (fun D => Litex.HasPartialDerivativeAtValue M (Litex.componentFunctionValue {f} D (Litex.denote row)) {point} {n} (Litex.denote col) (Litex.FunctionSemantics.callValue {value} (Litex.FiniteFunction.pack2 (Litex.denote row) (Litex.denote col)))) {equal}).mpr h_partial\n)")
            }
        } else if let Some(member) = original_value_member {
            let FactWellDefinedProof::AtomicExceptEquality(wd) = &conclusions_wd[0] else {
                unreachable!()
            };
            let stage = SourcePosition::new(
                Some(&formed),
                SourceOwner::AtomicWD(wd),
                args.len() + context,
            );
            let member = self.compile_verify(member, &stage)?.1;
            let body = if hessian {
                format!("  intro row h_row col h_col\n  exact {original} (Litex.semanticObject row (M.member_isSet h_row)) h_row (Litex.semanticObject col (M.member_isSet h_col)) h_col")
            } else {
                format!("  intro coordinate h_coordinate\n  exact {original} (Litex.semanticObject coordinate (M.member_isSet h_coordinate)) h_coordinate")
            };
            format!("(by\n  apply Litex.{law} {raw} {member}\n{body}\n)")
        } else {
            let body = if hessian {
                "  intro _Row _row_rep row h_row _Col _col_rep col h_col\n  exact _coordinates (Litex.denote row) h_row (Litex.denote col) h_col"
            } else {
                "  intro _Host _rep coordinate h_coordinate\n  exact _coordinates (Litex.denote coordinate) h_coordinate"
            };
            format!("(by\n  have _coordinates := Litex.{law} {raw} {original}\n{body}\n)")
        };
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}
