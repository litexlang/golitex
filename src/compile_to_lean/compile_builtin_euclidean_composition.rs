//! Replay exact Euclidean composition contexts, mapping and function equation.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::compile_sequence_analysis::call_matches;
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::function_domain::{
    function_domains_alpha_equal, CompleteFunctionDomainProof,
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
    LeanCompileError::unsupported(&format!("EuclideanComposition/{stage}"))
}
fn stage(mut error: LeanCompileError, stage: impl std::fmt::Display) -> LeanCompileError {
    error.message = format!("Euclidean composition {stage}: {}", error.message);
    error
}
fn same(a: &Obj, b: &Obj) -> bool {
    a.ir()==b.ir() || crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::compound_objs_alpha_equal(a,b)
}
fn candidate<'a>(
    fact: &'a Fact,
    name: &str,
    args: &[Obj],
) -> Result<&'a MultivariableAnalysisRelation, LeanCompileError> {
    let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(f)) = fact else {
        return Err(invalid("PositiveCandidate"));
    };
    let r = &f.relation;
    if r.predicate_name() != name
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
fn captured_domain<'a>(
    store: &'a StoreFactAndInferResult,
    fact: &Fact,
    derived: usize,
) -> Result<&'a CompleteFunctionDomainProof, LeanCompileError> {
    let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(rules))) =
        &store.infer
    else {
        return Err(invalid("OriginalInference"));
    };
    let [InferMultivariableAnalysisFactResult::Definition(c)] = rules.as_slice() else {
        return Err(invalid("OriginalInference"));
    };
    if c.source_fact_id != fact.fact_id() || c.derived.len() != derived {
        return Err(invalid("OriginalInferenceIdentity"));
    }
    c.function_domain
        .as_ref()
        .ok_or_else(|| invalid("OriginalCompleteDomain"))
}
fn clauses(
    req: &[Fact],
    domain: &Obj,
    outer_domain: &Obj,
    args: &[Obj],
) -> Result<(), LeanCompileError> {
    for (index, fact) in req.iter().enumerate() {
        let Fact::ForallFact(all) = fact else {
            return Err(invalid("OriginalForall"));
        };
        let x = parameter(&all.typed_parameters, domain)?;
        if !all.dom_facts.is_empty()
            || args
                .iter()
                .chain([domain, outer_domain])
                .any(|a| contains_parameter(a, x.id))
        {
            return Err(invalid("ClauseCapture"));
        }
        let input = Obj::Identifier(IdentifierObj::from_bound_name(x));
        let inner = schema::apply(&args[0], vec![input.clone()]);
        if index == 0 {
            if !matches!(all.then_facts.as_slice(),[ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(f))]
                if f.element.ir()==inner.ir() && same(&f.set,outer_domain))
            {
                return Err(invalid("OriginalRangeMapping"));
            }
        } else if !matches!(all.then_facts.as_slice(),[ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(f))]
            if call_matches(&f.left,&args[2],&input) && f.right.ir()==schema::apply(&args[1],vec![inner]).ir())
        {
            return Err(invalid("OriginalCompositionEquation"));
        }
    }
    Ok(())
}
impl LitexToLeanCompiler {
    fn euclidean_composition_domain_view(
        &self,
        f: &Obj,
        source: &CompleteFunctionDomainProof,
        prefix: &str,
        scope: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let domain =
            schema::actual_domain(&source.signature).ok_or_else(|| invalid("ActualDomain"))?;
        let signature = self.compile_complete_domain_signature(source, scope)?;
        let member = self.compile_complete_domain_member(f, source, scope)?;
        self.compile_named_limit_domain_view(
            f,
            &domain,
            &source.signature,
            &signature,
            &member,
            prefix,
            scope,
        )
    }
    pub(super) fn compile_builtin_euclidean_composition(
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
        let (vector, limit, law) = match builtin.theorem {
            MultiContinuousAtCompose => (false, false, "scalarMultivariableContinuityCompose"),
            MultiLimitAtCompose => (false, true, "scalarMultivariableLimitCompose"),
            VectorContinuousAtCompose => (true, false, "vectorMultivariableContinuityCompose"),
            VectorLimitAtCompose => (true, true, "vectorMultivariableLimitCompose"),
            _ => return Err(invalid("Identity")),
        };
        let context = 4 + usize::from(vector) + usize::from(!limit);
        let outer_start = context + 1;
        let outer_index = outer_start + if vector { 6 } else { 1 };
        let output_start = outer_index + 1;
        let mapping = output_start + context;
        let count = mapping + 2;
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
        let req = &builtin.requirements;
        let name = match (vector, limit) {
            (false, false) => "is_multi_continuous_at",
            (false, true) => "has_multi_limit_at",
            (true, false) => "is_vector_continuous_at",
            (true, true) => "has_vector_limit_at",
        };
        let at = if limit {
            args.last().unwrap().clone()
        } else {
            schema::apply(&args[0], vec![args[3].clone()])
        };
        let mut input = vec![args[0].clone(), args[3].clone(), args[4].clone()];
        let mut output = vec![args[2].clone(), args[3].clone(), args[4].clone()];
        if vector {
            input.push(args[5].clone());
            output.push(args[6].clone());
        }
        if limit {
            input.push(at.clone());
            output.push(schema::apply(&args[1], vec![at.clone()]));
        }
        let inner = candidate(&req[context], name, &input)?;
        candidate(&builtin.conclusions[0], name, &output)?;
        let source = captured_domain(
            &dom_stores[context],
            &req[context],
            if limit { 3 } else { 1 },
        )?;
        if limit {
            super::compile_multivariable_limit_context::validate_limit_context(
                &input,
                &req[..context],
                source,
                vector.then(|| &args[5]),
            )?;
        } else {
            super::compile_builtin_derivative_schema::validate_context(
                inner,
                &req[..context],
                source,
            )?;
        }
        let Fact::AtomicFact(atomic) = &builtin.conclusions[0] else {
            unreachable!()
        };
        let FactWellDefinedProof::AtomicExceptEquality(wd) = &conclusions_wd[0] else {
            return Err(invalid("OriginalFormation"));
        };
        let PredicateDomainProof::MultivariableAnalysis(formation) = &wd
            .as_detailed()
            .map_err(|_| invalid("DetailedFormation"))?
            .predicate_domain
        else {
            return Err(invalid("OriginalFormationDomain"));
        };
        if formation.requirements.len()!=context+usize::from(limit)
            || !req[output_start..mapping].iter().zip(&formation.requirements[..context]).all(|(a,b)|crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::quantifier_free_source_facts_alpha_equal(a,&b.requirement)) {return Err(invalid("OriginalOutputContext"));}
        let output_source = &formation.function_domain;
        if !function_domains_alpha_equal(&source.signature, &output_source.signature) {
            return Err(invalid("OriginalCommonDomain"));
        }
        let output_r = candidate(&builtin.conclusions[0], name, &output)?;
        if limit {
            super::compile_multivariable_limit_context::validate_limit_context(
                &output,
                &req[output_start..mapping],
                output_source,
                vector.then(|| &args[6]),
            )?;
        } else {
            super::compile_builtin_derivative_schema::validate_context(
                output_r,
                &req[output_start..mapping],
                output_source,
            )?;
        }
        let domain = schema::actual_domain(&source.signature)
            .ok_or_else(|| invalid("OriginalInputDomain"))?;
        let mut scalar_point = None;
        let outer_domain;
        if vector {
            let outer_args = vec![
                args[1].clone(),
                at.clone(),
                args[5].clone(),
                args[6].clone(),
            ];
            let outer = candidate(&req[outer_index], "is_vector_continuous_at", &outer_args)?;
            let outer_source = captured_domain(&dom_stores[outer_index], &req[outer_index], 1)?;
            super::compile_builtin_derivative_schema::validate_context(
                outer,
                &req[outer_start..outer_index],
                outer_source,
            )?;
            outer_domain = schema::actual_domain(&outer_source.signature)
                .ok_or_else(|| invalid("OriginalOuterDomain"))?;
        } else {
            if !matches!(&req[outer_index],Fact::AtomicFact(AtomicFact::FunctionContinuousAtFact(f))
                if f.side==RealApproachSide::Both && f.function.ir()==args[1].ir() && f.point.ir()==at.ir())
            {
                return Err(invalid("OriginalOuterContinuity"));
            }
            let VerifyFactResult::AtomicExceptEquality(proof) = &dom_proofs[outer_index] else {
                return Err(invalid("OriginalOuterProof"));
            };
            let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_ref() else {
                return Err(invalid("OriginalOuterProof"));
            };
            let prior = SourcePosition {
                before: outer_index,
                ..*position
            };
            let point = self.compile_continuity_point_formation(
                &proof.fact,
                &proof.well_defined_proof,
                &prior,
            )?;
            outer_domain = point.domain.clone();
            if !matches!(&req[outer_start],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==at.ir() && same(&f.set,&outer_domain))
            {
                return Err(invalid("OriginalOuterPointDomain"));
            }
            scalar_point = Some(point);
        }
        clauses(&req[mapping..], &domain, &outer_domain, args)?;
        let value_member = if limit {
            let r = &formation.requirements[context];
            let carrier = schema::value_carrier(output_r);
            if !matches!(&r.requirement,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==output.last().unwrap().ir() && f.set.ir()==carrier.ir())
            {
                return Err(invalid("OriginalOutputValueCarrier"));
            }
            let PredicateDomainRequirementProof::Verified(p) = &r.result else {
                return Err(invalid("OriginalOutputValueProof"));
            };
            if source_subject(p)? != r.requirement {
                return Err(invalid("OriginalOutputValueSubject"));
            }
            Some(r.requirement.fact_id())
        } else {
            None
        };
        let mut definitions = Vec::new();
        for (i, ((fact, proof), store)) in req.iter().zip(dom_proofs).zip(dom_stores).enumerate() {
            if source_subject(proof)? != *fact {
                return Err(invalid("OriginalProofSubject"));
            }
            let prior = SourcePosition {
                before: i,
                ..*position
            };
            let compiled = self
                .compile_verify(proof, &prior)
                .map_err(|e| stage(e, format!("requirement {i}")))?;
            self.validate_store(&store.store, fact)?;
            definitions.push(self.emit_internal_fact(fact, &compiled, &prior)?);
            definitions.extend(
                self.compile_stored_inferences(
                    store,
                    fact,
                    &(compiled.0, format!("h_{}", fact.fact_id().value())),
                    &SourcePosition {
                        before: i + 1,
                        ..*position
                    },
                )
                .map_err(|e| stage(e, format!("inference {i}")))?,
            );
        }
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], &builtin.conclusions[0], &formed)
            .map_err(|e| stage(e, "conclusion formation"))?;
        let bindings = self
            .compile_atomic_wd_locals(wd, atomic, &formed)
            .map_err(|e| stage(e, "conclusion formation bindings"))?;
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::AtomicWDLocals(wd, output.len()),
            usize::MAX,
        );
        let objects = args
            .iter()
            .map(|o| self.compile_object_reference(o, &scope))
            .collect::<Result<Vec<_>, _>>()?;
        let raw = objects
            .iter()
            .map(|s| format!("(Litex.denote {s})"))
            .collect::<Vec<_>>()
            .join(" ");
        let (inner_view, inner_eq) = self
            .euclidean_composition_domain_view(&args[0], source, "composition_inner_", &scope)
            .map_err(|e| stage(e, "inner domain"))?;
        let (output_view, output_eq) = self
            .euclidean_composition_domain_view(
                &args[2],
                output_source,
                "composition_output_",
                &scope,
            )
            .map_err(|e| stage(e, "output domain"))?;
        let mut lines = vec![inner_view, output_view];
        lines.push(format!("  have _composition_domains : Litex.FunctionSemantics.domainValue (Litex.denote {}) = Litex.FunctionSemantics.domainValue (Litex.denote {}) := ({output_eq}).symm.trans ((show _composition_output_source_domain = _composition_inner_source_domain from by rfl).trans {inner_eq})",objects[2],objects[0]));
        let outer_eq = if vector {
            let outer_source = captured_domain(&dom_stores[outer_index], &req[outer_index], 1)?;
            let (view, eq) = self
                .euclidean_composition_domain_view(
                    &args[1],
                    outer_source,
                    "composition_outer_",
                    &scope,
                )
                .map_err(|e| stage(e, "outer domain"))?;
            lines.push(view);
            eq
        } else {
            let point = scalar_point.unwrap();
            lines.extend(
                point
                    .bindings
                    .iter()
                    .map(|s| format!("  {}", s.replace('\n', "\n  "))),
            );
            // Point formation emits the original real-function certificate and domain view.
            lines.push(format!(
                "  have _composition_outer_real := {}",
                point.real_function
            ));
            point.domain_equality
        };
        let map_id = req[mapping].fact_id().value();
        let formula_id = req[mapping + 1].fact_id().value();
        lines.push(format!("  have _composition_maps : ∀ x, M.mem x (Litex.FunctionSemantics.domainValue (Litex.denote {})) → M.mem (Litex.FunctionSemantics.callValue (Litex.denote {}) x) (Litex.FunctionSemantics.domainValue (Litex.denote {})) := by\n    intro x hx\n    have hs : M.mem x _composition_inner_source_domain := ({inner_eq}).symm ▸ hx\n    exact {outer_eq} ▸ (h_{map_id} (Litex.semanticObject x (M.member_isSet hs)) hs)",objects[0],objects[0],objects[1]));
        lines.push(format!("  have _composition_formula : ∀ x, M.mem x (Litex.FunctionSemantics.domainValue (Litex.denote {})) → Litex.FunctionSemantics.callValue (Litex.denote {}) x = Litex.FunctionSemantics.callValue (Litex.denote {}) (Litex.FunctionSemantics.callValue (Litex.denote {}) x) := by\n    intro x hx\n    have hs : M.mem x _composition_inner_source_domain := ({inner_eq}).symm ▸ hx\n    exact h_{formula_id} (Litex.semanticObject x (M.member_isSet hs)) hs",objects[0],objects[2],objects[1],objects[0]));
        let real = if vector {
            String::new()
        } else {
            " _composition_outer_real".into()
        };
        let specific = if limit {
            format!(" h_{}", value_member.unwrap().value())
        } else {
            format!(" ({inner_eq} ▸ h_{})", req[context - 1].fact_id().value())
        };
        lines.push(format!("  exact Litex.{law} {raw}{real} _composition_domains{specific} _composition_maps _composition_formula h_{} h_{}",req[context].fact_id().value(),req[outer_index].fact_id().value()));
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        // Atomic formation includes both object lets and checked predicate facts.
        // Emit its complete ordered block; the equality helper accepts only lets.
        let proof = format!(
            "(by\n  {}\n  exact (by\n  {}\n  )\n)",
            bindings.join("\n").replace('\n', "\n  "),
            lines.join("\n").replace('\n', "\n  ")
        );
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}
