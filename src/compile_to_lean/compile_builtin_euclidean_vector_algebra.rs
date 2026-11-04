//! Replay vector Euclidean algebra from its unchanged ordered NativeSchema.
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
    MultivariableAnalysisPredicateDomainProof, PredicateDomainProof,
    PredicateDomainRequirementProof,
};
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
};

#[derive(Clone, Copy)]
enum Operation {
    Add,
    Subtract,
}
impl Operation {
    fn field(self) -> &'static str {
        match self {
            Self::Add => "addValue",
            Self::Subtract => "subValue",
        }
    }
    fn closure(self) -> &'static str {
        match self {
            Self::Add => "addInR",
            Self::Subtract => "subInR",
        }
    }
    fn matches(self, obj: &Obj, a: &Obj, b: &Obj) -> bool {
        let (left, right) = match (self, obj) {
            (Self::Add, Obj::ArithmeticOperator(ArithmeticOperator::Add(x))) => (&x.left, &x.right),
            (Self::Subtract, Obj::ArithmeticOperator(ArithmeticOperator::Sub(x))) => {
                (&x.left, &x.right)
            }
            _ => return false,
        };
        left.ir() == a.ir() && right.ir() == b.ir()
    }
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("EuclideanVectorAlgebra/{stage}"))
}
fn stage(mut error: LeanCompileError, stage: impl std::fmt::Display) -> LeanCompileError {
    error.message = format!("Euclidean vector algebra {stage}: {}", error.message);
    error
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
fn source_domain<'a>(
    store: &'a StoreFactAndInferResult,
    fact: &Fact,
    derived: usize,
) -> Result<&'a CompleteFunctionDomainProof, LeanCompileError> {
    let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(rules))) =
        &store.infer
    else {
        return Err(invalid("OriginalInference"));
    };
    let [InferMultivariableAnalysisFactResult::Definition(p)] = rules.as_slice() else {
        return Err(invalid("OriginalInference"));
    };
    if p.source_fact_id != fact.fact_id() || p.derived.len() != derived {
        return Err(invalid("OriginalInferenceIdentity"));
    }
    p.function_domain
        .as_ref()
        .ok_or_else(|| invalid("OriginalCompleteDomain"))
}
fn vector_formula(
    obj: &Obj,
    a: &Obj,
    b: &Obj,
    m: &Obj,
    op: Operation,
) -> Result<(), LeanCompileError> {
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(literal)) = obj else {
        return Err(invalid("OriginalCoordinateFormula"));
    };
    let [group] = literal.body.set_bound_parameters.groups.as_slice() else {
        return Err(invalid("CoordinateBinder"));
    };
    let [binder] = group.params.as_slice() else {
        return Err(invalid("CoordinateBinder"));
    };
    let Obj::SetFormer(SetFormer::ClosedRange(range)) = group.param_type.as_ref() else {
        return Err(invalid("CoordinateInterval"));
    };
    if closed_integer(&range.start) != Some(1)
        || range.end.ir() != m.ir()
        || literal.body.ret_set.as_ref() != &Obj::StandardSet(StandardSet::R)
        || !literal.body.dom_facts.is_empty()
        || [a, b, m].iter().any(|o| contains_parameter(o, binder.id))
    {
        return Err(invalid("ExactCoordinateDomain"));
    }
    let k = schema::identifier(binder);
    if !op.matches(
        &literal.equal_to,
        &schema::apply(a, vec![k.clone()]),
        &schema::apply(b, vec![k]),
    ) {
        return Err(invalid("ExactCoordinateOperation"));
    }
    Ok(())
}

impl LitexToLeanCompiler {
    // Borrow the exact earlier WD owner. The existing citation consumer checks
    // visibility and all argument equality certificates before this reader runs.
    // This leaf currently supports identity/alpha citations; distinct semantic
    // argument transports remain unsupported rather than changing the source route.
    fn with_vector_algebra_output_formation<T>(
        &self,
        fact: &AtomicFact,
        wd: &AtomicFactWellDefinedProof,
        position: &SourcePosition<'_>,
        callback: &mut impl FnMut(
            &MultivariableAnalysisPredicateDomainProof,
            &AtomicFact,
            &AtomicFactWellDefinedProof,
            &SourcePosition<'_>,
        ) -> Result<T, LeanCompileError>,
    ) -> Result<T, LeanCompileError> {
        match &wd
            .as_detailed()
            .map_err(|_| invalid("DetailedFormation"))?
            .predicate_domain
        {
            PredicateDomainProof::MultivariableAnalysis(formation) => {
                callback(formation, fact, wd, position)
            }
            PredicateDomainProof::ByKnownFact(cite) => {
                let AtomicFact::MultivariableAnalysisFact(property) = fact else {
                    return Err(invalid("CitedFormationFamily"));
                };
                let formed = SourcePosition::new(
                    Some(position),
                    SourceOwner::AtomicWDLocals(wd, property.relation.argument_refs().len()),
                    usize::MAX,
                );
                self.compile_known_atomic(cite, fact, &formed)?;
                let mut previous = |source: &AtomicFact,
                                    source_wd: &AtomicFactWellDefinedProof,
                                    prior: &SourcePosition<'_>| {
                    let (
                        AtomicFact::MultivariableAnalysisFact(old),
                        AtomicFact::MultivariableAnalysisFact(current),
                    ) = (source, fact)
                    else {
                        return Err(invalid("CitedFormationFamily"));
                    };
                    let a = old.relation.argument_refs();
                    let b = current.relation.argument_refs();
                    if old.relation.predicate_name()!=current.relation.predicate_name() || a.len()!=b.len() || !a.iter().zip(b).all(|(x,y)|x.ir()==y.ir() || crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::compound_objs_alpha_equal(x,y)) {
                        return Err(invalid("CitedFormationArgumentIdentity"));
                    }
                    self.with_vector_algebra_output_formation(source, source_wd, prior, callback)
                };
                self.with_cited_atomic_formation(cite.cite_fact_id, &formed, &mut previous)
            }
            _ => Err(invalid("OriginalFormationDomain")),
        }
    }
    fn vector_algebra_domain_view(
        &self,
        f: &Obj,
        proof: &CompleteFunctionDomainProof,
        prefix: &str,
        scope: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let domain =
            schema::actual_domain(&proof.signature).ok_or_else(|| invalid("ActualDomain"))?;
        let signature = self.compile_complete_domain_signature(proof, scope)?;
        let member = self.compile_complete_domain_member(f, proof, scope)?;
        self.compile_named_limit_domain_view(
            f,
            &domain,
            &proof.signature,
            &signature,
            &member,
            prefix,
            scope,
        )
    }
    pub(super) fn compile_builtin_euclidean_vector_algebra(
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
        let (continuous, op, law) = match builtin.theorem {
            VectorLimitAtAdd => (false, Operation::Add, "vectorMultivariableLimitAdd"),
            VectorLimitAtSubtract => (
                false,
                Operation::Subtract,
                "vectorMultivariableLimitSubtract",
            ),
            VectorContinuousAtAdd => (true, Operation::Add, "vectorMultivariableContinuousAdd"),
            VectorContinuousAtSubtract => (
                true,
                Operation::Subtract,
                "vectorMultivariableContinuousSubtract",
            ),
            _ => return Err(invalid("Identity")),
        };
        let context = if continuous { 6 } else { 5 };
        let first_index = 3 * context;
        let second_index = first_index + 1;
        let formula_index = first_index + 2;
        let count = formula_index + 1;
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
        let name = if continuous {
            "is_vector_continuous_at"
        } else {
            "has_vector_limit_at"
        };
        let mut first = vec![
            args[0].clone(),
            args[3].clone(),
            args[4].clone(),
            args[5].clone(),
        ];
        let mut second = vec![
            args[1].clone(),
            args[3].clone(),
            args[4].clone(),
            args[5].clone(),
        ];
        if !continuous {
            first.push(args[6].clone());
            second.push(args[7].clone());
        }
        let req = &builtin.requirements;
        let first_r = candidate(&req[first_index], name, &first)?;
        let second_r = candidate(&req[second_index], name, &second)?;
        let first_source = source_domain(
            &dom_stores[first_index],
            &req[first_index],
            if continuous { 1 } else { 3 },
        )?;
        let second_source = source_domain(
            &dom_stores[second_index],
            &req[second_index],
            if continuous { 1 } else { 3 },
        )?;
        let Fact::AtomicFact(atomic @ AtomicFact::MultivariableAnalysisFact(out)) =
            &builtin.conclusions[0]
        else {
            return Err(invalid("PositiveConclusion"));
        };
        let output_r = &out.relation;
        let out_args = output_r.argument_refs();
        if output_r.predicate_name() != name
            || out_args.len() != if continuous { 4 } else { 5 }
            || out_args[0].ir() != args[2].ir()
            || out_args[1].ir() != args[3].ir()
            || out_args[2].ir() != args[4].ir()
            || out_args[3].ir() != args[5].ir()
        {
            return Err(invalid("OriginalConclusion"));
        }
        if !continuous {
            vector_formula(out_args[4], &args[6], &args[7], &args[5], op)?;
        }
        let FactWellDefinedProof::AtomicExceptEquality(wd) = &conclusions_wd[0] else {
            return Err(invalid("OriginalFormation"));
        };
        let output_position = SourcePosition {
            before: count,
            ..*position
        };
        let cached = matches!(
            &wd.as_detailed()
                .map_err(|_| invalid("DetailedFormation"))?
                .predicate_domain,
            PredicateDomainProof::ByKnownFact(_)
        );
        let mut replay = |formation: &MultivariableAnalysisPredicateDomainProof,
                          source_atomic: &AtomicFact,
                          source_wd: &AtomicFactWellDefinedProof,
                          source_prior: &SourcePosition<'_>| {
            if formation.requirements.len()!=context+usize::from(!continuous)
            || !req[2*context..3*context].iter().zip(&formation.requirements[..context]).all(|(a,b)|crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::quantifier_free_source_facts_alpha_equal(a,&b.requirement)) {
            return Err(invalid("OriginalOutputContext"));
        }
            let third_source = &formation.function_domain;
            for source in [second_source, third_source] {
                if !function_domains_alpha_equal(&first_source.signature, &source.signature) {
                    return Err(invalid("OriginalCommonDomains"));
                }
            }
            let output: Vec<_> = out_args.iter().map(|o| (*o).clone()).collect();
            let all_args = [first.clone(), second.clone(), output];
            let relations = [first_r, second_r, output_r];
            let sources = [first_source, second_source, third_source];
            for i in 0..3 {
                let prefix = &req[i * context..(i + 1) * context];
                if continuous {
                    super::compile_builtin_derivative_schema::validate_context(
                        relations[i],
                        prefix,
                        sources[i],
                    )?;
                } else {
                    super::compile_multivariable_limit_context::validate_limit_context(
                        &all_args[i],
                        prefix,
                        sources[i],
                        Some(&args[5]),
                    )?;
                }
            }
            let domain = schema::actual_domain(&first_source.signature)
                .ok_or_else(|| invalid("OriginalDomain"))?;
            let Fact::ForallFact(formula) = &req[formula_index] else {
                return Err(invalid("OriginalFormula"));
            };
            let x = parameter(&formula.typed_parameters, &domain)?;
            if !formula.dom_facts.is_empty()
                || args
                    .iter()
                    .chain([&domain])
                    .any(|o| contains_parameter(o, x.id))
            {
                return Err(invalid("FormulaCapture"));
            }
            let input = schema::identifier(x);
            let [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq))] =
                formula.then_facts.as_slice()
            else {
                return Err(invalid("OriginalPointwiseEquation"));
            };
            if !call_matches(&eq.left, &args[2], &input) {
                return Err(invalid("OriginalPointwiseSubject"));
            }
            vector_formula(
                &eq.right,
                &schema::apply(&args[0], vec![input.clone()]),
                &schema::apply(&args[1], vec![input]),
                &args[5],
                op,
            )?;
            let value_id = if continuous {
                None
            } else {
                let value = &formation.requirements[context];
                if !matches!(&value.requirement,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==out_args[4].ir() && super::compile_multivariable_scalar_limit::vector_carrier(&f.set,&args[5]))
                {
                    return Err(invalid("OriginalValueCarrier"));
                }
                let PredicateDomainRequirementProof::Verified(p) = &value.result else {
                    return Err(invalid("OriginalValueProof"));
                };
                if source_subject(p)? != value.requirement {
                    return Err(invalid("OriginalValueSubject"));
                }
                Some(value.requirement.fact_id())
            };
            let mut definitions = Vec::new();
            for (i, ((fact, proof), store)) in
                req.iter().zip(dom_proofs).zip(dom_stores).enumerate()
            {
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
            self.compile_fact_wd(&conclusions_wd[0], &builtin.conclusions[0], &formed)?;
            let bindings = self.compile_atomic_wd_locals(wd, atomic, &formed)?;
            let scope = SourcePosition::new(
                Some(&formed),
                SourceOwner::AtomicWDLocals(wd, out_args.len()),
                usize::MAX,
            );
            let objects = args
                .iter()
                .map(|o| self.compile_object_reference(o, &scope))
                .collect::<Result<Vec<_>, _>>()?;
            let raw = objects
                .iter()
                .map(|o| format!("(Litex.denote {o})"))
                .collect::<Vec<_>>();
            let mut lines = Vec::new();
            let mut equals = Vec::new();
            for i in 0..3 {
                if i == 2 && cached {
                    let previous_bindings =
                        self.compile_atomic_wd_locals(source_wd, source_atomic, source_prior)?;
                    let previous_scope = SourcePosition::new(
                        Some(source_prior),
                        SourceOwner::AtomicWDLocals(source_wd, out_args.len()),
                        usize::MAX,
                    );
                    let (domain_view, domain_equal) = self.vector_algebra_domain_view(
                        &args[2],
                        sources[2],
                        "vector_algebra_cited_",
                        &previous_scope,
                    )?;
                    let (function_view, _) = self.compile_multivariable_limit_view(
                        &args[2],
                        sources[2],
                        &previous_scope,
                    )?;
                    let function = self.compile_euclidean_limit_function_context(
                        &all_args[2],
                        &req[2 * context..2 * context + 5],
                        sources[2],
                        Some(&args[5]),
                        &previous_scope,
                    )?;
                    let membership = if continuous {
                        format!(
                            "{domain_equal} ▸ h_{}",
                            formation.requirements[context - 1]
                                .requirement
                                .fact_id()
                                .value()
                        )
                    } else {
                        format!("h_{}", value_id.unwrap().value())
                    };
                    let member_type = if continuous {
                        format!(
                            "M.mem {} (Litex.FunctionSemantics.domainValue {})",
                            raw[3], raw[2]
                        )
                    } else {
                        format!(
                            "M.mem (Litex.denote {}) (Litex.realVectorSetValue {})",
                            self.compile_object_reference(out_args[4], &scope)?,
                            raw[5]
                        )
                    };
                    lines.push(format!("  let _vector_algebra_2_source_domain := _vector_algebra_0_source_domain\n  have _vector_algebra_output_context : (_vector_algebra_2_source_domain = Litex.FunctionSemantics.domainValue {}) ∧ Litex.VectorMultivariableFunctionValue M {} {} {} ∧ {member_type} := by\n    {}\n  {}\n  {}\n  {}\n    exact ⟨(show _vector_algebra_2_source_domain = _vector_algebra_cited_source_domain from by rfl).trans {domain_equal},_multivariable_real,{membership}⟩\n  have _vector_algebra_vector_2 := _vector_algebra_output_context.2.1",raw[2],raw[2],raw[4],raw[5],previous_bindings.join("\n").replace('\n',"\n    "),domain_view.replace('\n',"\n  "),function_view.replace('\n',"\n  "),function.replace('\n',"\n  ")));
                    equals.push("_vector_algebra_output_context.1".into());
                    continue;
                }
                let (view, eq) = self.vector_algebra_domain_view(
                    &args[i],
                    sources[i],
                    &format!("vector_algebra_{i}_"),
                    &scope,
                )?;
                lines.push(view);
                equals.push(eq);
                let (view, _) =
                    self.compile_multivariable_limit_view(&args[i], sources[i], &scope)?;
                let function = self.compile_euclidean_limit_function_context(
                    &all_args[i],
                    &req[i * context..i * context + 5],
                    sources[i],
                    Some(&args[5]),
                    &scope,
                )?;
                lines.push(format!("  have _vector_algebra_vector_{i} : Litex.VectorMultivariableFunctionValue M {} {} {} := by\n  {}\n  {}\n    exact _multivariable_real",raw[i],raw[4],raw[5],view.replace('\n',"\n  "),function.replace('\n',"\n  ")));
            }
            for i in 0..2 {
                lines.push(format!("  have _vector_algebra_domain_{i} : Litex.FunctionSemantics.domainValue {} = Litex.FunctionSemantics.domainValue {} := ({}).symm.trans ((show _vector_algebra_{i}_source_domain = _vector_algebra_2_source_domain from by rfl).trans {})",raw[i],raw[2],equals[i],equals[2]));
            }
            let field = op.field();
            let closure = op.closure();
            let m = &raw[5];
            lines.push(format!("  let _vector_algebra_indices := Litex.SetSemantics.sepValue (Litex.closedRangeValue (M.number 1) {m}) (fun _ => True)\n  have _vector_algebra_returns : ∀ a b, M.mem a (Litex.realVectorSetValue {m}) → M.mem b (Litex.realVectorSetValue {m}) → ∀ k, M.mem k _vector_algebra_indices → M.mem (M.{field} (Litex.FunctionSemantics.callValue a k) (Litex.FunctionSemantics.callValue b k)) (M.standard .real) := by\n    intro a b ha hb k hk\n    have ha' := Litex.FunctionSemantics.call_mem _ _ _ _ ha hk\n    have hb' := Litex.FunctionSemantics.call_mem _ _ _ _ hb hk\n    exact Litex.{closure} (Litex.semanticObject _ (M.member_isSet ha')) (Litex.semanticObject _ (M.member_isSet hb')) ha' hb'"));
            let body=format!("fun k => M.{field} (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.callValue {} x) k) (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.callValue {} x) k)",raw[0],raw[1]);
            let formula_id = req[formula_index].fact_id().value();
            lines.push(format!("  have _vector_algebra_formula : ∀ x, M.mem x (Litex.FunctionSemantics.domainValue {}) → ∀ k, M.mem k (Litex.closedRangeValue (M.number 1) {m}) → Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.callValue {} x) k = M.{field} (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.callValue {} x) k) (Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.callValue {} x) k) := by\n    intro x hx k hk\n    have hs : M.mem x _vector_algebra_0_source_domain := ({}).symm ▸ (_vector_algebra_domain_0.symm ▸ hx)\n    have heq := h_{formula_id} (Litex.semanticObject x (M.member_isSet hs)) hs\n    change Litex.FunctionSemantics.callValue {} x = Litex.FunctionSemantics.graphValue _vector_algebra_indices (M.standard .real) ({body}) at heq\n    apply Eq.trans (congrArg (fun v => Litex.FunctionSemantics.callValue v k) heq)\n    exact Litex.FunctionSemantics.call_graphValue _ _ _ (_vector_algebra_returns _ _ (Litex.multivariableVectorFunctionReturns _ _ _ _ _vector_algebra_vector_0 (_vector_algebra_domain_0.symm ▸ hx)) (Litex.multivariableVectorFunctionReturns _ _ _ _ _vector_algebra_vector_1 (_vector_algebra_domain_1.symm ▸ hx))) k ((Litex.SetSemantics.sep_members _ _ _).mpr ⟨hk,True.intro⟩)",raw[2],raw[2],raw[0],raw[1],equals[0],raw[2]));
            let mut native_args = raw.clone();
            let specific = if continuous {
                format!(
                    "({} ▸ h_{})",
                    equals[2],
                    req[3 * context - 1].fact_id().value()
                )
            } else {
                let target = self.compile_object_reference(out_args[4], &scope)?;
                native_args.push(format!("(Litex.denote _vector_algebra_target)"));
                lines.push(format!("  let _vector_algebra_target := {target}\n  have _vector_algebra_target_coordinates : ∀ k, M.mem k (Litex.closedRangeValue (M.number 1) {m}) → Litex.FunctionSemantics.callValue (Litex.denote _vector_algebra_target) k = M.{field} (Litex.FunctionSemantics.callValue {} k) (Litex.FunctionSemantics.callValue {} k) := by\n    intro k hk\n    change Litex.FunctionSemantics.callValue (Litex.FunctionSemantics.graphValue _vector_algebra_indices (M.standard .real) (fun j => M.{field} (Litex.FunctionSemantics.callValue {} j) (Litex.FunctionSemantics.callValue {} j))) k = _\n    exact Litex.FunctionSemantics.call_graphValue _ _ _ (_vector_algebra_returns _ _ h_{}.1 h_{}.1) k ((Litex.SetSemantics.sep_members _ _ _).mpr ⟨hk,True.intro⟩)",raw[6],raw[7],raw[6],raw[7],req[first_index].fact_id().value(),req[second_index].fact_id().value()));
                if cached {
                    "_vector_algebra_output_context.2.2".into()
                } else {
                    format!("h_{}", value_id.unwrap().value())
                }
            };
            let target_proof = if continuous {
                ""
            } else {
                " _vector_algebra_target_coordinates"
            };
            lines.push(format!("  exact Litex.{law} {} (Litex.inNPos_natural {} h_{}) _vector_algebra_vector_0 _vector_algebra_vector_1 _vector_algebra_vector_2 _vector_algebra_domain_0 _vector_algebra_domain_1 {specific} _vector_algebra_formula{target_proof} h_{} h_{}",native_args.join(" "),objects[5],req[2].fact_id().value(),req[first_index].fact_id().value(),req[second_index].fact_id().value()));
            let statement = self.compile_formed_fact_proposition(
                &conclusions_wd[0],
                &builtin.conclusions[0],
                &formed,
            )?;
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
        };
        self.with_vector_algebra_output_formation(atomic, wd, &output_position, &mut replay)
    }
}
