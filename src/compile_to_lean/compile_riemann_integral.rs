//! Replay the source's oriented Darboux predicate and proof-consuming integral.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::riemann_integral::{
    RiemannIntegralSelectionProof, RiemannIntegralWellDefinedProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    FunctionAnalysisPredicateDomainProof, PredicateDomainRequirementProof,
};
use crate::prelude::*;
use std::collections::HashMap;

pub(super) fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("RiemannIntegral/{stage}"))
}
pub(super) fn parts(fact: &AtomicFact) -> Option<(&Obj, &Obj, &Obj, Option<&Obj>, bool)> {
    Some(match fact {
        AtomicFact::HasRiemannIntegralFact(f) => {
            (&f.function, &f.lower, &f.upper, Some(&f.value), false)
        }
        AtomicFact::NotHasRiemannIntegralFact(f) => {
            (&f.function, &f.lower, &f.upper, Some(&f.value), true)
        }
        AtomicFact::FunctionRiemannIntegrableFact(f) => {
            (&f.function, &f.lower, &f.upper, None, false)
        }
        AtomicFact::NotFunctionRiemannIntegrableFact(f) => {
            (&f.function, &f.lower, &f.upper, None, true)
        }
        _ => return None,
    })
}
pub(super) fn is_enclosure(name: &AtomicName) -> bool {
    name == &AtomicName::plain("is_darboux_enclosure".into())
}
pub(super) fn enclosure_arguments(fact: &AtomicFact) -> Option<&[Obj]> {
    match fact {
        AtomicFact::NormalAtomicFact(f) if is_enclosure(&f.predicate) => Some(&f.body),
        AtomicFact::NotNormalAtomicFact(f) if is_enclosure(&f.predicate) => Some(&f.body),
        _ => None,
    }
}
pub(super) fn raw_proposition(
    fact: &AtomicFact,
    args: &[String],
) -> Result<String, LeanCompileError> {
    let (_, _, _, value, negative) = parts(fact).ok_or_else(|| invalid("Predicate"))?;
    if args.len() != if value.is_some() { 4 } else { 3 } {
        return Err(invalid("PredicateArity"));
    }
    let name = if value.is_some() {
        "HasRiemannIntegralValue"
    } else {
        "FunctionRiemannIntegrableValue"
    };
    Ok(format!(
        "({}Litex.{name} M {})",
        if negative { "¬ " } else { "" },
        args.join(" ")
    ))
}
pub(super) fn validate_existence(
    f: &Obj,
    a: &Obj,
    b: &Obj,
    fact: &Fact,
) -> Result<(), LeanCompileError> {
    let Fact::ExistFact(e) = fact else {
        return Err(invalid("Existence"));
    };
    let v = parameter(&e.typed_parameters, &Obj::StandardSet(StandardSet::R))?;
    if [f, a, b].iter().any(|x| contains_parameter(x, v.id)) {
        return Err(invalid("ExistenceCapture"));
    }
    if !matches!(e.facts.as_slice(),[QuantifierFreeFact::AtomicFact(AtomicFact::HasRiemannIntegralFact(p))]
        if p.function.ir()==f.ir() && p.lower.ir()==a.ir() && p.upper.ir()==b.ir()
            && p.value.ir()==Obj::Identifier(IdentifierObj::from_bound_name(v)).ir())
    {
        return Err(invalid("ExistenceCandidate"));
    }
    Ok(())
}
pub(super) fn validate_domain_requirement(
    fact: &Fact,
    index: usize,
    a: &Obj,
    b: &Obj,
    domain: &Obj,
) -> Result<(), LeanCompileError> {
    let valid = match (index, fact) {
        (0, Fact::AtomicFact(AtomicFact::InFact(p))) => {
            p.element.ir() == a.ir() && p.set == Obj::StandardSet(StandardSet::R)
        }
        (1, Fact::AtomicFact(AtomicFact::InFact(p))) => {
            p.element.ir() == b.ir() && p.set == Obj::StandardSet(StandardSet::R)
        }
        (2, Fact::AtomicFact(AtomicFact::SubsetFact(p))) => {
            p.left.ir()
                == crate::execute::execute_fact_stmt::riemann_integral::helper::sorted_interval(
                    a.clone(),
                    b.clone(),
                )
                .ir()
                && p.right.ir() == domain.ir()
        }
        _ => false,
    };
    if valid {
        Ok(())
    } else {
        Err(invalid("DomainRequirementSubject"))
    }
}

pub(super) fn endpoint_rewrites(names: &[&str], location: &str) -> String {
    names
        .iter()
        .enumerate()
        .map(|(index, name)| {
            // At equal endpoints the first rewrite can also normalize the second.
            format!(
                "{}erw [{name}]{location}",
                if index == 0 { "" } else { "try " }
            )
        })
        .collect::<Vec<_>>()
        .join("\n  ")
}

impl LitexToLeanCompiler {
    /// Replay only the closed endpoint folding performed by the source clause builder.
    pub(super) fn compile_riemann_endpoint_reductions(
        &self,
        a: &Obj,
        b: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<Option<(String, Vec<&'static str>)>, LeanCompileError> {
        use crate::execute::execute_fact_stmt::riemann_integral::helper::{max, min};
        let lower = min(a.clone(), b.clone());
        let upper = max(a.clone(), b.clone());
        let folded = [
            (false, "_integral_min", lower),
            (true, "_integral_max", upper),
        ]
        .into_iter()
        .filter(|(_, _, target)| matches!(target, Obj::Literal(Literal::Number(_))))
        .collect::<Vec<_>>();
        if folded.is_empty() {
            return Ok(None);
        }
        // The source clause builder has already selected exact closed folding.
        // Replay each endpoint with the shared numeric denotation laws, after
        // its original WD, rather than restrict that folding to field syntax.
        let (av, ap) = self.compile_eval_closed_value(a, position)?;
        let (bv, bp) = self.compile_eval_closed_value(b, position)?;
        let ar = exact_rational_literal(&av, "ℝ")?;
        let br = exact_rational_literal(&bv, "ℝ")?;
        let ac = exact_rational_literal(&av, "ℂ")?;
        let bc = exact_rational_literal(&bv, "ℂ")?;
        let a = self.compile_function_raw_expression_bound(a, position, &HashMap::new())?;
        let b = self.compile_function_raw_expression_bound(b, position, &HashMap::new())?;
        let mut lines = vec![
            format!("have _integral_lower : {a} = M.number {ac} := {ap}"),
            format!("have _integral_upper : {b} = M.number {bc} := {bp}"),
        ];
        let mut names = Vec::new();
        for (maximum, name, target) in folded {
            let target =
                self.compile_function_raw_expression_bound(&target, position, &HashMap::new())?;
            lines.push(format!("have {name} : Litex.minMaxValue {maximum} {a} {b} = {target} := by\n  have _evaluated := Litex.minMaxValue_number (M := M) {maximum} {ar} {br}\n  norm_num at _evaluated\n  exact ((congrArg₂ (Litex.minMaxValue {maximum}) _integral_lower _integral_upper).trans _evaluated).trans (congrArg M.number (by norm_num))"));
            names.push(name);
        }
        Ok(Some((lines.join("\n"), names)))
    }

    pub(super) fn compile_riemann_wd(
        &self,
        object: &RiemannIntegral,
        proof: &RiemannIntegralWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let args = [&*object.function, &*object.lower, &*object.upper];
        let mut bindings = Vec::new();
        for (i, (obj, child)) in args
            .iter()
            .zip([&proof.function_wd, &proof.lower_wd, &proof.upper_wd])
            .enumerate()
        {
            ensure_object(obj, child)?;
            bindings.push(format!(
                "let _integral_arg_{i} := {}",
                self.compile_wd(
                    child,
                    &SourcePosition {
                        before: i,
                        ..*position
                    }
                )?
            ));
        }
        if proof.requirements.len() != 3 {
            return Err(invalid("WDRequirements"));
        }
        let real = self.compile_real_function_domain(args[0], &proof.domain, position)?;
        let (view, equal) =
            self.compile_function_limit_domain_view(args[0], &proof.domain, position)?;
        let mut lines = vec![format!("have _integral_real := {real}")];
        for (i, r) in proof.requirements.iter().enumerate() {
            validate_domain_requirement(&r.requirement, i, args[1], args[2], &proof.domain.domain)?;
            let PredicateDomainRequirementProof::Verified(p) = &r.result else {
                return Err(invalid("WDRequirementRoute"));
            };
            if source_subject(p)? != r.requirement {
                return Err(invalid("WDRequirementProof"));
            }
            let prior = SourcePosition {
                before: 3 + i,
                ..*position
            };
            let (_checked_type, term) = self.compile_verify(p, &prior)?;
            // Keep the original proof/WD term, but fix its semantic proposition
            // independently of proof-consuming object constructors in its type.
            let ty =
                self.compile_function_raw_predicate(&r.requirement, &prior, &HashMap::new())?;
            lines.push(format!(
                "have h_{} : {ty} := {term}",
                r.requirement.fact_id().value()
            ));
        }
        let selection = match &proof.selection {
            RiemannIntegralSelectionProof::Candidate(p) => {
                let AtomicFact::HasRiemannIntegralFact(c) = &p.fact else {
                    return Err(invalid("WDCandidate"));
                };
                if c.function.ir() != args[0].ir()
                    || c.lower.ir() != args[1].ir()
                    || c.upper.ir() != args[2].ir()
                {
                    return Err(invalid("WDCandidateSubject"));
                }
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(k) =
                    p.searched_proof.as_ref()
                else {
                    return Err(invalid("WDCandidateCitation"));
                };
                let h = self.compile_known_atomic(k, &p.fact, position)?;
                let value = self.compile_function_raw_expression_bound(
                    &c.value,
                    position,
                    &HashMap::new(),
                )?;
                format!("(Litex.riemannIntegralExistsOfCandidate (Litex.denote _integral_arg_0) (Litex.denote _integral_arg_1) (Litex.denote _integral_arg_2) {value} {h})")
            }
            RiemannIntegralSelectionProof::Existence { fact, proof } => {
                validate_existence(args[0], args[1], args[2], fact)?;
                if source_subject(proof)? != *fact {
                    return Err(invalid("WDExistenceProof"));
                }
                self.compile_verify(proof, position)?.1
            }
        };
        let ids = proof
            .requirements
            .iter()
            .map(|r| r.requirement.fact_id().value())
            .collect::<Vec<_>>();
        lines.push(format!("have _integral_domain_eq := {equal}"));
        let reduction = self.compile_riemann_endpoint_reductions(args[1], args[2], position)?;
        let interval_fold = if let Some((proofs, names)) = reduction {
            lines.push(proofs);
            format!(
                "\n  unfold Litex.riemannIntervalValue\n  {}",
                endpoint_rewrites(&names, "")
            )
        } else {
            String::new()
        };
        lines.push(format!("have _integral_interval : ∀ x, M.mem x (Litex.riemannIntervalValue (Litex.denote _integral_arg_1) (Litex.denote _integral_arg_2)) → M.mem x (Litex.FunctionSemantics.domainValue (Litex.denote _integral_arg_0)) := by\n  rw [← _integral_domain_eq]{interval_fold}\n  exact h_{}",ids[2]));
        lines.push(format!(
            "exact ⟨_integral_real,h_{},h_{},_integral_interval,{selection}⟩",
            ids[0], ids[1]
        ));
        // Expose the fixed payload to congruence and tuple projections; only
        // the WD field belongs inside the proof block.
        Ok(format!(
            "({}; @Litex.Obj.mk M _ (Litex.riemannIntegralRepresentation (M := M)) (Litex.RiemannIntegralObj.mk _integral_arg_0 _integral_arg_1 _integral_arg_2) (by\n{view}\n  {}\n))",
            bindings.join("; "),
            lines.join("\n").replace('\n', "\n  ")
        ))
    }

    pub(super) fn compile_riemann_domain(
        &self,
        fact: &AtomicFact,
        proof: &FunctionAnalysisPredicateDomainProof,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let args = atomic_fact_args_ref(fact);
        let enclosure = enclosure_arguments(fact);
        let (f, a, b, value, count) = if let Some(arguments) = enclosure {
            let [f, a, b, _, _, _, _] = arguments else {
                return Err(invalid("EnclosureArity"));
            };
            (f, a, b, None, 7)
        } else {
            let (f, a, b, value, _) =
                parts(fact).ok_or_else(|| invalid("PredicateDomainFamily"))?;
            (f, a, b, value, 3 + usize::from(value.is_some()))
        };
        if proof.requirements.len() != count {
            return Err(invalid("PredicateRequirements"));
        }
        let real = self.compile_real_function_domain(f, &proof.function_domain, position)?;
        let mut lines = vec![format!("have _integral_real := {real}")];
        for (i, r) in proof.requirements.iter().enumerate() {
            if i < 3 {
                validate_domain_requirement(
                    &r.requirement,
                    i,
                    a,
                    b,
                    &proof.function_domain.domain,
                )?;
            } else if let Some(arguments) = enclosure {
                let Fact::AtomicFact(AtomicFact::InFact(member)) = &r.requirement else {
                    return Err(invalid("EnclosureMembership"));
                };
                if member.element.ir() != arguments[i].ir() {
                    return Err(invalid("EnclosureRequirementSubject"));
                }
                if i == 3 {
                    if member.set != Obj::StandardSet(StandardSet::NPos) {
                        return Err(invalid("PartitionSizeCarrier"));
                    }
                } else {
                    let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &member.set else {
                        return Err(invalid("EnclosureFunctionCarrier"));
                    };
                    super::compile_riemann_definition::index_signature(
                        signature,
                        &crate::execute::execute_fact_stmt::riemann_integral::helper::num(
                            if i == 4 { "0" } else { "1" },
                        ),
                        &arguments[3],
                    )?;
                }
            } else if !matches!(&r.requirement,Fact::AtomicFact(AtomicFact::InFact(p)) if Some(p.element.ir())==value.map(Obj::ir)&&p.set==Obj::StandardSet(StandardSet::R))
            {
                return Err(invalid("CandidateRealRequirement"));
            }
            let prior = SourcePosition {
                before: args.len() + i,
                ..*position
            };
            let (_checked_type, term) = match &r.result {
                PredicateDomainRequirementProof::Verified(p) => {
                    if source_subject(p)? != r.requirement {
                        return Err(invalid("PredicateRequirementProof"));
                    }
                    self.compile_verify(p, &prior)?
                }
                PredicateDomainRequirementProof::CheckedArgument(p) => (
                    self.compile_function_raw_predicate(&r.requirement, &prior, &HashMap::new())?,
                    self.compile_checked_domain_argument(&r.requirement, p, &args, i, &prior)?,
                ),
            };
            // A guarded function carrier repeats its complete formation inside
            // dependent enclosure hypotheses. Bind that fixed semantic carrier
            // while retaining its original proof. Keep other checked types,
            // including intervals, at their already-formed constructors.
            let ty = if matches!(&r.requirement,
                Fact::AtomicFact(AtomicFact::InFact(member))
                if matches!(&member.set, Obj::FunctionSpace(FunctionSpace::FnSet(_))))
            {
                self.compile_function_raw_predicate(&r.requirement, &prior, &HashMap::new())?
            } else {
                _checked_type
            };
            lines.push(format!(
                "have h_{} : {ty} := {term}",
                r.requirement.fact_id().value()
            ));
        }
        Ok(lines)
    }

    pub(super) fn compile_riemann_equality(
        &self,
        fact: &EqualFact,
        proof:&crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_riemann_integral::RiemannIntegralSelectedValueProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (selected, value, object, reversed) = match (&fact.left, &fact.right) {
            (s @ Obj::IntegralOperator(IntegralOperator::Riemann(o)), v) => (s, v, o, false),
            (v, s @ Obj::IntegralOperator(IntegralOperator::Riemann(o))) => (s, v, o, true),
            _ => return Err(invalid("EqualityObject")),
        };
        let AtomicFact::HasRiemannIntegralFact(c) = &proof.candidate.fact else {
            return Err(invalid("EqualityCandidate"));
        };
        if c.function.ir() != object.function.ir()
            || c.lower.ir() != object.lower.ir()
            || c.upper.ir() != object.upper.ir()
        {
            return Err(invalid("EqualityCandidateSubject"));
        }
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(k) =
            proof.candidate.searched_proof.as_ref()
        else {
            return Err(invalid("EqualityCitation"));
        };
        let h = self.compile_known_atomic(k, &proof.candidate.fact, position)?;
        let comparison = EqualFact {
            fact_id: fact.fact_id,
            left: c.value.clone(),
            right: value.clone(),
            line_file: None,
        };
        let eq = self.compile_equality_search(&comparison, &proof.value_equality, position)?;
        let term = format!(
            "((Litex.riemannIntegralEqCandidate {} {} {h}).trans {eq})",
            self.compile_object_reference(selected, position)?,
            self.compile_function_raw_expression_bound(&c.value, position, &HashMap::new())?
        );
        Ok(if reversed {
            format!("{term}.symm")
        } else {
            term
        })
    }
}
