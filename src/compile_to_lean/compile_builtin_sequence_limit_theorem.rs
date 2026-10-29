//! Replay explicit sequence-limit certificates and epsilon-tail controls.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("SequenceLimitTheorem/{stage}"))
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_sequence_limit_theorem(
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
        let (arity, count) = match builtin.theorem {
            SequenceLimitUnique => (3, 3),
            SequenceLimitExists => (2, 2),
            SequenceLimitSelected => (1, 2),
            SequenceLimitFromEpsilon => (2, 3),
            SequenceLimitTail => (3, 3),
            SequenceCauchyFromEpsilon => (1, 2),
            SequenceCauchyTail => (2, 3),
            SequenceConvergentFromLimit => (2, 2),
            SequenceLimitFromConvergent => (1, 2),
            SequenceStrictIncreasingNondecreasing | SequenceStrictDecreasingNonincreasing => (1, 2),
            SequenceBoundedFromBounds => (3, 4),
            _ => return Err(invalid("Id")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || !matches!(&call.name, AtomicName::Plain { name } if name == builtin.theorem.as_str())
            || args != &builtin.arguments
            || args.len() != arity
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("Stages"));
        }
        let req = &builtin.requirements;
        if !matches!(&req[0], Fact::AtomicFact(AtomicFact::InFact(f))
            if f.element.ir() == args[0].ir() && matches!(&f.set, Obj::FunctionSpace(FunctionSpace::FnSet(s))
                if matches!(s.set_bound_parameters.groups.as_slice(), [g] if g.params.len() == 1
                    && g.param_type.as_ref() == &Obj::StandardSet(StandardSet::NPos))
                && s.dom_facts.is_empty() && s.ret_set.as_ref() == &Obj::StandardSet(StandardSet::R)))
        {
            return Err(invalid("SequenceDomain"));
        }
        let candidates = match builtin.theorem {
            SequenceLimitUnique => 2,
            SequenceLimitExists | SequenceLimitTail | SequenceConvergentFromLimit => 1,
            _ => 0,
        };
        for (premise, value) in req[1..1 + candidates].iter().zip(&args[1..1 + candidates]) {
            if !matches!(premise, Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(f))
                if f.sequence.ir() == args[0].ir() && f.value.ir() == value.ir())
            {
                return Err(invalid("Candidate"));
            }
        }
        let goal = &builtin.conclusions[0];
        let selected = match builtin.theorem {
            SequenceStrictIncreasingNondecreasing | SequenceStrictDecreasingNonincreasing => {
                let (strict, weak) = if builtin.theorem == SequenceStrictIncreasingNondecreasing {
                    (
                        SequenceAnalysisProperty::StrictlyIncreasing,
                        SequenceAnalysisProperty::Nondecreasing,
                    )
                } else {
                    (
                        SequenceAnalysisProperty::StrictlyDecreasing,
                        SequenceAnalysisProperty::Nonincreasing,
                    )
                };
                if !matches!(&req[1],Fact::AtomicFact(AtomicFact::SequenceAnalysisFact(f)) if f.sequence.ir()==args[0].ir() && f.property==strict)
                    || !matches!(goal,Fact::AtomicFact(AtomicFact::SequenceAnalysisFact(f)) if f.sequence.ir()==args[0].ir() && f.property==weak)
                {
                    return Err(invalid("OrderProperties"));
                }
                None
            }
            SequenceBoundedFromBounds => {
                for index in 1..3 {
                    if !matches!(&req[index],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==args[index].ir() && f.set==Obj::StandardSet(StandardSet::R))
                    {
                        return Err(invalid("RealBounds"));
                    }
                }
                let Fact::ForallFact(f) = &req[3] else {
                    return Err(invalid("PointwiseBounds"));
                };
                let n = super::compile_real_set_bounds::parameter(
                    &f.typed_parameters,
                    &Obj::StandardSet(StandardSet::NPos),
                )?;
                if !f.dom_facts.is_empty()
                    || f.then_facts.len() != 2
                    || args
                        .iter()
                        .any(|a| super::compile_real_set_bounds::contains_parameter(a, n.id))
                {
                    return Err(invalid("BoundIndex"));
                }
                let input = Obj::Identifier(IdentifierObj::from_bound_name(n));
                for (index, clause) in f.then_facts.iter().enumerate() {
                    let ExistOrAndChainAtomicFact::AtomicFact(bound) = clause else {
                        return Err(invalid("BoundClause"));
                    };
                    let (left, right, strict) = source_order_oriented(bound)?;
                    if strict
                        || (index == 0
                            && (left.ir() != args[1].ir()
                                || !super::compile_sequence_analysis::call_matches(
                                    right, &args[0], &input,
                                )))
                        || (index == 1
                            && (!super::compile_sequence_analysis::call_matches(
                                left, &args[0], &input,
                            ) || right.ir() != args[2].ir()))
                    {
                        return Err(invalid("BoundSubjects"));
                    }
                }
                if !matches!(goal,Fact::AtomicFact(AtomicFact::SequenceAnalysisFact(f)) if f.sequence.ir()==args[0].ir() && f.property==SequenceAnalysisProperty::Bounded)
                {
                    return Err(invalid("BoundedConclusion"));
                }
                None
            }
            SequenceCauchyFromEpsilon => {
                if !matches!(goal, Fact::AtomicFact(AtomicFact::SequenceAnalysisFact(f))
                    if f.sequence.ir() == args[0].ir() && f.property == SequenceAnalysisProperty::Cauchy)
                {
                    return Err(invalid("CauchyConclusion"));
                }
                super::compile_sequence_epsilon::validate_epsilon_clause(&args[0], None, &req[1])?;
                None
            }
            SequenceCauchyTail => {
                if !matches!(&req[1], Fact::AtomicFact(AtomicFact::SequenceAnalysisFact(f))
                    if f.sequence.ir() == args[0].ir() && f.property == SequenceAnalysisProperty::Cauchy)
                    || !matches!(&req[2], Fact::AtomicFact(AtomicFact::InFact(f))
                        if f.element.ir() == args[1].ir() && f.set == Obj::StandardSet(StandardSet::RPos))
                {
                    return Err(invalid("CauchyTailPremises"));
                }
                let Fact::ExistFact(e) = goal else {
                    return Err(invalid("CauchyTailExistence"));
                };
                super::compile_sequence_epsilon::validate_control_clause(
                    &args[0], None, &args[1], e,
                )?;
                None
            }
            SequenceConvergentFromLimit => {
                if !matches!(goal, Fact::AtomicFact(AtomicFact::SequenceAnalysisFact(f))
                    if f.sequence.ir() == args[0].ir() && f.property == SequenceAnalysisProperty::Convergent)
                {
                    return Err(invalid("ConvergentConclusion"));
                }
                None
            }
            SequenceLimitFromConvergent => {
                if !matches!(&req[1], Fact::AtomicFact(AtomicFact::SequenceAnalysisFact(f))
                    if f.sequence.ir() == args[0].ir() && f.property == SequenceAnalysisProperty::Convergent)
                {
                    return Err(invalid("ConvergentPremise"));
                }
                super::compile_sequence_epsilon::validate_limit_existence(&args[0], goal)?;
                None
            }
            SequenceLimitUnique => {
                if !matches!(goal, Fact::AtomicFact(AtomicFact::EqualFact(f))
                    if f.left.ir() == args[1].ir() && f.right.ir() == args[2].ir())
                {
                    return Err(invalid("Conclusion"));
                }
                None
            }
            SequenceLimitExists => {
                super::compile_sequence_epsilon::validate_limit_existence(&args[0], goal)?;
                None
            }
            SequenceLimitSelected => {
                super::compile_sequence_epsilon::validate_limit_existence(&args[0], &req[1])?;
                let Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(f)) = goal else {
                    return Err(invalid("SelectedConclusion"));
                };
                if f.sequence.ir() != args[0].ir()
                    || !matches!(&f.value, Obj::LimitOperator(LimitOperator::Sequence(p))
                        if p.sequence.ir() == args[0].ir())
                {
                    return Err(invalid("SelectedSequence"));
                }
                Some(&f.value)
            }
            SequenceLimitFromEpsilon => {
                if !matches!(&req[1], Fact::AtomicFact(AtomicFact::InFact(f))
                    if f.element.ir() == args[1].ir() && f.set == Obj::StandardSet(StandardSet::R))
                    || !matches!(goal, Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(f))
                        if f.sequence.ir() == args[0].ir() && f.value.ir() == args[1].ir())
                {
                    return Err(invalid("EpsilonSubject"));
                }
                super::compile_sequence_epsilon::validate_epsilon_clause(
                    &args[0],
                    Some(&args[1]),
                    &req[2],
                )?;
                None
            }
            SequenceLimitTail => {
                if !matches!(&req[2], Fact::AtomicFact(AtomicFact::InFact(f))
                    if f.element.ir() == args[2].ir() && f.set == Obj::StandardSet(StandardSet::RPos))
                {
                    return Err(invalid("PositiveEpsilon"));
                }
                let Fact::ExistFact(e) = goal else {
                    return Err(invalid("TailExistence"));
                };
                super::compile_sequence_epsilon::validate_control_clause(
                    &args[0],
                    Some(&args[1]),
                    &args[2],
                    e,
                )?;
                None
            }
            _ => unreachable!(),
        };
        let mut definitions = Vec::new();
        let mut references = Vec::new();
        for (index, ((requirement, checked), stored)) in
            req.iter().zip(dom_proofs).zip(dom_stores).enumerate()
        {
            if source_subject(checked)? != *requirement {
                return Err(invalid("PremiseSubject"));
            }
            self.validate_store(&stored.store, requirement)?;
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let compiled = self.compile_verify(checked, &prior)?;
            definitions.push(self.emit_internal_fact(requirement, &compiled, &prior)?);
            let reference = format!("h_{}", requirement.fact_id().value());
            definitions.extend(self.compile_stored_inferences(
                stored,
                requirement,
                &(compiled.0, reference.clone()),
                &SourcePosition {
                    before: index + 1,
                    ..*position
                },
            )?);
            references.push(reference);
        }
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        let wd = &conclusions_wd[0];
        self.compile_fact_wd(wd, goal, &formed)?;
        let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
        let statement = self.compile_formed_fact_proposition(wd, goal, &formed)?;
        let objects = args
            .iter()
            .map(|a| self.compile_object_reference(a, &scope))
            .collect::<Result<Vec<_>, _>>()?;
        let domain = || {
            format!(
            "(Litex.unguardedFunctionDomain {} (Litex.denote (Litex.NPos (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet (Litex.R (M := M))) {})",
            objects[0], references[0]
        )
        };
        let law = match builtin.theorem {
            SequenceStrictIncreasingNondecreasing | SequenceStrictDecreasingNonincreasing => {
                let reverse=builtin.theorem==SequenceStrictDecreasingNonincreasing;
                let domain = domain();
                format!("Litex.sequenceStrictOrderWeak (Litex.denote {}) {reverse} {domain} {}",objects[0],references[1])
            }
            SequenceBoundedFromBounds => {
                let domain = domain();
                format!("Litex.sequenceBoundedFromPointwise {} {domain} {} {} (by\n  intro n hn\n  exact {} (Litex.semanticObject n (M.member_isSet hn)) hn\n)",objects.join(" "),references[1],references[2],references[3])
            }
            SequenceLimitUnique => {
                let domain = domain();
                let left_real = self.compile_real_membership_certificate(&args[1], &scope)?;
                let right_real = self.compile_real_membership_certificate(&args[2], &scope)?;
                format!(
                    "Litex.sequenceLimitCandidatesEqual {} {domain} {left_real} {right_real} {} {}",
                    objects.join(" "),
                    references[1],
                    references[2]
                )
            }
            SequenceLimitExists | SequenceConvergentFromLimit => format!(
                "Litex.sequenceConvergentOfCandidate {} {} {} {}",
                objects[0],
                objects[1],
                self.compile_real_membership_certificate(&args[1], &scope)?,
                references[1]
            ),
            SequenceLimitSelected => format!(
                "Litex.sequenceLimitSelected {}",
                self.compile_object_reference(selected.expect("validated selector"), &scope)?
            ),
            SequenceLimitFromEpsilon => format!(
                "Litex.sequenceLimitOfForall {} {}",
                objects.join(" "),
                references[2]
            ),
            SequenceCauchyFromEpsilon => format!("Litex.sequenceCauchyOfForall {} {}", objects[0], references[1]),
            SequenceCauchyTail => format!("(by\n  obtain ⟨_cutoff, _member, _control⟩ := {} (Litex.denote {}) {}\n  exact ⟨_cutoff, _member, _control⟩\n)", references[1], objects[1], references[2]),
            SequenceLimitFromConvergent => references[1].clone(),
            SequenceLimitTail => format!(
                "(by\n  obtain ⟨_limit_cutoff, _limit_cutoff_member, _limit_control⟩ := Litex.sequenceLimitTail {} {} {}\n  refine ⟨_limit_cutoff, _limit_cutoff_member, ?_⟩\n  exact _limit_control\n)",
                objects.join(" "),
                references[1],
                references[2]
            ),
            _ => unreachable!(),
        };
        Ok((
            definitions,
            format!("(show {statement} from {law})"),
            builtin.conclusions.clone(),
        ))
    }
}
