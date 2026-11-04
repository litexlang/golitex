//! Tail laws consume the selected schema and the candidates' original formation.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::compile_sequence_analysis::call_matches;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::prelude::*;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("SequenceTailOrder/{stage}"))
}
fn sequence_member(fact: &Fact, value: &Obj) -> bool {
    matches!(fact, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==value.ir()
        && matches!(&f.set,Obj::FunctionSpace(FunctionSpace::FnSet(s))
            if s.dom_facts.is_empty() && s.ret_set.as_ref()==&Obj::StandardSet(StandardSet::R)
            && matches!(s.set_bound_parameters.groups.as_slice(),[g] if g.params.len()==1
                && g.param_type.as_ref()==&Obj::StandardSet(StandardSet::NPos))))
}
fn member(fact: &Fact, value: &Obj, set: StandardSet) -> bool {
    matches!(fact,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==value.ir() && f.set==Obj::StandardSet(set))
}
fn candidate(fact: &Fact, sequence: &Obj, value: &Obj) -> bool {
    matches!(fact,Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(f)) if f.sequence.ir()==sequence.ir() && f.value.ir()==value.ir())
}
pub(super) fn validate_tail_order(
    id: BuiltinTheoremId,
    args: &[Obj],
    req: &[Fact],
    goal: &Fact,
) -> Result<(), LeanCompileError> {
    use BuiltinTheoremId::*;
    let (arity, count) = match id {
        SequenceLimitEventuallyEqual => (4, 5),
        SequenceLimitShift => (3, 3),
        SequenceLimitCompare => (5, 5),
        SequenceLimitSqueeze => (5, 6),
        _ => return Err(invalid("Id")),
    };
    if args.len() != arity || req.len() != count || !sequence_member(&req[0], &args[0]) {
        return Err(invalid("Stages"));
    }
    if id == SequenceLimitShift {
        if !candidate(&req[1], &args[0], &args[1]) || !member(&req[2], &args[2], StandardSet::N) {
            return Err(invalid("ShiftPremises"));
        }
        let Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(g)) = goal else {
            return Err(invalid("ShiftConclusion"));
        };
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = &g.sequence else {
            return Err(invalid("ShiftFunction"));
        };
        let [group] = f.body.set_bound_parameters.groups.as_slice() else {
            return Err(invalid("ShiftBinder"));
        };
        let [n] = group.params.as_slice() else {
            return Err(invalid("ShiftBinder"));
        };
        if group.param_type.as_ref() != &Obj::StandardSet(StandardSet::NPos) {
            return Err(invalid("ShiftIndexCarrier"));
        }
        let input = Obj::Identifier(IdentifierObj::from_bound_name(n));
        let Obj::FnObj(call) = f.equal_to.as_ref() else {
            return Err(invalid("ShiftCall"));
        };
        let [inputs] = call.body.as_slice() else {
            return Err(invalid("ShiftArguments"));
        };
        let [index] = inputs.as_slice() else {
            return Err(invalid("ShiftIndexArity"));
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = index.as_ref() else {
            return Err(invalid("ShiftIndex"));
        };
        if !f.body.dom_facts.is_empty()
            || f.body.ret_set.as_ref() != &Obj::StandardSet(StandardSet::R)
            || args.iter().any(|o| contains_parameter(o, n.id))
            || g.value.ir() != args[1].ir()
            || call.head.as_ref() != &FnObjHead::from_obj(args[0].clone())
            || sum.left.ir() != input.ir()
            || sum.right.ir() != args[2].ir()
        {
            return Err(invalid("ShiftBody"));
        }
        return Ok(());
    }
    let (cutoff, tail) = match id {
        SequenceLimitEventuallyEqual => {
            if !sequence_member(&req[1], &args[1])
                || !candidate(&req[2], &args[0], &args[2])
                || !candidate(goal, &args[1], &args[2])
            {
                return Err(invalid("EqualityCandidates"));
            }
            (3, 4)
        }
        SequenceLimitCompare => {
            if !candidate(&req[1], &args[0], &args[2])
                || !candidate(&req[2], &args[1], &args[3])
                || !matches!(goal,Fact::AtomicFact(AtomicFact::LessEqualFact(f)) if f.left.ir()==args[2].ir() && f.right.ir()==args[3].ir())
            {
                return Err(invalid("CompareCandidates"));
            }
            (4, 4)
        }
        SequenceLimitSqueeze => {
            if !sequence_member(&req[1], &args[1])
                || !candidate(&req[2], &args[0], &args[3])
                || !candidate(&req[3], &args[2], &args[3])
                || !candidate(goal, &args[1], &args[3])
            {
                return Err(invalid("SqueezeCandidates"));
            }
            (4, 5)
        }
        _ => unreachable!(),
    };
    if !member(&req[tail - 1], &args[cutoff], StandardSet::NPos) {
        return Err(invalid("Cutoff"));
    }
    let Fact::ForallFact(f) = &req[tail] else {
        return Err(invalid("Tail"));
    };
    let n = parameter(&f.typed_parameters, &Obj::StandardSet(StandardSet::NPos))?;
    let input = Obj::Identifier(IdentifierObj::from_bound_name(n));
    if args.iter().any(|o| contains_parameter(o, n.id))
        || !matches!(f.dom_facts.as_slice(),[Fact::AtomicFact(AtomicFact::GreaterEqualFact(g))]
        if g.left.ir()==input.ir() && g.right.ir()==args[cutoff].ir())
    {
        return Err(invalid("TailGuard"));
    }
    let expected = if id == SequenceLimitSqueeze { 2 } else { 1 };
    if f.then_facts.len() != expected {
        return Err(invalid("TailConclusions"));
    }
    for (i, clause) in f.then_facts.iter().enumerate() {
        let valid = match clause {
            ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(e))
                if id == SequenceLimitEventuallyEqual =>
            {
                call_matches(&e.left, &args[0], &input) && call_matches(&e.right, &args[1], &input)
            }
            ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::LessEqualFact(e))
                if id != SequenceLimitEventuallyEqual =>
            {
                call_matches(&e.left, &args[i], &input)
                    && call_matches(&e.right, &args[i + 1], &input)
            }
            _ => false,
        };
        if !valid {
            return Err(invalid("TailSubjects"));
        }
    }
    Ok(())
}

impl LitexToLeanCompiler {
    // Cached formation is borrowed from its exact visible producer. This leaf
    // accepts identity/alpha arguments, keeping old WD bindings inside a closed proof.
    fn sequence_tail_candidate_formation(
        &self,
        fact: &AtomicFact,
        wd: &AtomicFactWellDefinedProof,
        prior: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::HasSequenceLimitFact(limit) = fact else {
            return Err(invalid("CandidateFamily"));
        };
        let formed =
            SourcePosition::new(Some(prior), SourceOwner::AtomicWDLocals(wd, 2), usize::MAX);
        match &wd
            .as_detailed()
            .map_err(|_| invalid("DetailedFormation"))?
            .predicate_domain
        {
            PredicateDomainProof::SequenceLimit(_) => {
                let bindings = self
                    .compile_atomic_wd_locals(wd, fact, prior)?
                    .join("\n")
                    .replace('\n', "\n  ");
                let obj = self.compile_object_reference(&limit.sequence, &formed)?;
                let hf = sequence_domain(&obj, "_sequence_domain");
                Ok(format!(
                    "(by\n  {bindings}\n  exact ⟨{hf}, _sequence_limit_real⟩\n)"
                ))
            }
            PredicateDomainProof::ByKnownFact(cite) => {
                self.compile_known_atomic(cite, fact, &formed)?;
                self.with_cited_atomic_formation(cite.cite_fact_id,&formed,&mut |old,old_wd,old_prior| {
                    let AtomicFact::HasSequenceLimitFact(old_limit)=old else {return Err(invalid("CitedFamily"))};
                    let same=|a:&Obj,b:&Obj| a.ir()==b.ir() || crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::compound_objs_alpha_equal(a,b);
                    if !same(&old_limit.sequence,&limit.sequence) || !same(&old_limit.value,&limit.value) {
                        return Err(invalid("CitedArguments"));
                    }
                    self.sequence_tail_candidate_formation(old,old_wd,old_prior)
                })
            }
            _ => Err(invalid("CandidateFormation")),
        }
    }
    pub(super) fn compile_sequence_tail_order_law(
        &self,
        id: BuiltinTheoremId,
        _args: &[Obj],
        req: &[Fact],
        goal: &Fact,
        objects: &[String],
        references: &[String],
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
        scope: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use BuiltinTheoremId::*;
        let indices: &[usize] = match id {
            SequenceLimitEventuallyEqual => &[2],
            SequenceLimitShift => &[1],
            SequenceLimitCompare => &[1, 2],
            SequenceLimitSqueeze => &[2, 3],
            _ => return Err(invalid("Id")),
        };
        let mut bindings = Vec::new();
        for (i, index) in indices.iter().enumerate() {
            let VerifyFactResult::AtomicExceptEquality(result) = &proofs[*index] else {
                return Err(invalid("CandidateProof"));
            };
            let VerifyAtomicExceptEqualityFactResult::Success(p) = result.as_ref() else {
                return Err(invalid("FailedCandidate"));
            };
            if req[*index] != Fact::AtomicFact(p.fact.clone()) {
                return Err(invalid("CandidateSubject"));
            }
            let prior = SourcePosition {
                before: *index,
                ..*position
            };
            let prior = SourcePosition::new(Some(&prior), SourceOwner::AtomicVerify(p), 0);
            let closed = self
                .sequence_tail_candidate_formation(&p.fact, &p.well_defined_proof, &prior)?
                .replace('\n', "\n  ");
            let AtomicFact::HasSequenceLimitFact(f) = &p.fact else {
                return Err(invalid("CandidateFamily"));
            };
            let a = self.compile_object_reference(&f.sequence, scope)?;
            let v = self.compile_object_reference(&f.value, scope)?;
            bindings.push(format!("have _tail_context_{i} : M.mem (Litex.denote {a}) (Litex.FunctionSemantics.fnSetValue (Litex.denote (Litex.NPos (M := M))) (Litex.denote (Litex.R (M := M)))) ∧ Litex.In {v} (Litex.R (M := M)) := {closed}"));
        }
        let d: Vec<_> = objects
            .iter()
            .map(|o| format!("(Litex.denote {o})"))
            .collect();
        let ha = sequence_domain(&objects[0], &references[0]);
        let tail = |index: usize| {
            format!("(by\n    intro _n _hn _ho\n    exact {} (Litex.semanticObject _n (M.member_isSet _hn)) _hn _ho\n  )",references[index])
        };
        let law=match id {
            SequenceLimitEventuallyEqual=>format!("Litex.sequenceLimitEventuallyEqual {} {ha} {} _tail_context_0.2 {} {} {}",d.join(" "),sequence_domain(&objects[1],&references[1]),references[3],references[2],tail(4)),
            SequenceLimitCompare=>format!("Litex.sequenceLimitCompare {} {ha} _tail_context_1.1 _tail_context_0.2 _tail_context_1.2 {} {} {} {}",d.join(" "),references[3],references[1],references[2],tail(4)),
            SequenceLimitSqueeze=>format!("Litex.sequenceLimitSqueeze {} {ha} {} _tail_context_1.1 _tail_context_0.2 {} {} {} {}",d.join(" "),sequence_domain(&objects[1],&references[1]),references[4],references[2],references[3],tail(5)),
            SequenceLimitShift=> {
                let Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(g))=goal else {return Err(invalid("ShiftConclusion"))};
                let g=self.compile_object_reference(&g.sequence,scope)?.replace('\n',"\n  ");
                bindings.push(format!("let _sequence_shift := {g}"));
                let domain_equal="(Litex.FunctionSignature.withGuard_true_domain (Litex.denote (Litex.NPos (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet (Litex.R (M := M))))";
                format!("Litex.sequenceLimitShift {} _sequence_shift {ha} _tail_context_0.2 {} {} {domain_equal} (by rfl) (by rfl)",d.join(" "),references[2],references[1])
            }
            _=>unreachable!(),
        };
        Ok(format!(
            "(by\n  {}\n  exact {law}\n)",
            bindings.join("\n  ")
        ))
    }
}
fn sequence_domain(obj: &str, proof: &str) -> String {
    format!("(Litex.unguardedFunctionDomain {obj} (Litex.denote (Litex.NPos (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet (Litex.R (M := M))) {proof})")
}
