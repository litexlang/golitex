//! Replay exact finite-extremum transport and cross-link NativeSchema results.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::compile_sequence_analysis::call_matches;
use super::compile_sequence_extremum::extremum_parts;
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::prelude::*;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Compare,
    Equal,
    Shift,
    Neg,
    Limit,
    Order,
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("SequenceExtremaTransport/{stage}"))
}
fn member(f: &Fact, o: &Obj, set: StandardSet) -> bool {
    matches!(f,Fact::AtomicFact(AtomicFact::InFact(x)) if x.element.ir()==o.ir() && x.set==Obj::StandardSet(set))
}
fn sequence(f: &Fact, o: &Obj) -> bool {
    matches!(f,Fact::AtomicFact(AtomicFact::InFact(x)) if x.element.ir()==o.ir()
        && matches!(&x.set,Obj::FunctionSpace(FunctionSpace::FnSet(s)) if s.dom_facts.is_empty()
            && s.ret_set.as_ref()==&Obj::StandardSet(StandardSet::R)
            && matches!(s.set_bound_parameters.groups.as_slice(),[g] if g.params.len()==1
                && g.param_type.as_ref()==&Obj::StandardSet(StandardSet::NPos))))
}
fn candidate(f: &Fact, a: &Obj, v: &Obj, upper: bool) -> bool {
    matches!(f,Fact::AtomicFact(x) if extremum_parts(x).is_some_and(|(s,l,u,n)|!n && u==upper && s.ir()==a.ir() && l.ir()==v.ir()))
}
fn captured_candidate(f: &AtomicFact) -> Option<(&Obj, &Obj, Option<bool>)> {
    if let AtomicFact::HasSequenceLimitFact(f) = f {
        return Some((&f.sequence, &f.value, None));
    }
    let (a, v, upper, negative) = extremum_parts(f)?;
    (!negative).then_some((a, v, Some(upper)))
}
fn le(f: &Fact, a: &Obj, b: &Obj) -> bool {
    matches!(f,Fact::AtomicFact(AtomicFact::LessEqualFact(x)) if x.left.ir()==a.ir() && x.right.ir()==b.ir())
}
fn formula(kind: Kind, args: &[Obj], f: &Fact) -> Result<(), LeanCompileError> {
    let Fact::ForallFact(f) = f else {
        return Err(invalid("Formula"));
    };
    let n = parameter(&f.typed_parameters, &Obj::StandardSet(StandardSet::NPos))?;
    let input = Obj::Identifier(IdentifierObj::from_bound_name(n));
    if args.iter().any(|a| contains_parameter(a, n.id)) {
        return Err(invalid("FormulaCapture"));
    }
    if matches!(kind, Kind::Equal | Kind::Compare) {
        let cutoff = &args[if kind == Kind::Compare { 4 } else { 3 }];
        if !matches!(f.dom_facts.as_slice(),[Fact::AtomicFact(AtomicFact::GreaterEqualFact(g))]
            if g.left.ir()==input.ir() && g.right.ir()==cutoff.ir())
        {
            return Err(invalid("TailGuard"));
        }
    } else if !f.dom_facts.is_empty() {
        return Err(invalid("UnexpectedFormulaGuard"));
    }
    if kind == Kind::Compare {
        if !matches!(f.then_facts.as_slice(),[ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::LessEqualFact(g))]
            if call_matches(&g.left,&args[0],&input) && call_matches(&g.right,&args[1],&input))
        {
            return Err(invalid("PointwiseOrder"));
        }
        return Ok(());
    }
    let [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq))] =
        f.then_facts.as_slice()
    else {
        return Err(invalid("PointwiseEquation"));
    };
    if !call_matches(&eq.left, &args[1], &input) {
        return Err(invalid("OutputCall"));
    }
    let valid = match kind {
        Kind::Equal => call_matches(&eq.right, &args[0], &input),
        Kind::Neg => {
            matches!(&eq.right,Obj::ArithmeticOperator(ArithmeticOperator::Neg(x)) if call_matches(&x.arg,&args[0],&input))
        }
        Kind::Shift => {
            let Obj::FnObj(call) = &eq.right else {
                return Err(invalid("ShiftCall"));
            };
            let [inputs] = call.body.as_slice() else {
                return Err(invalid("ShiftCallArguments"));
            };
            matches!(inputs.as_slice(),[index] if matches!(index.as_ref(),Obj::ArithmeticOperator(ArithmeticOperator::Add(x))
                if x.left.ir()==input.ir() && x.right.ir()==args[3].ir()))
                && call.head.as_ref() == &FnObjHead::from_obj(args[0].clone())
        }
        _ => false,
    };
    if !valid {
        return Err(invalid("OriginalFormulaOperation"));
    }
    Ok(())
}
impl LitexToLeanCompiler {
    // Borrow the exact candidate's recorded WD. Cached identity/alpha citations
    // retain their original owner and keep old WD locals inside a closed proof.
    fn extrema_transport_value_real(
        &self,
        fact: &AtomicFact,
        wd: &AtomicFactWellDefinedProof,
        prior: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Some((sequence, value, side)) = captured_candidate(fact) else {
            return Err(invalid("ValueCandidateFamily"));
        };
        let formed =
            SourcePosition::new(Some(prior), SourceOwner::AtomicWDLocals(wd, 2), usize::MAX);
        match &wd
            .as_detailed()
            .map_err(|_| invalid("DetailedValueFormation"))?
            .predicate_domain
        {
            PredicateDomainProof::SequenceLimit(p) => {
                if p.value_real.element.ir() != value.ir() || p.value_real.set != StandardSet::R {
                    return Err(invalid("OriginalValueRealSubject"));
                }
                let bindings = self
                    .compile_atomic_wd_locals(wd, fact, prior)?
                    .join("\n")
                    .replace('\n', "\n  ");
                Ok(format!(
                    "(by\n  {bindings}\n  exact _sequence_limit_real\n)"
                ))
            }
            PredicateDomainProof::ByKnownFact(cite) => {
                self.compile_known_atomic(cite, fact, &formed)?;
                if let Some(real) = self.cited_obtained_argument_membership(
                    cite.cite_fact_id,
                    value,
                    &StandardSet::R,
                    &formed,
                )? {
                    return Ok(real);
                }
                self.with_cited_atomic_formation(cite.cite_fact_id,&formed,&mut |old,old_wd,old_prior| {
                    let Some((old_sequence,old_value,old_side))=captured_candidate(old) else {return Err(invalid("CitedValueFamily"))};
                    let same=|a:&Obj,b:&Obj| a.ir()==b.ir() || crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::compound_objs_alpha_equal(a,b);
                    if old_side!=side || !same(old_sequence,sequence) || !same(old_value,value) {return Err(invalid("CitedValueArguments"));}
                    self.extrema_transport_value_real(old,old_wd,old_prior)
                })
            }
            _ => Err(invalid("OriginalValueFormation")),
        }
    }
    pub(super) fn extrema_transport_candidate_real(
        &self,
        proof: &VerifyFactResult,
        prior: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let VerifyFactResult::AtomicExceptEquality(result) = proof else {
            return Err(invalid("ValueProofFamily"));
        };
        let VerifyAtomicExceptEqualityFactResult::Success(p) = result.as_ref() else {
            return Err(invalid("FailedValueProof"));
        };
        let source = SourcePosition::new(Some(prior), SourceOwner::AtomicVerify(p), 0);
        self.extrema_transport_value_real(&p.fact, &p.well_defined_proof, &source)
    }
    pub(super) fn compile_builtin_sequence_extrema_transport(
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
        let (kind, upper, arity, count) = match builtin.theorem {
            SequenceLimsupCompare => (Kind::Compare, true, 5, 6),
            SequenceLiminfCompare => (Kind::Compare, false, 5, 6),
            SequenceLimsupEventuallyEqual => (Kind::Equal, true, 4, 5),
            SequenceLiminfEventuallyEqual => (Kind::Equal, false, 4, 5),
            SequenceLimsupShift => (Kind::Shift, true, 4, 5),
            SequenceLiminfShift => (Kind::Shift, false, 4, 5),
            SequenceLimsupNeg => (Kind::Neg, true, 3, 5),
            SequenceLiminfNeg => (Kind::Neg, false, 3, 5),
            SequenceLimitFromExtrema => (Kind::Limit, true, 2, 3),
            SequenceExtremaOrder => (Kind::Order, false, 3, 3),
            _ => return Err(invalid("Id")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || !matches!(&call.name,AtomicName::Plain{name} if name==builtin.theorem.as_str())
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
        let goal = &builtin.conclusions[0];
        if !sequence(&req[0], &args[0]) {
            return Err(invalid("FirstSequence"));
        }
        match kind {
            Kind::Limit => {
                if !candidate(&req[1], &args[0], &args[1], true)
                    || !candidate(&req[2], &args[0], &args[1], false)
                    || !matches!(goal,Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(x)) if x.sequence.ir()==args[0].ir() && x.value.ir()==args[1].ir())
                {
                    return Err(invalid("CoincidentExtrema"));
                }
            }
            Kind::Order => {
                if !candidate(&req[1], &args[0], &args[1], false)
                    || !candidate(&req[2], &args[0], &args[2], true)
                    || !le(goal, &args[1], &args[2])
                {
                    return Err(invalid("OrderedExtrema"));
                }
            }
            _ => {
                if !sequence(&req[1], &args[1]) || !candidate(&req[2], &args[0], &args[2], upper) {
                    return Err(invalid("OriginalCandidate"));
                }
                match kind {
                    Kind::Compare => {
                        if !candidate(&req[3], &args[1], &args[3], upper)
                            || !member(&req[4], &args[4], StandardSet::NPos)
                            || !le(goal, &args[2], &args[3])
                        {
                            return Err(invalid("ComparisonSubjects"));
                        }
                        formula(kind, args, &req[5])?;
                    }
                    Kind::Equal | Kind::Shift => {
                        if !member(
                            &req[3],
                            &args[3],
                            if kind == Kind::Shift {
                                StandardSet::N
                            } else {
                                StandardSet::NPos
                            },
                        ) || !candidate(goal, &args[1], &args[2], upper)
                        {
                            return Err(invalid("TailSubjects"));
                        }
                        formula(kind, args, &req[4])?;
                    }
                    Kind::Neg => {
                        if !matches!(&req[3],Fact::AtomicFact(AtomicFact::InFact(x)) if x.set==Obj::StandardSet(StandardSet::R)
                            && matches!(&x.element,Obj::ArithmeticOperator(ArithmeticOperator::Neg(c)) if closed_integer(&c.arg)==Some(1)))
                        {
                            return Err(invalid("NegationFixedScalar"));
                        }
                        let Fact::AtomicFact(g) = goal else {
                            return Err(invalid("NegationConclusion"));
                        };
                        let Some((a, v, u, negative)) = extremum_parts(g) else {
                            return Err(invalid("NegationFamily"));
                        };
                        if negative
                            || u == upper
                            || a.ir() != args[1].ir()
                            || !matches!(v,Obj::ArithmeticOperator(ArithmeticOperator::Neg(x)) if x.arg.ir()==args[2].ir())
                        {
                            return Err(invalid("NegationTarget"));
                        }
                        formula(kind, args, &req[4])?;
                    }
                    _ => unreachable!(),
                }
            }
        }
        let (definitions, refs) = self
            .compile_function_limit_requirements(req, dom_proofs, dom_stores, position)
            .map_err(|mut e| {
                e.message = format!("Extremum transport prerequisites: {}", e.message);
                e
            })?;
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        let wd = &conclusions_wd[0];
        self.compile_fact_wd(wd, goal, &formed).map_err(|mut e| {
            e.message = format!("Extremum transport conclusion WD: {}", e.message);
            e
        })?;
        let statement = self
            .compile_formed_fact_proposition(wd, goal, &formed)
            .map_err(|mut e| {
                e.message = format!("Extremum transport conclusion: {}", e.message);
                e
            })?;
        let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
        let objects = args
            .iter()
            .map(|o| self.compile_object_reference(o, &scope))
            .collect::<Result<Vec<_>, _>>()?;
        let values: Vec<_> = objects
            .iter()
            .map(|o| format!("(Litex.denote {o})"))
            .collect();
        let hf = |index: usize| {
            format!("(Litex.unguardedFunctionDomain {} (Litex.denote (Litex.NPos (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet (Litex.R (M := M))) {})",objects[index],refs[index])
        };
        let real = |index: usize| {
            let candidate = match kind {
                Kind::Compare => index,
                Kind::Equal | Kind::Shift | Kind::Neg => 2,
                Kind::Limit => 1,
                Kind::Order => index,
            };
            self.extrema_transport_candidate_real(
                &dom_proofs[candidate],
                &SourcePosition {
                    before: candidate,
                    ..*position
                },
            )
            .map_err(|mut e| {
                e.message = format!("Extremum transport candidate value {index}: {}", e.message);
                e
            })
        };
        let equation = |index: usize, guard: bool| {
            format!("(by\n  intro _n _hn{}\n  exact {} (Litex.semanticObject _n (M.member_isSet _hn)) _hn{}\n)",if guard {" _ho"}else{""},refs[index],if guard {" _ho"}else{""})
        };
        let law = match kind {
            Kind::Compare => format!(
                "Litex.sequenceExtremumCompare {upper} {} {} {} {} {} {} {} {} {}",
                values.join(" "),
                hf(0),
                hf(1),
                real(2)?,
                real(3)?,
                refs[4],
                refs[2],
                refs[3],
                equation(5, true)
            ),
            Kind::Equal => format!(
                "Litex.sequenceExtremumEventuallyEqual {upper} {} {} {} {} {} {} {}",
                values.join(" "),
                hf(0),
                hf(1),
                real(2)?,
                refs[3],
                refs[2],
                equation(4, true)
            ),
            Kind::Shift => format!(
                "Litex.sequenceExtremumShift {upper} {} {} {} {} {} {} {}",
                values.join(" "),
                hf(0),
                hf(1),
                real(2)?,
                refs[3],
                refs[2],
                equation(4, false)
            ),
            Kind::Neg => format!(
                "Litex.sequenceExtremumNeg {upper} {} {} {} {} {} {}",
                values.join(" "),
                hf(0),
                hf(1),
                real(2)?,
                refs[2],
                equation(4, false)
            ),
            Kind::Limit => format!(
                "Litex.sequenceLimitFromExtrema {} {} {} {} {}",
                values.join(" "),
                hf(0),
                real(1)?,
                refs[1],
                refs[2]
            ),
            Kind::Order => format!(
                "Litex.sequenceExtremaOrder {} {} {} {} {} {}",
                values.join(" "),
                hf(0),
                real(1)?,
                real(2)?,
                refs[1],
                refs[2]
            ),
        };
        Ok((
            definitions,
            format!("(show {statement} from {law})"),
            builtin.conclusions.clone(),
        ))
    }
}
