//! Replay the captured affine finite-extremum contracts, including surplus bounds.
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
use crate::prelude::*;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    AddConstant,
    Nonnegative,
    Negative,
    AddConvergent,
    SumBound,
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("SequenceExtremaAffine/{stage}"))
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
fn ordinary(f: &Fact, a: &Obj, v: &Obj) -> bool {
    matches!(f,Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(x)) if x.sequence.ir()==a.ir() && x.value.ir()==v.ir())
}
fn operation(kind: Kind, o: &Obj) -> Option<(&Obj, &Obj)> {
    match o {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(x))
            if matches!(
                kind,
                Kind::AddConstant | Kind::AddConvergent | Kind::SumBound
            ) =>
        {
            Some((&x.left, &x.right))
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(x))
            if matches!(kind, Kind::Nonnegative | Kind::Negative) =>
        {
            Some((&x.left, &x.right))
        }
        _ => None,
    }
}
fn original_forall<'a>(
    f: &'a Fact,
    args: &[Obj],
) -> Result<(&'a ForallFact, Obj), LeanCompileError> {
    let Fact::ForallFact(f) = f else {
        return Err(invalid("Formula"));
    };
    let n = parameter(&f.typed_parameters, &Obj::StandardSet(StandardSet::NPos))?;
    if !f.dom_facts.is_empty() || args.iter().any(|a| contains_parameter(a, n.id)) {
        return Err(invalid("FormulaDomainOrCapture"));
    }
    Ok((f, Obj::Identifier(IdentifierObj::from_bound_name(n))))
}
fn formula(kind: Kind, args: &[Obj], f: &Fact) -> Result<(), LeanCompileError> {
    let (f, n) = original_forall(f, args)?;
    let [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq))] =
        f.then_facts.as_slice()
    else {
        return Err(invalid("PointwiseEquation"));
    };
    let output = if matches!(kind, Kind::AddConvergent | Kind::SumBound) {
        2
    } else {
        1
    };
    let Some((left, right)) = operation(kind, &eq.right) else {
        return Err(invalid("FormulaOperation"));
    };
    let operands = match kind {
        Kind::AddConstant => call_matches(left, &args[0], &n) && right.ir() == args[3].ir(),
        Kind::Nonnegative | Kind::Negative => {
            left.ir() == args[3].ir() && call_matches(right, &args[0], &n)
        }
        Kind::AddConvergent | Kind::SumBound => {
            call_matches(left, &args[0], &n) && call_matches(right, &args[1], &n)
        }
    };
    if !call_matches(&eq.left, &args[output], &n) || !operands {
        return Err(invalid("OriginalPointwiseOperands"));
    }
    Ok(())
}
fn bound(args: &[Obj], sequence: usize, value: usize, f: &Fact) -> Result<(), LeanCompileError> {
    let (f, n) = original_forall(f, args)?;
    if !matches!(f.then_facts.as_slice(),[ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::LessEqualFact(x))]
        if x.right.ir()==args[value].ir() && matches!(&x.left,Obj::ArithmeticOperator(ArithmeticOperator::Abs(a)) if call_matches(&a.arg,&args[sequence],&n)))
    {
        return Err(invalid("OriginalAbsoluteBound"));
    }
    Ok(())
}
impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_sequence_extrema_affine(
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
            SequenceLimsupAddConstant => (Kind::AddConstant, true, 4, 5),
            SequenceLiminfAddConstant => (Kind::AddConstant, false, 4, 5),
            SequenceLimsupScaleNonnegative => (Kind::Nonnegative, true, 4, 6),
            SequenceLiminfScaleNonnegative => (Kind::Nonnegative, false, 4, 6),
            SequenceLimsupScaleNegative => (Kind::Negative, true, 4, 6),
            SequenceLiminfScaleNegative => (Kind::Negative, false, 4, 6),
            SequenceLimsupAddConvergent => (Kind::AddConvergent, true, 5, 6),
            SequenceLiminfAddConvergent => (Kind::AddConvergent, false, 5, 6),
            SequenceLimsupSumBound => (Kind::SumBound, true, 8, 11),
            SequenceLiminfSumBound => (Kind::SumBound, false, 8, 11),
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
        if !sequence(&req[0], &args[0]) || !sequence(&req[1], &args[1]) {
            return Err(invalid("SequenceDomains"));
        }
        match kind {
            Kind::AddConstant | Kind::Nonnegative | Kind::Negative => {
                if !candidate(&req[2], &args[0], &args[2], upper)
                    || !member(&req[3], &args[3], StandardSet::R)
                {
                    return Err(invalid("CandidateOrScalar"));
                }
                if kind == Kind::Nonnegative
                    && !matches!(&req[4],Fact::AtomicFact(AtomicFact::LessEqualFact(x)) if closed_integer(&x.left)==Some(0) && x.right.ir()==args[3].ir())
                {
                    return Err(invalid("NonnegativeScalar"));
                }
                if kind == Kind::Negative
                    && !matches!(&req[4],Fact::AtomicFact(AtomicFact::LessFact(x)) if x.left.ir()==args[3].ir() && closed_integer(&x.right)==Some(0))
                {
                    return Err(invalid("NegativeScalar"));
                }
                formula(kind, args, &req[count - 1])?;
                let Fact::AtomicFact(g) = goal else {
                    return Err(invalid("Conclusion"));
                };
                let Some((a, v, u, negative)) = extremum_parts(g) else {
                    return Err(invalid("ConclusionFamily"));
                };
                let Some((left, right)) = operation(kind, v) else {
                    return Err(invalid("ConclusionOperation"));
                };
                let values = if kind == Kind::AddConstant {
                    left.ir() == args[2].ir() && right.ir() == args[3].ir()
                } else {
                    left.ir() == args[3].ir() && right.ir() == args[2].ir()
                };
                if negative
                    || a.ir() != args[1].ir()
                    || u != (if kind == Kind::Negative {
                        !upper
                    } else {
                        upper
                    })
                    || !values
                {
                    return Err(invalid("ConclusionSubjects"));
                }
            }
            Kind::AddConvergent | Kind::SumBound => {
                if !sequence(&req[2], &args[2])
                    || !candidate(&req[3], &args[0], &args[3], upper)
                    || !(if kind == Kind::SumBound {
                        candidate(&req[4], &args[1], &args[4], upper)
                    } else {
                        ordinary(&req[4], &args[1], &args[4])
                    })
                {
                    return Err(invalid("SumCandidates"));
                }
                formula(kind, args, &req[5])?;
                if kind == Kind::SumBound {
                    if !candidate(&req[6], &args[2], &args[5], upper)
                        || !member(&req[7], &args[6], StandardSet::RPos)
                        || !member(&req[9], &args[7], StandardSet::RPos)
                    {
                        return Err(invalid("SumBoundCandidatesOrCarriers"));
                    }
                    bound(args, 0, 6, &req[8])?;
                    bound(args, 1, 7, &req[10])?;
                    let Fact::AtomicFact(AtomicFact::LessEqualFact(g)) = goal else {
                        return Err(invalid("SumBoundConclusion"));
                    };
                    let (value, sum) = if upper {
                        (&g.left, &g.right)
                    } else {
                        (&g.right, &g.left)
                    };
                    let Some((left, right)) = operation(kind, sum) else {
                        return Err(invalid("SumBoundOperation"));
                    };
                    if value.ir() != args[5].ir()
                        || left.ir() != args[3].ir()
                        || right.ir() != args[4].ir()
                    {
                        return Err(invalid("SumBoundOperands"));
                    }
                } else {
                    let Fact::AtomicFact(g) = goal else {
                        return Err(invalid("SumConclusion"));
                    };
                    let Some((a, v, u, negative)) = extremum_parts(g) else {
                        return Err(invalid("SumConclusionFamily"));
                    };
                    let Some((left, right)) = operation(kind, v) else {
                        return Err(invalid("SumConclusionOperation"));
                    };
                    if negative
                        || u != upper
                        || a.ir() != args[2].ir()
                        || left.ir() != args[3].ir()
                        || right.ir() != args[4].ir()
                    {
                        return Err(invalid("SumConclusionOperands"));
                    }
                }
            }
        }
        let (definitions, refs) =
            self.compile_function_limit_requirements(req, dom_proofs, dom_stores, position)?;
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        let wd = &conclusions_wd[0];
        self.compile_fact_wd(wd, goal, &formed)?;
        let statement = self.compile_formed_fact_proposition(wd, goal, &formed)?;
        let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
        let objects = args
            .iter()
            .map(|o| self.compile_object_reference(o, &scope))
            .collect::<Result<Vec<_>, _>>()?;
        let values: Vec<_> = objects
            .iter()
            .map(|o| format!("(Litex.denote {o})"))
            .collect();
        let hf = |i: usize| {
            format!("(Litex.unguardedFunctionDomain {} (Litex.denote (Litex.NPos (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet (Litex.R (M := M))) {})",objects[i],refs[i])
        };
        let real = |i: usize| {
            self.extrema_transport_candidate_real(
                &dom_proofs[i],
                &SourcePosition {
                    before: i,
                    ..*position
                },
            )
        };
        let eq = |i: usize| {
            format!("(by\n  intro _n _hn\n  exact {} (Litex.semanticObject _n (M.member_isSet _hn)) _hn\n)",refs[i])
        };
        let law = match kind {
            Kind::AddConstant => format!(
                "Litex.sequenceExtremumAddConstant {upper} {} {} {} {} {} {} {}",
                values.join(" "),
                hf(0),
                hf(1),
                real(2)?,
                refs[3],
                refs[2],
                eq(4)
            ),
            Kind::Nonnegative | Kind::Negative => format!(
                "Litex.{} {upper} {} {} {} {} {} {} {} {}",
                if kind == Kind::Negative {
                    "sequenceExtremumScaleNegative"
                } else {
                    "sequenceExtremumScaleNonnegative"
                },
                values.join(" "),
                hf(0),
                hf(1),
                real(2)?,
                refs[3],
                refs[4],
                refs[2],
                eq(5)
            ),
            Kind::AddConvergent => format!(
                "Litex.sequenceExtremumAddConvergent {upper} {} {} {} {} {} {} {} {} {}",
                values.join(" "),
                hf(0),
                hf(1),
                hf(2),
                real(3)?,
                real(4)?,
                refs[3],
                refs[4],
                eq(5)
            ),
            Kind::SumBound => format!(
                "Litex.sequenceExtremumSumBound {upper} {} {} {} {} {} {} {} {} {} {} {}",
                values[..6].join(" "),
                hf(0),
                hf(1),
                hf(2),
                real(3)?,
                real(4)?,
                real(6)?,
                refs[3],
                refs[4],
                refs[6],
                eq(5)
            ),
        };
        Ok((
            definitions,
            format!("(show {statement} from {law})"),
            builtin.conclusions.clone(),
        ))
    }
}
