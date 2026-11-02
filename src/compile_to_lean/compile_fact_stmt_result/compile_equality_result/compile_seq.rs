use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_seq_equality(
        &self,
        fact: &EqualFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (source, sequence, signature, reversed) = match (&fact.left, &fact.right) {
            (
                a @ Obj::SetFormer(SetFormer::SeqSet(s)),
                Obj::FunctionSpace(FunctionSpace::FnSet(f)),
            ) => (a, s, f, false),
            (
                Obj::FunctionSpace(FunctionSpace::FnSet(f)),
                a @ Obj::SetFormer(SetFormer::SeqSet(s)),
            ) => (a, s, f, true),
            _ => return Err(LeanCompileError::unsupported("Seq/EqualitySubject")),
        };
        Self::validate_seq_signature(sequence, signature)?;
        let source = self.compile_object_reference(source, position)?;
        let proof = format!("(Litex.seqSet_eq_fnSet {source})");
        Ok(if reversed {
            format!("{proof}.symm")
        } else {
            proof
        })
    }
}

pub(in crate::compile_to_lean) enum FiniteSeqSpaceRule {
    OneBased,
    EmptyInput,
}

enum FiniteSeqDomainSpelling {
    Closed,
    Positive,
    HalfOpen(i128),
    Empty,
}

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_finite_seq_space_equality(
        &self,
        fact: &EqualFact,
        rule: FiniteSeqSpaceRule,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (source, sequence, target, signature, reversed) = match (&fact.left, &fact.right) {
            (
                a @ Obj::SetFormer(SetFormer::FiniteSeqSet(s)),
                b @ Obj::FunctionSpace(FunctionSpace::FnSet(f)),
            ) => (a, s, b, f, false),
            (
                a @ Obj::FunctionSpace(FunctionSpace::FnSet(f)),
                b @ Obj::SetFormer(SetFormer::FiniteSeqSet(s)),
            ) => (b, s, a, f, true),
            _ => return Err(invalid("Endpoints")),
        };
        let spelling = checked_spelling(sequence, signature, rule)?;
        let source = self.compile_object_reference(source, position)?;
        let target = self.compile_object_reference(target, position)?;
        let proof = match spelling {
            FiniteSeqDomainSpelling::Closed => format!("(Litex.finiteSeq_eq_fnSet {source})"),
            FiniteSeqDomainSpelling::Empty => format!("(show Litex.Same {source} {target} from by\n  let _finite_space := {source}\n  let _fn_space := {target}\n  have _right_empty : ∀ x, ¬ M.mem x _fn_space.val.domain := by\n    intro x hx\n    exact Litex.SetSemantics.empty_members (M := M) x ((Litex.SetSemantics.sep_members _ _ x).mp hx).1\n  exact (Litex.finiteSeq_eq_fnSet _finite_space).trans ((Litex.functionSpaceSingletonOfEmptyDomain (Litex.finiteSeqSignature _finite_space) (Litex.finiteSeqDomainEmptyOfLengthZero _finite_space (by rfl))).trans (Litex.functionSpaceSingletonOfEmptyDomain _fn_space.val _right_empty).symm)\n)"),
            other => {
                let domain = match other {
                    FiniteSeqDomainSpelling::Positive => "(Litex.finiteSeqDomainOfNPosBound _finite_space.val.length (Litex.naturalToInteger _finite_space.val.length _finite_space.wd.2))".to_string(),
                    FiniteSeqDomainSpelling::HalfOpen(length) => format!("(by\n  have _base := Litex.integerRangeUpperSuccEqClosed (M := M) (1 : ℤ) ({length} : ℤ)\n  norm_num at _base\n  exact congrArg (fun D => Litex.SetSemantics.sepValue (M := M) D (fun _ => True)) _base\n)"),
                    _ => unreachable!(),
                };
                format!("(show Litex.Same {source} {target} from by\n  let _finite_space := {source}\n  let _fn_space := {target}\n  have _domain : _fn_space.val.domain = Litex.finiteSeqDomain _finite_space.val.length := {domain}\n  change Litex.FunctionSemantics.fnSetValue (Litex.finiteSeqDomain _finite_space.val.length) (Litex.denote _finite_space.val.carrier) = Litex.FunctionSemantics.fnSetValue _fn_space.val.domain (Litex.denote _finite_space.val.carrier)\n  exact congrArg (fun D => Litex.FunctionSemantics.fnSetValue D (Litex.denote _finite_space.val.carrier)) _domain.symm\n)")
            }
        };
        Ok(if reversed {
            format!("({proof}).symm")
        } else {
            proof
        })
    }
}

/// Mirror the selected equality rule; complete-domain validators stay canonical.
fn checked_spelling(
    sequence: &FiniteSeqSet,
    signature: &FnSet,
    rule: FiniteSeqSpaceRule,
) -> Result<FiniteSeqDomainSpelling, LeanCompileError> {
    let [group] = signature.set_bound_parameters.groups.as_slice() else {
        return Err(invalid("ParameterGroups"));
    };
    if group.params.len() != 1 || signature.ret_set.ir() != sequence.set.ir() {
        return Err(invalid("Signature"));
    }
    let domain = group.param_type.as_ref();
    match rule {
        FiniteSeqSpaceRule::EmptyInput => {
            if !signature.dom_facts.is_empty()
                || !matches!(sequence.n.as_ref(),Obj::Literal(Literal::Number(n)) if n.normalized_value=="0")
                || !matches!(domain,Obj::SetFormer(SetFormer::ListSet(s)) if s.list.is_empty())
            {
                return Err(invalid("EmptyInputShape"));
            }
            Ok(FiniteSeqDomainSpelling::Empty)
        }
        FiniteSeqSpaceRule::OneBased => {
            if matches!(domain, Obj::StandardSet(StandardSet::NPos)) {
                let [QuantifierFreeFact::AtomicFact(AtomicFact::LessEqualFact(bound))] =
                    signature.dom_facts.as_slice()
                else {
                    return Err(invalid("PositiveGuard"));
                };
                let parameter = Obj::Identifier(IdentifierObj::from_bound_name(&group.params[0]));
                if bound.left.ir() != parameter.ir() || bound.right.ir() != sequence.n.ir() {
                    return Err(invalid("PositiveBound"));
                }
                return Ok(FiniteSeqDomainSpelling::Positive);
            }
            if !signature.dom_facts.is_empty() {
                return Err(invalid("UnexpectedGuards"));
            }
            match domain {
                Obj::SetFormer(SetFormer::ClosedRange(range))
                    if literal_i128(&range.start) == Some(1)
                        && range.end.ir() == sequence.n.ir() =>
                {
                    Ok(FiniteSeqDomainSpelling::Closed)
                }
                Obj::SetFormer(SetFormer::Range(range))
                    if literal_i128(&range.start) == Some(1) =>
                {
                    let (Some(length), Some(stop)) =
                        (literal_i128(&sequence.n), literal_i128(&range.end))
                    else {
                        return Err(invalid("LiteralHalfOpenBound"));
                    };
                    if length.checked_add(1) != Some(stop) {
                        return Err(invalid("HalfOpenSuccessor"));
                    }
                    Ok(FiniteSeqDomainSpelling::HalfOpen(length))
                }
                _ => Err(invalid("OneBasedDomain")),
            }
        }
    }
}
fn literal_i128(object: &Obj) -> Option<i128> {
    match object {
        Obj::Literal(Literal::Number(n)) => n.normalized_value.parse().ok(),
        _ => None,
    }
}
fn invalid(part: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("FiniteSeqSpace/{part}"))
}
