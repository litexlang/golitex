use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_or_integer_discrete(
        &self,
        fact: &OrFact,
        subject: &Obj,
        base: &Obj,
        subject_z: &VerifyFactResult,
        base_z: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let [AndChainAtomicFact::AtomicFact(first), AndChainAtomicFact::AtomicFact(second)] =
            fact.facts.as_slice()
        else {
            return Err(invalid("DiscreteBranches"));
        };
        let (a, b, sa) = source_order_oriented(first)?;
        let (c, d, sb) = source_order_oriented(second)?;
        if sa || sb {
            return Err(invalid("DiscreteRelation"));
        }
        let one = |o: &Obj| matches!(o,Obj::Literal(Literal::Number(n)) if n.normalized_value=="1");
        let successor = |o: &Obj| matches!(o,Obj::ArithmeticOperator(ArithmeticOperator::Add(p)) if p.left.ir()==base.ir() && one(&p.right));
        let predecessor = |o: &Obj| matches!(o,Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) if p.left.ir()==base.ir() && one(&p.right));
        let (pred, swapped) = if a.ir() == subject.ir()
            && b.ir() == base.ir()
            && successor(c)
            && d.ir() == subject.ir()
        {
            (false, false)
        } else if c.ir() == subject.ir()
            && d.ir() == base.ir()
            && successor(a)
            && b.ir() == subject.ir()
        {
            (false, true)
        } else if a.ir() == base.ir()
            && b.ir() == subject.ir()
            && c.ir() == subject.ir()
            && predecessor(d)
        {
            (true, false)
        } else if c.ir() == base.ir()
            && d.ir() == subject.ir()
            && a.ir() == subject.ir()
            && predecessor(b)
        {
            (true, true)
        } else {
            return Err(invalid("DiscreteEndpoints"));
        };
        let mut lines = Vec::new();
        for (index, (checked, object)) in [(subject_z, subject), (base_z, base)]
            .into_iter()
            .enumerate()
        {
            if membership_subject(&source_subject(checked)?, object)? != StandardSet::Z {
                return Err(invalid("DiscreteCarrier"));
            }
            let compiled = self.compile_verify(
                checked,
                &SourcePosition {
                    before: position.before + index,
                    ..*position
                },
            )?;
            lines.push(format!(
                "have _integer_{index} : {} := {}",
                compiled.0, compiled.1
            ));
        }
        let complete = SourcePosition {
            before: position.before + 2,
            ..*position
        };
        let subject = self.compile_object_reference(subject, &complete)?;
        let base = self.compile_object_reference(base, &complete)?;
        let law = if pred {
            "integerDiscretePredecessorValue"
        } else {
            "integerDiscreteSuccessorValue"
        };
        lines.push(format!("exact {}(Litex.{law} (Litex.denote {subject}) (Litex.denote {base}) _integer_0 _integer_1)",if swapped {"Or.symm "}else{""}));
        Ok(block(lines))
    }

    pub(in crate::compile_to_lean) fn compile_or_absolute_sign(
        &self,
        fact: &OrFact,
        arg: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let [AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(first)), AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(second))] =
            fact.facts.as_slice()
        else {
            return Err(invalid("AbsoluteBranches"));
        };
        let classify = |equal: &EqualFact| {
            for (absolute, other, reversed) in [
                (&equal.left, &equal.right, false),
                (&equal.right, &equal.left, true),
            ] {
                if matches!(absolute,Obj::ArithmeticOperator(ArithmeticOperator::Abs(p)) if p.arg.ir()==arg.ir())
                {
                    if other.ir() == arg.ir() {
                        return Ok((false, reversed));
                    }
                    if matches!(other,Obj::ArithmeticOperator(ArithmeticOperator::Neg(p)) if p.arg.ir()==arg.ir())
                    {
                        return Ok((true, reversed));
                    }
                }
            }
            Err(invalid("AbsoluteSubjects"))
        };
        let a = classify(first)?;
        let b = classify(second)?;
        if a.0 == b.0 {
            return Err(invalid("AbsoluteCoverage"));
        }
        let absolute = if a.1 { &first.right } else { &first.left };
        let object = self.compile_object_reference(absolute, position)?;
        let (positive, negative) = if a.0 { (1, 0) } else { (0, 1) };
        let orientations = [a.1, b.1];
        Ok(block(vec![format!("let _absolute := {object}"),
            "rcases Litex.absoluteSignSplitValue false (Litex.denote _absolute.val.arg) _absolute.wd with _positive | _negative".into(),
            format!("· exact {}",introduce(if orientations[positive] {"_positive.symm".into()}else{"_positive".into()},positive,2)),
            format!("· exact {}",introduce(if orientations[negative] {"_negative.symm".into()}else{"_negative".into()},negative,2))]))
    }

    pub(in crate::compile_to_lean) fn compile_or_real_totality(
        &self,
        fact: &OrFact,
        left: &Obj,
        right: &Obj,
        left_real: &VerifyFactResult,
        right_real: &VerifyFactResult,
        kind: usize,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let branches = fact
            .facts
            .iter()
            .map(|f| match f {
                AndChainAtomicFact::AtomicFact(f) => Ok(f),
                _ => Err(invalid("AtomicBranches")),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let equality_reversed = if kind < 3 {
            let (equal, less, greater) = match (kind, branches.as_slice()) {
                (
                    0,
                    [AtomicFact::EqualFact(e), AtomicFact::LessFact(l), AtomicFact::GreaterFact(g)],
                ) => (e, l, g),
                (
                    1,
                    [AtomicFact::LessFact(l), AtomicFact::EqualFact(e), AtomicFact::GreaterFact(g)],
                ) => (e, l, g),
                (
                    2,
                    [AtomicFact::GreaterFact(g), AtomicFact::EqualFact(e), AtomicFact::LessFact(l)],
                ) => (e, l, g),
                _ => return Err(invalid("TrichotomyOrder")),
            };
            if less.left.ir() != left.ir()
                || less.right.ir() != right.ir()
                || greater.left.ir() != left.ir()
                || greater.right.ir() != right.ir()
            {
                return Err(invalid("TrichotomySubjects"));
            }
            equality_orientation(equal, left, right)?
        } else if kind == 3 {
            let [first, second] = branches.as_slice() else {
                return Err(invalid("TotalityShape"));
            };
            let (a, b, strict) = source_order_oriented(first)?;
            let (c, d, other_strict) = source_order_oriented(second)?;
            if strict
                || other_strict
                || !((a.ir() == left.ir()
                    && b.ir() == right.ir()
                    && c.ir() == right.ir()
                    && d.ir() == left.ir())
                    || (a.ir() == right.ir()
                        && b.ir() == left.ir()
                        && c.ir() == left.ir()
                        && d.ir() == right.ir()))
            {
                return Err(invalid("TotalitySubjects"));
            }
            a.ir() != left.ir() || b.ir() != right.ir()
        } else {
            return Err(invalid("SelectedKind"));
        };
        let mut lines = Vec::new();
        for (index, (checked, object)) in [(left_real, left), (right_real, right)]
            .into_iter()
            .enumerate()
        {
            if membership_subject(&source_subject(checked)?, object)? != StandardSet::R {
                return Err(invalid("RealChildren"));
            }
            let compiled = self.compile_verify(
                checked,
                &SourcePosition {
                    before: position.before + index,
                    ..*position
                },
            )?;
            lines.push(format!(
                "have _or_real_{index} : {} := {}",
                compiled.0, compiled.1
            ));
        }
        let complete = SourcePosition {
            before: position.before + 2,
            ..*position
        };
        lines.push(format!(
            "let _or_left := {}",
            self.compile_object_reference(left, &complete)?
        ));
        lines.push(format!(
            "let _or_right := {}",
            self.compile_object_reference(right, &complete)?
        ));
        let values = "(Litex.denote _or_left) (Litex.denote _or_right) _or_real_0 _or_real_1";
        if kind == 3 {
            lines.push(format!(
                "exact {}(Litex.realWeakTotalValue {values})",
                if equality_reversed { "Or.symm " } else { "" }
            ));
        } else {
            lines.push(format!(
                "rcases Litex.realTrichotomyValue {values} with _equal | _less | _greater"
            ));
            let indices = match kind {
                0 => [0, 1, 2],
                1 => [1, 0, 2],
                _ => [1, 2, 0],
            };
            for (index, name) in indices.into_iter().zip([
                if equality_reversed {
                    "_equal.symm"
                } else {
                    "_equal"
                },
                "_less",
                "_greater",
            ]) {
                lines.push(format!("· exact {}", introduce(name.into(), index, 3)));
            }
        }
        Ok(block(lines))
    }

    pub(in crate::compile_to_lean) fn compile_or_natural_zero(
        &self,
        fact: &OrFact,
        n: &Obj,
        checked: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let [AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(e)), AndChainAtomicFact::AtomicFact(AtomicFact::GreaterEqualFact(g))] =
            fact.facts.as_slice()
        else {
            return Err(invalid("NaturalBranches"));
        };
        if e.left.ir() != n.ir()
            || g.left.ir() != n.ir()
            || !is_exact_zero(&e.right)
            || !matches!(&g.right,Obj::Literal(Literal::Number(num)) if num.normalized_value=="1")
            || membership_subject(&source_subject(checked)?, n)? != StandardSet::N
        {
            return Err(invalid("NaturalSubjects"));
        }
        let compiled = self.compile_verify(checked, position)?;
        let complete = SourcePosition {
            before: position.before + 1,
            ..*position
        };
        let n = self.compile_object_reference(n, &complete)?;
        Ok(block(vec![
            format!("have _natural : {} := {}", compiled.0, compiled.1),
            format!("exact Litex.naturalZeroOrAtLeastOneValue (Litex.denote {n}) _natural"),
        ]))
    }

    pub(in crate::compile_to_lean) fn compile_or_weak_cover(
        &self,
        fact: &OrFact,
        left: &Obj,
        right: &Obj,
        checked: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (equal, strict, equal_index) = match fact.facts.as_slice() {
            [AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(e)), AndChainAtomicFact::AtomicFact(s)] => {
                (e, s, 0)
            }
            [AndChainAtomicFact::AtomicFact(s), AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(e))] => {
                (e, s, 1)
            }
            _ => return Err(invalid("WeakCoverShape")),
        };
        let reverse = match strict {
            AtomicFact::LessFact(p) if p.left.ir() == left.ir() && p.right.ir() == right.ir() => {
                false
            }
            AtomicFact::GreaterFact(p)
                if p.left.ir() == left.ir() && p.right.ir() == right.ir() =>
            {
                true
            }
            _ => return Err(invalid("WeakCoverSubjects")),
        };
        let (a, b) = if reverse {
            (right, left)
        } else {
            (left, right)
        };
        let eq_reverse = equality_orientation(equal, a, b)?;
        let source = source_subject(checked)?;
        let Fact::AtomicFact(source) = source else {
            return Err(invalid("WeakCoverChild"));
        };
        let (x, y, is_strict) = source_order_oriented(&source)?;
        if is_strict || x.ir() != a.ir() || y.ir() != b.ir() {
            return Err(invalid("WeakCoverChild"));
        }
        let compiled = self.compile_verify(checked, position)?;
        let complete = SourcePosition {
            before: position.before + 1,
            ..*position
        };
        let a = self.compile_object_reference(a, &complete)?;
        let b = self.compile_object_reference(b, &complete)?;
        Ok(block(vec![
            format!("have _weak : {} := {}", compiled.0, compiled.1),
            format!("rcases Litex.leEqOrLt {a} {b} _weak with _equal | _strict"),
            format!(
                "· exact {}",
                introduce(
                    if eq_reverse {
                        "_equal.symm".into()
                    } else {
                        "_equal".into()
                    },
                    equal_index,
                    2
                )
            ),
            format!(
                "· exact {}",
                introduce("_strict".into(), 1 - equal_index, 2)
            ),
        ]))
    }
}
fn equality_orientation(equal: &EqualFact, a: &Obj, b: &Obj) -> Result<bool, LeanCompileError> {
    if equal.left.ir() == a.ir() && equal.right.ir() == b.ir() {
        Ok(false)
    } else if equal.left.ir() == b.ir() && equal.right.ir() == a.ir() {
        Ok(true)
    } else {
        Err(invalid("EqualitySubjects"))
    }
}
fn introduce(mut term: String, index: usize, count: usize) -> String {
    if index + 1 != count {
        term = format!("(Or.inl {term})");
    }
    for _ in 0..index {
        term = format!("(Or.inr {term})");
    }
    term
}
fn block(lines: Vec<String>) -> String {
    format!("(by\n  {}\n)", lines.join("\n").replace('\n', "\n  "))
}
fn invalid(part: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("OrOrder/{part}"))
}
