use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_or_fact::{
    integer_range_cover_indices, integer_range_literal_bounds,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_integer_range_cover(
        &self,
        fact: &OrFact,
        subject: &Obj,
        interval: &Obj,
        membership: &VerifyFactResult,
        carrier_equal: &KnownEqualityPathProof,
        branch_indices: &[usize],
        closed: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let correct_constructor = if closed {
            matches!(interval, Obj::SetFormer(SetFormer::ClosedRange(_)))
        } else {
            matches!(interval, Obj::SetFormer(SetFormer::Range(_)))
        };
        if !correct_constructor
            || integer_range_cover_indices(subject, interval, &fact.facts).as_deref()
                != Some(branch_indices)
        {
            return Err(LeanCompileError::new(
                "Or/IntegerRangeCover",
                "The original equality branches do not match the recorded interval cover.",
            ));
        }
        let Fact::AtomicFact(AtomicFact::InFact(member)) = source_subject(membership)? else {
            return Err(LeanCompileError::unsupported("Or/IntegerRangeMembership"));
        };
        if member.element.ir() != subject.ir() {
            return Err(LeanCompileError::new(
                "Or/IntegerRangeMembership",
                "The member child has another subject.",
            ));
        }
        let checked = self.compile_verify(membership, position)?;
        let transport =
            self.compile_equality_path(&member.set, interval, carrier_equal, position)?;
        let subject = self.compile_object_reference(subject, position)?;
        let interval_term = self.compile_object_reference(interval, position)?;
        let source_carrier = self.compile_object_reference(&member.set, position)?;
        let (start, count) = integer_range_literal_bounds(interval).unwrap();
        let end = if closed {
            start + (count as i128 - 1)
        } else {
            start + count as i128
        };
        let theorem = if closed {
            "inClosedRange_iff"
        } else {
            "inRange_iff"
        };
        let (lower, upper) = match interval {
            Obj::SetFormer(SetFormer::ClosedRange(range)) => (&range.start, &range.end),
            Obj::SetFormer(SetFormer::Range(range)) => (&range.start, &range.end),
            _ => unreachable!(),
        };
        let lower_denote = self.compile_numeric_observation(lower, position)?.1;
        let upper_denote = self.compile_numeric_observation(upper, position)?.1;
        let mut lines = vec![
            format!("let _interval := {interval_term}"),
            format!("have _member : {} := {}", checked.0, checked.1),
            format!("have _carrier : Litex.Same {source_carrier} _interval := {transport}"),
            format!("have _range_member : Litex.In {subject} _interval := by change M.mem (Litex.denote {subject}) (Litex.denote _interval); rw [← _carrier]; exact _member"),
            format!("obtain ⟨_lower, _upper, _k, _hl, _hu, _hx, _hlo, _hhi⟩ := (Litex.{theorem} _interval.val.start _interval.val.finish {subject} _interval.wd.1 _interval.wd.2).mp _range_member"),
            format!("have _start_num : Litex.denote _interval.val.start = M.number (({start} : ℤ) : ℂ) := ({lower_denote}).trans (congrArg M.number (by norm_num))"),
            format!("have _lo : _lower = ({start} : ℤ) := by exact_mod_cast M.number_injective (_hl.symm.trans _start_num)"),
            format!("have _end_num : Litex.denote _interval.val.finish = M.number (({end} : ℤ) : ℂ) := ({upper_denote}).trans (congrArg M.number (by norm_num))"),
            format!("have _hi : _upper = ({end} : ℤ) := by exact_mod_cast M.number_injective (_hu.symm.trans _end_num)"),
            "subst _lower _upper".into(),
        ];
        let alternatives = (0..count)
            .map(|i| format!("_k = ({} : ℤ)", start + i as i128))
            .collect::<Vec<_>>()
            .join(" ∨ ");
        lines.push(format!("have _cases : {alternatives} := by omega"));
        lines.push(format!(
            "rcases _cases with {}",
            (0..count)
                .map(|i| format!("_case_{i}"))
                .collect::<Vec<_>>()
                .join(" | ")
        ));
        for (offset, &index) in branch_indices.iter().enumerate() {
            let AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(equal)) = &fact.facts[index]
            else {
                unreachable!()
            };
            let reversed = equal.right.ir() == member.element.ir();
            let literal = if reversed { &equal.left } else { &equal.right };
            let literal_denote = self.compile_numeric_observation(literal, position)?.1;
            let literal = self.compile_object_reference(literal, position)?;
            let value = start + offset as i128;
            let numeric = format!("(show Litex.denote {literal} = M.number (({value} : ℤ) : ℂ) from ({literal_denote}).trans (congrArg M.number (by norm_num)))");
            let mut term = format!("(show Litex.Same {subject} {literal} from ((_hx.trans (congrArg (fun k : ℤ => M.number (k : ℂ)) _case_{offset})).trans ({numeric}).symm))");
            if reversed {
                term = format!("({term}).symm");
            }
            if index + 1 != fact.facts.len() {
                term = format!("Or.inl ({term})");
            }
            for _ in 0..index {
                term = format!("Or.inr ({term})");
            }
            lines.push(format!("· exact {term}"));
        }
        Ok(format!(
            "(by\n  {}\n)",
            lines.join("\n").replace('\n', "\n  ")
        ))
    }
}
