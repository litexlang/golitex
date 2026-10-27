//! Consume the selected bounded integer-interval enumeration rule.
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

fn literal(obj: &Obj) -> Option<i128> {
    let Obj::Literal(Literal::Number(number)) = obj else {
        return None;
    };
    number.normalized_value.parse().ok()
}

fn disjunction_branch(index: usize, length: usize, proof: String) -> String {
    let mut result = if index + 1 == length {
        proof
    } else {
        format!("Or.inl ({proof})")
    };
    for _ in 0..index {
        result = format!("Or.inr ({result})");
    }
    result
}

impl LitexToLeanCompiler {
    pub(super) fn compile_closed_range_literal(
        &self,
        fact: &EqualFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let (
                Obj::SetFormer(SetFormer::ClosedRange(range)),
                Obj::SetFormer(SetFormer::ListSet(set)),
            ) = (left, right)
            else {
                continue;
            };
            let (Some(start), Some(end)) = (literal(&range.start), literal(&range.end)) else {
                continue;
            };
            let count = if start > end {
                Some(0)
            } else {
                end.checked_sub(start)
                    .and_then(|x| x.checked_add(1))
                    .and_then(|x| usize::try_from(x).ok())
            };
            let Some(count) = count.filter(|n| *n <= 1024 && *n == set.list.len()) else {
                continue;
            };
            if !set
                .list
                .iter()
                .enumerate()
                .all(|(i, x)| literal(x) == start.checked_add(i as i128))
            {
                continue;
            }
            let range_object = self.compile_object_reference(left, position)?;
            let list_object = self.compile_object_reference(right, position)?;
            let mut list_value = "Litex.SetSemantics.emptyValue (M := M)".to_string();
            let mut list_equality = "Eq.refl _".to_string();
            for i in (0..count).rev() {
                let k = start + i as i128;
                list_value = format!(
                    "Litex.SetSemantics.insertValue (M.number (({k} : ℤ) : ℂ)) ({list_value})"
                );
                list_equality = format!(
                    "congrArg₂ (Litex.SetSemantics.insertValue (M := M)) ((Litex.NativeBridge.denoteNumber (M := M) ({k} : ℂ)).trans (congrArg M.number (by norm_num))) ({list_equality})"
                );
            }
            let cases = if count == 0 {
                "  constructor\n  · rintro ⟨k, _, hlo, hhi⟩\n    omega\n  · exact False.elim"
                    .to_string()
            } else {
                let alternatives = (0..count)
                    .map(|i| format!("k = ({} : ℤ)", start + i as i128))
                    .collect::<Vec<_>>()
                    .join(" ∨ ");
                let names = (0..count)
                    .map(|i| format!("h_{i}"))
                    .collect::<Vec<_>>()
                    .join(" | ");
                let mut lines = format!(
                    "  constructor\n  · rintro ⟨k, rfl, hlo, hhi⟩\n    have h : {alternatives} := by omega\n    rcases h with {names}\n"
                );
                for i in 0..count {
                    let branch = disjunction_branch(i, count, "rfl".into());
                    lines.push_str(&format!("    · subst k\n      exact {branch}\n"));
                }
                lines.push_str(&format!("  · intro h\n    rcases h with {names}\n"));
                for i in 0..count {
                    let k = start + i as i128;
                    lines.push_str(&format!(
                        "    · exact ⟨({k} : ℤ), h_{i}, by omega, by omega⟩\n"
                    ));
                }
                lines
            };
            let simp_laws = if count == 0 {
                "Litex.SetSemantics.empty_members"
            } else {
                "Litex.SetSemantics.insert_members, Litex.SetSemantics.empty_members, or_false"
            };
            let symm = if reversed { ".symm" } else { "" };
            return Ok(format!(
                "((by\n  let _range := {range_object}\n  let _list := {list_object}\n  change Litex.denote _range = Litex.denote _list\n  have hr : Litex.denote _range = Litex.closedRangeValue (M.number (({start} : ℤ) : ℂ)) (M.number (({end} : ℤ) : ℂ)) := congrArg₂ (Litex.closedRangeValue (M := M)) ((Litex.NativeBridge.denoteNumber (M := M) ({start} : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) ({end} : ℂ)).trans (congrArg M.number (by norm_num)))\n  have hs : Litex.denote _list = ({list_value}) := {list_equality}\n  apply Litex.SetSemantics.ext _ _ (Litex.isSet _range) (Litex.isSet _list)\n  intro x\n  rw [hr, hs, Litex.closedRangeValue_members]\n  simp only [{simp_laws}]\n{cases}\n) : Litex.Same {range_object} {list_object}){symm}"
            ));
        }
        Err(LeanCompileError::unsupported(
            "ClosedRangeLiteral/Endpoints",
        ))
    }
}
