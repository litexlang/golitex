use crate::compile_to_lean::compile_expand_range_stmt_result::integer_interval_parts;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_integer_enumeration(
        &self,
        carrier: &Obj,
        input: &str,
        membership: &str,
        case: &str,
        position: &SourcePosition<'_>,
        branch: impl Fn(usize) -> Result<String, LeanCompileError>,
    ) -> Result<String, LeanCompileError> {
        let (start, end, closed) = integer_interval_parts(carrier)?;
        let (lower, hl) = self.compile_interval_integer_endpoint(start, position)?;
        let (upper, hu) = self.compile_interval_integer_endpoint(end, position)?;
        let empty = if closed {
            upper < lower
        } else {
            upper <= lower
        };
        let count = if empty {
            Some(0)
        } else {
            upper
                .checked_sub(lower)
                .and_then(|n| if closed { n.checked_add(1) } else { Some(n) })
        };
        if count.is_none_or(|n| n > 1024) {
            return Err(LeanCompileError::unsupported(
                "Enumeration/IntervalCoverage",
            ));
        }
        let range = self.compile_object_reference(carrier, position)?;
        let family = if closed { "ClosedRange" } else { "Range" };
        let mut lines = vec![format!(
            "obtain ⟨_enumerated_integer, _enumerated_same, _enumerated_lower, _enumerated_upper⟩ := Litex.in{family}Integer {range} {input} ({lower} : ℤ) ({upper} : ℤ) {hl} {hu} {membership}"
        )];
        if empty {
            lines.push("have _empty_interval : False := by omega".into());
            lines.push("exact False.elim _empty_interval".into());
        } else {
            let values = (0..count.unwrap() as usize)
                .map(|i| lower + i as i128)
                .collect::<Vec<_>>();
            lines.push(format!(
                "have _enumerated_values : {} := by omega",
                values
                    .iter()
                    .map(|n| format!("_enumerated_integer = ({n} : ℤ)"))
                    .collect::<Vec<_>>()
                    .join(" ∨ ")
            ));
            if values.len() > 1 {
                lines.push(format!(
                    "rcases _enumerated_values with {}",
                    vec!["_enumerated_value"; values.len()].join(" | ")
                ));
            }
            for (i, value) in values.iter().enumerate() {
                let name = if values.len() == 1 {
                    "_enumerated_values"
                } else {
                    "_enumerated_value"
                };
                let branch = branch(i)?;
                let prefix = if values.len() == 1 { "" } else { "· " };
                let indent = if values.len() == 1 { "" } else { "  " };
                lines.push(format!("{prefix}have {case} : Litex.denote {input} = M.number ({value} : ℂ) := _enumerated_same.trans (congrArg M.number (by norm_num [{name}] : (_enumerated_integer : ℂ) = ({value} : ℂ)))"));
                lines.push(format!(
                    "{indent}exact {}",
                    branch.replace('\n', &format!("\n{indent}"))
                ));
            }
        }
        Ok(format!(
            "(by\n  {}\n)",
            lines.join("\n").replace('\n', "\n  ")
        ))
    }
}
