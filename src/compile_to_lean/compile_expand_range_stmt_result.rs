use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_by_stmt::ExecExpandRangeStmtResult;
use crate::prelude::*;

pub(super) fn integer_interval_parts(set: &Obj) -> Result<(&Obj, &Obj, bool), LeanCompileError> {
    match set {
        Obj::SetFormer(SetFormer::Range(r)) => Ok((&r.start, &r.end, false)),
        Obj::SetFormer(SetFormer::ClosedRange(r)) => Ok((&r.start, &r.end, true)),
        _ => Err(LeanCompileError::unsupported("IntegerInterval/Subject")),
    }
}

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_interval_integer_endpoint(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<(i128, String), LeanCompileError> {
        let native = self.compile_numeric_observation(object, position)?;
        let value = native
            .3
            .as_ref()
            .and_then(|r| r.to_i128_if_integer())
            .ok_or_else(|| LeanCompileError::unsupported("IntegerInterval/ClosedEndpoint"))?;
        Ok((
            value,
            format!(
                "(({}).trans (congrArg M.number (by norm_num : {} = (({value} : ℤ) : ℂ))))",
                native.1, native.0
            ),
        ))
    }

    pub(in crate::compile_to_lean) fn compile_expand_range_statement(
        &self,
        result: &ExecExpandRangeStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let ExecExpandRangeStmtResult::Success(proof) = result else {
            return Err(LeanCompileError::unsupported("ExpandRange/Failed"));
        };
        let Fact::AtomicFact(AtomicFact::InFact(member)) = source_subject(&proof.membership)?
        else {
            return Err(LeanCompileError::unsupported("ExpandRange/Membership"));
        };
        let (start, end, closed) = integer_interval_parts(&member.set)?;
        let scope = SourcePosition::new(Some(position), SourceOwner::RangeExpansion(proof), 0);
        let (_, member_proof) = self.compile_verify(&proof.membership, &scope)?;
        let formed = SourcePosition::new(
            Some(&scope),
            SourceOwner::Verify(&proof.membership),
            usize::MAX,
        );
        let (lower, hl) = self.compile_interval_integer_endpoint(start, &formed)?;
        let (upper, hu) = self.compile_interval_integer_endpoint(end, &formed)?;
        let count =
            upper
                .checked_sub(lower)
                .and_then(|d| if closed { d.checked_add(1) } else { Some(d) });
        if count.is_none_or(|n| n <= 0 || n > 1024 || n as usize != proof.values.len()) {
            return Err(LeanCompileError::unsupported("ExpandRange/Coverage"));
        }
        let StoreFactResult::OrFact(stored) = &proof.stored.store else {
            return Err(LeanCompileError::unsupported("ExpandRange/Store"));
        };
        let fact = Fact::OrFact(stored.fact.clone());
        if stored.fact.facts.len() != proof.values.len() {
            return Err(LeanCompileError::unsupported("ExpandRange/Branches"));
        }
        let mut values = Vec::new();
        for (i, (value, branch)) in proof.values.iter().zip(&stored.fact.facts).enumerate() {
            let k = lower
                .checked_add(i as i128)
                .ok_or_else(|| LeanCompileError::unsupported("ExpandRange/ValueOverflow"))?;
            if !matches!(value, Obj::Literal(Literal::Number(n)) if n.normalized_value == k.to_string())
                || !matches!(branch, AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(e))
                    if e.left.ir() == member.element.ir() && e.right.ir() == value.ir())
            {
                return Err(LeanCompileError::new("ExpandRange/Values", "The captured values and stored equalities must enumerate the complete source interval in order."));
            }
            values.push(k);
        }
        self.validate_store(&proof.stored.store, &fact)?;
        let range = self.compile_object_reference(&member.set, &formed)?;
        let element = self.compile_object_reference(&member.element, &formed)?;
        let family = if closed { "ClosedRange" } else { "Range" };
        let mut lines = vec![
            format!("let _expanded_range := {range}"),
            format!("obtain ⟨_range_integer, _range_same, _range_lower, _range_upper⟩ := Litex.in{family}Integer _expanded_range {element} ({lower} : ℤ) ({upper} : ℤ) {hl} {hu} {member_proof}"),
            format!("have _range_cases : {} := by omega", values.iter().map(|v| format!("_range_integer = ({v} : ℤ)")).collect::<Vec<_>>().join(" ∨ ")),
        ];
        if values.len() > 1 {
            lines.push(format!(
                "rcases _range_cases with {}",
                vec!["_range_case"; values.len()].join(" | ")
            ));
        }
        for i in 0..values.len() {
            let name = if values.len() == 1 {
                "_range_cases"
            } else {
                "_range_case"
            };
            let mut term =
                format!("(_range_same.trans (congrArg M.number (by norm_num [{name}])))");
            if i + 1 < values.len() {
                term = format!("(Or.inl {term})");
            }
            for _ in 0..i {
                term = format!("(Or.inr {term})");
            }
            lines.push(format!(
                "{}exact {term}",
                if values.len() == 1 { "" } else { "· " }
            ));
        }
        // The expansion itself constructs these integer literals. Their exact
        // values and stored subjects were checked above; there is no source WD
        // search for an intermediate literal that never appeared in the input.
        let proposition = values
            .iter()
            .map(|k| format!("(Litex.Same {element} (Litex.number (M := M) ({k} : ℂ)))"))
            .collect::<Vec<_>>()
            .join(" ∨ ");
        let compiled = (
            proposition,
            format!("(by\n  {}\n)", lines.join("\n").replace('\n', "\n  ")),
        );
        self.emit_by_completed_fact(&fact, compiled, &proof.stored, position, 2, index, local)
    }
}
