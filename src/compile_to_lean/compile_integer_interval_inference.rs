use crate::compile_to_lean::compile_expand_range_stmt_result::integer_interval_parts;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::InferIntegerIntervalBoundsResult;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_integer_interval_inference(
        &self,
        proof: &InferIntegerIntervalBoundsResult,
        closed: bool,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let Fact::AtomicFact(AtomicFact::InFact(source)) = seed else {
            return Err(LeanCompileError::unsupported(
                "IntegerInterval/InferenceSource",
            ));
        };
        let (start, end, source_closed) = integer_interval_parts(&source.set)?;
        if source_closed != closed {
            return Err(LeanCompileError::unsupported(
                "IntegerInterval/InferenceFamily",
            ));
        }
        let positive_start = matches!(start, Obj::Literal(Literal::Number(n))
            if n.normalized_value.parse::<i128>().ok().is_some_and(|k| k > 0));
        if positive_start != proof.positive_membership.is_some() {
            return Err(LeanCompileError::unsupported(
                "IntegerInterval/PositiveInference",
            ));
        }
        let range = self.compile_object_reference(&source.set, position)?;
        let element = self.compile_object_reference(&source.element, position)?;
        let family = if closed { "ClosedRange" } else { "Range" };
        let bounds = format!("(Litex.in{family}Bounds {range} {element} {})", compiled.1);
        let mut declarations = Vec::new();
        let mut ids = std::collections::HashSet::from([source.fact_id]);
        for (index, captured) in proof.stored_conclusions().iter().enumerate() {
            let store = &captured.store;
            let fact = self.resolve_fact(store.primary_fact_id(), position)?;
            self.validate_store(store, &fact)?;
            if !ids.insert(fact.fact_id()) {
                return Err(LeanCompileError::unsupported(
                    "IntegerInterval/InferenceIdentity",
                ));
            }
            let Fact::AtomicFact(atomic) = &fact else {
                return Err(LeanCompileError::unsupported(
                    "IntegerInterval/InferenceConclusion",
                ));
            };
            let valid = match (index, atomic) {
                (0, AtomicFact::InFact(f)) => {
                    f.element.ir() == source.element.ir()
                        && f.set == Obj::StandardSet(StandardSet::Z)
                }
                (1, AtomicFact::LessEqualFact(f)) => {
                    f.left.ir() == start.ir() && f.right.ir() == source.element.ir()
                }
                (2, AtomicFact::LessEqualFact(f)) if closed => {
                    f.left.ir() == source.element.ir() && f.right.ir() == end.ir()
                }
                (2, AtomicFact::LessFact(f)) if !closed => {
                    f.left.ir() == source.element.ir() && f.right.ir() == end.ir()
                }
                (3, AtomicFact::InFact(f)) if positive_start => {
                    f.element.ir() == source.element.ir()
                        && f.set == Obj::StandardSet(StandardSet::NPos)
                }
                (_, AtomicFact::EqualFact(f)) if index == 3 + usize::from(positive_start) => {
                    f.left.ir() == source.element.ir()
                }
                _ => false,
            };
            if !valid {
                return Err(LeanCompileError::unsupported(
                    "IntegerInterval/InferenceConclusion",
                ));
            }
            let formed = SourcePosition::new(
                Some(position),
                SourceOwner::InferredStore(store),
                usize::MAX,
            );
            let term = match index {
                0 => format!("{bounds}.1"),
                1 => format!("{bounds}.2.1"),
                2 => format!("{bounds}.2.2"),
                3 if positive_start => {
                    let (lower, hl) = self.compile_interval_integer_endpoint(start, position)?;
                    format!("(Litex.in{family}Positive {range} {element} ({lower} : ℤ) {hl} (by norm_num) {})", compiled.1)
                }
                _ => {
                    let AtomicFact::EqualFact(equality) = atomic else {
                        unreachable!()
                    };
                    let (lower, hl) = self.compile_interval_integer_endpoint(start, position)?;
                    let (upper, hu) = self.compile_interval_integer_endpoint(end, position)?;
                    let singleton = if closed {
                        Some(lower)
                    } else {
                        lower.checked_add(1)
                    };
                    if singleton != Some(upper)
                        || !matches!(&equality.right,
                        Obj::Literal(Literal::Number(n)) if n.normalized_value == lower.to_string())
                    {
                        return Err(LeanCompileError::unsupported(
                            "IntegerInterval/SingletonConclusion",
                        ));
                    }
                    let right = self.compile_numeric_observation(&equality.right, &formed)?;
                    format!("(by\n  obtain ⟨k, hk, hlo, hhi⟩ := Litex.in{family}Integer {range} {element} ({lower} : ℤ) ({upper} : ℤ) {hl} {hu} {}\n  have heq : k = ({lower} : ℤ) := by omega\n  exact hk.trans ((congrArg M.number (by norm_num [heq] : (k : ℂ) = {})).trans ({}).symm)\n)", compiled.1, right.0, right.1)
                }
            };
            declarations.push(self.emit_internal_fact(
                &fact,
                &(self.fact_proposition(&fact, &formed)?, term),
                &formed,
            )?);
        }
        Ok(declarations)
    }
}
