use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::InferAtomicExceptEqualityResult;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_order_bound_inferences(
        &self,
        rules: &[InferAtomicExceptEqualityResult],
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let mut declarations = Vec::new();
        for (index, rule) in rules.iter().enumerate() {
            let (source_id, bound, value, checks, captured, weak) = match (rule, seed) {
                (
                    InferAtomicExceptEqualityResult::WeakIntegerLowerBoundInN(rule),
                    Fact::AtomicFact(AtomicFact::LessEqualFact(source)),
                ) => (
                    rule.source_fact_id,
                    &source.left,
                    &source.right,
                    vec![&rule.integer_proof, &rule.bound_nonnegative_proof],
                    &rule.derived,
                    true,
                ),
                (
                    InferAtomicExceptEqualityResult::WeakIntegerLowerBoundInN(rule),
                    Fact::AtomicFact(AtomicFact::GreaterEqualFact(source)),
                ) => (
                    rule.source_fact_id,
                    &source.right,
                    &source.left,
                    vec![&rule.integer_proof, &rule.bound_nonnegative_proof],
                    &rule.derived,
                    true,
                ),
                (
                    InferAtomicExceptEqualityResult::StrictLowerBoundPositive(rule),
                    Fact::AtomicFact(AtomicFact::LessFact(source)),
                ) => (
                    rule.source_fact_id,
                    &source.left,
                    &source.right,
                    vec![&rule.bound_nonnegative_proof],
                    &rule.derived,
                    false,
                ),
                (
                    InferAtomicExceptEqualityResult::StrictLowerBoundPositive(rule),
                    Fact::AtomicFact(AtomicFact::GreaterFact(source)),
                ) => (
                    rule.source_fact_id,
                    &source.right,
                    &source.left,
                    vec![&rule.bound_nonnegative_proof],
                    &rule.derived,
                    false,
                ),
                (InferAtomicExceptEqualityResult::WeakIntegerLowerBoundInN(_), _)
                | (InferAtomicExceptEqualityResult::StrictLowerBoundPositive(_), _) => {
                    return Err(LeanCompileError::unsupported(
                        "Inference/OrderBoundSeedFamily",
                    ))
                }
                _ => continue,
            };
            if source_id != seed.fact_id() {
                return Err(LeanCompileError::new(
                    "Inference/OrderBoundSeedIdentity",
                    "The conditional order rule cites another original seed FactId.",
                ));
            }
            let preceding = SourcePosition {
                before: index,
                ..*position
            };
            let current =
                SourcePosition::new(Some(&preceding), SourceOwner::OrderBoundInference(rule), 0);
            let mut checked = Vec::new();
            for (index, proof) in checks.iter().enumerate() {
                let subject = source_subject(proof)?;
                if weak && index == 0 {
                    match subject {
                        Fact::AtomicFact(AtomicFact::InFact(member))
                            if member.element.ir() == value.ir()
                                && member.set == Obj::StandardSet(StandardSet::Z) => {}
                        _ => {
                            return Err(LeanCompileError::new(
                                "Inference/OrderBoundInteger",
                                "The integer certificate describes another value or carrier.",
                            ))
                        }
                    }
                } else {
                    match subject {
                        Fact::AtomicFact(AtomicFact::LessEqualFact(nonnegative)) if is_exact_zero(&nonnegative.left) && nonnegative.right.ir() == bound.ir() => {},
                        Fact::AtomicFact(AtomicFact::GreaterEqualFact(nonnegative)) if is_exact_zero(&nonnegative.right) && nonnegative.left.ir() == bound.ir() => {},
                        _ => return Err(LeanCompileError::new("Inference/OrderBoundNonnegative", "The bound certificate does not prove zero below this exact source operand.")),
                    }
                }
                let prior = SourcePosition {
                    before: index,
                    ..current
                };
                checked.push(self.compile_verify(proof, &prior)?.1);
            }
            let derived = &captured.store;
            let StoreFactResult::AtomicFact(stored) = derived else {
                return Err(LeanCompileError::unsupported(
                    "Inference/OrderBoundConclusion",
                ));
            };
            let fact = Fact::AtomicFact(stored.fact.clone());
            if stored.fact_id != stored.fact.fact_id()
                || self.resolve_fact(stored.fact_id, &current)? != fact
            {
                return Err(LeanCompileError::new(
                    "Inference/OrderBoundIdentity",
                    "The captured derived FactId differs from its actual recorded subject.",
                ));
            }
            let valid = if weak {
                matches!(&stored.fact, AtomicFact::InFact(member) if member.element.ir() == value.ir() && member.set == Obj::StandardSet(StandardSet::N))
            } else {
                matches!(&stored.fact, AtomicFact::LessFact(positive) if is_exact_zero(&positive.left) && positive.right.ir() == value.ir())
            };
            if !valid {
                return Err(LeanCompileError::new(
                    "Inference/OrderBoundConclusion",
                    "The conditional rule derives another exact value, relation or carrier.",
                ));
            }
            let formation = SourcePosition {
                before: checks.len(),
                ..current
            };
            self.validate_store(derived, &fact)?;
            let formed = SourcePosition::new(
                Some(&formation),
                SourceOwner::InferredStore(&captured.store),
                usize::MAX,
            );
            let b = self.compile_object_reference(bound, &formed)?;
            let a = self.compile_object_reference(value, &formed)?;
            let proof = if weak {
                format!(
                    "(Litex.weakIntegerLowerBoundInN {b} {a} {} {} {})",
                    checked[0], checked[1], compiled.1
                )
            } else {
                let zero = match &stored.fact {
                    AtomicFact::LessFact(fact) => {
                        self.compile_object_reference(&fact.left, &formed)?
                    }
                    _ => unreachable!(),
                };
                format!(
                    "(Litex.leLtTrans {zero} {b} {a} {} {})",
                    checked[0], compiled.1
                )
            };
            let emitted = (self.fact_proposition(&fact, &formed)?, proof);
            declarations.push(self.emit_internal_fact(&fact, &emitted, &preceding));
        }
        Ok(declarations)
    }
}
