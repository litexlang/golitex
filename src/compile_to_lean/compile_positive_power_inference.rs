use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferEqualFactPositiveRealPowerResult, InferPositiveRealPowerPositivityResult,
};
use std::collections::HashSet;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_positive_power_inference(
        &self,
        rule: &InferEqualFactPositiveRealPowerResult,
        source: &EqualFact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        if rule.transports.is_empty() || rule.transports.len() > 2 {
            return Err(LeanCompileError::new(
                "Inference/PositivePowerArity",
                "A positive-power inference retains one or two original equality-side transports.",
            ));
        }
        let mut declarations = Vec::new();
        let mut identities = HashSet::new();
        let mut previous_side = None;
        for (index, transport) in rule.transports.iter().enumerate() {
            if transport.source_fact_id != source.fact_id {
                return Err(LeanCompileError::new(
                    "Inference/PositivePowerSeed",
                    "The captured positive-power transport cites another original equality identity.",
                ));
            }
            let (side, target, equality) = if transport.power.ir() == source.left.ir()
                && source.left.ir() != source.right.ir()
            {
                (0, &source.right, compiled.1.clone())
            } else if transport.power.ir() == source.right.ir()
                && source.left.ir() != source.right.ir()
            {
                (1, &source.left, format!("(Eq.symm {})", compiled.1))
            } else {
                return Err(LeanCompileError::new(
                    "Inference/PositivePowerSource",
                    "The captured power must be an exact original equality side with a distinct target.",
                ));
            };
            if previous_side.is_some_and(|prior| prior >= side) {
                return Err(LeanCompileError::new(
                    "Inference/PositivePowerOrder",
                    "The captured transports must retain their original left-then-right order.",
                ));
            }
            previous_side = Some(side);
            let Obj::ArithmeticOperator(ArithmeticOperator::Pow(power)) = &transport.power else {
                return Err(LeanCompileError::new(
                    "Inference/PositivePowerConstructor",
                    "The captured positive source must retain its original power constructor.",
                ));
            };
            let prior_group = SourcePosition::new(
                Some(position),
                SourceOwner::PositivePowerInferences(rule),
                index,
            );
            let prior = SourcePosition::new(
                Some(&prior_group),
                SourceOwner::PositivePowerTransport(transport),
                0,
            );
            let (positive, positive_subject, is_base) = match &transport.positivity {
                InferPositiveRealPowerPositivityResult::BasePositive(proof) => {
                    (proof, power.base.as_ref(), true)
                }
                InferPositiveRealPowerPositivityResult::PowerPositive(proof) => {
                    (proof, &transport.power, false)
                }
            };
            let positive_fact = source_subject(positive)?;
            let Fact::AtomicFact(positive_atomic) = &positive_fact else {
                return Err(LeanCompileError::unsupported(
                    "Inference/PositivePowerPositivityFamily",
                ));
            };
            let (zero, element, strict) = source_order_oriented(positive_atomic)?;
            if !strict || !is_exact_zero(zero) || element.ir() != positive_subject.ir() {
                return Err(LeanCompileError::new(
                    "Inference/PositivePowerPositivitySubject",
                    "The actual strict positivity child must name this exact selected base or power.",
                ));
            }
            let checked_positive = self.compile_verify(positive, &prior)?;
            let positive_name = format!("h_{}", positive_fact.fact_id().value());
            let real_members =
                self.order_real_members_from_known(positive_atomic, &positive_name, &prior)?;
            let positive_real = match source_order_parts(positive_atomic)?.0 {
                SourceOrderKind::Less => real_members.1,
                SourceOrderKind::Greater => real_members.0,
                _ => unreachable!("the original strict comparison was validated"),
            };
            let exponent_stage = SourcePosition { before: 1, ..prior };
            let exponent_fact = source_subject(&transport.exponent_real)?;
            if membership_subject(&exponent_fact, &power.exponent)? != StandardSet::R {
                return Err(LeanCompileError::new(
                    "Inference/PositivePowerExponentSubject",
                    "The actual exponent child must retain this original exponent's R-membership.",
                ));
            }
            let exponent = self.compile_verify(&transport.exponent_real, &exponent_stage)?;
            let exponent_name = format!("h_{}", exponent_fact.fact_id().value());
            let formation = SourcePosition { before: 2, ..prior };
            let power_term = self.compile_object_reference(&transport.power, &formation)?;
            let target_term = self.compile_object_reference(target, &formation)?;
            let (power_positive, power_real) = if is_base {
                (
                    format!("(Litex.powStructuralPositiveOfPositive {power_term} {positive_name})"),
                    format!("(Litex.powStructuralInR {power_term} {positive_real})"),
                )
            } else {
                (positive_name.clone(), positive_real)
            };
            let captured = &transport.derived;
            let StoreFactResult::AtomicFact(stored) = &captured.store else {
                return Err(LeanCompileError::unsupported(
                    "Inference/PositivePowerConclusionFamily",
                ));
            };
            let AtomicFact::InFact(member) = &stored.fact else {
                return Err(LeanCompileError::unsupported(
                    "Inference/PositivePowerConclusionFamily",
                ));
            };
            if member.element.ir() != target.ir()
                || member.set != Obj::StandardSet(StandardSet::RPos)
            {
                return Err(LeanCompileError::new(
                    "Inference/PositivePowerConclusionSubject",
                    "The direct store must retain R+ membership of the original equality's other side.",
                ));
            }
            let fact = Fact::AtomicFact(stored.fact.clone());
            if !identities.insert(captured.primary_fact_id())
                || self.resolve_fact(captured.primary_fact_id(), &formation)? != fact
            {
                return Err(LeanCompileError::new(
                    "Inference/PositivePowerConclusionIdentity",
                    "The captured membership store differs from its exact original identity.",
                ));
            }
            self.validate_store(&captured.store, &fact)?;
            let formed = SourcePosition::new(
                Some(&formation),
                SourceOwner::InferredStore(&captured.store),
                usize::MAX,
            );
            let set = standard_term(&StandardSet::RPos)?;
            let proof = format!(
                "(by\n  have {positive_name} : {} := {}\n  have {exponent_name} : {} := {}\n  exact Litex.inOfSame {power_term} {target_term} {set} {set} {equality} (Litex.sameRefl {set}) (Litex.inRPos_intro {power_term} {power_real} {power_positive})\n)",
                checked_positive.0, checked_positive.1, exponent.0, exponent.1,
            );
            let conclusion = (self.fact_proposition(&fact, &formed)?, proof);
            declarations.push(self.emit_internal_fact(&fact, &conclusion, &formed)?);
        }
        Ok(declarations)
    }
}
