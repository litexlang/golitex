use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_proper_inclusion_definition(
        &self,
        goal: &AtomicFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (a, b, reverse) = match goal {
            AtomicFact::ProperSubsetFact(f) => (&f.left, &f.right, false),
            AtomicFact::ProperSupersetFact(f) => (&f.left, &f.right, true),
            _ => return Err(LeanCompileError::unsupported("ProperInclusion/Subject")),
        };
        let (lower, upper) = if reverse { (b, a) } else { (a, b) };
        if requirements.len() != 2
            || proofs.len() != 2
            || !matches!(&requirements[0], Fact::AtomicFact(AtomicFact::SubsetFact(f)) if f.left.ir() == lower.ir() && f.right.ir() == upper.ir())
            || !matches!(&requirements[1], Fact::AtomicFact(AtomicFact::NotEqualFact(f)) if f.left.ir() == a.ir() && f.right.ir() == b.ir())
        {
            return Err(LeanCompileError::unsupported("ProperInclusion/Definition"));
        }
        for (requirement, proof) in requirements.iter().zip(proofs) {
            if source_subject(proof)? != *requirement {
                return Err(LeanCompileError::unsupported(
                    "ProperInclusion/ProofSubject",
                ));
            }
        }
        Ok(format!(
            "(And.intro {} {})",
            self.compile_verify(&proofs[0], position)?.1,
            self.compile_verify(&proofs[1], position)?.1
        ))
    }

    pub(super) fn compile_proper_inclusion_inferences(
        &self,
        infer: &crate::store_fact_and_infer::InferAtomicFactResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        use crate::store_fact_and_infer::{
            InferAtomicFactResult, InferProperSubsetFactResult, InferProperSupersetFactResult,
        };
        let (source, stores) = match infer {
            InferAtomicFactResult::ProperSubsetFact(rules) if rules.len() == 1 => {
                let InferProperSubsetFactResult::Definition(p) = &rules[0];
                (p.source_fact_id, [&p.subset, &p.distinct])
            }
            InferAtomicFactResult::ProperSupersetFact(rules) if rules.len() == 1 => {
                let InferProperSupersetFactResult::Definition(p) = &rules[0];
                (p.source_fact_id, [&p.reverse_subset, &p.distinct])
            }
            _ => {
                return Err(LeanCompileError::unsupported(
                    "ProperInclusion/InferenceArity",
                ))
            }
        };
        if source != seed.fact_id() {
            return Err(LeanCompileError::unsupported(
                "ProperInclusion/InferenceSource",
            ));
        }
        let (a, b, reverse) = match seed {
            Fact::AtomicFact(AtomicFact::ProperSubsetFact(f)) => (&f.left, &f.right, false),
            Fact::AtomicFact(AtomicFact::ProperSupersetFact(f)) => (&f.left, &f.right, true),
            _ => {
                return Err(LeanCompileError::unsupported(
                    "ProperInclusion/InferenceFamily",
                ))
            }
        };
        let (lower, upper) = if reverse { (b, a) } else { (a, b) };
        let mut lines = Vec::new();
        for (i, store) in stores.into_iter().enumerate() {
            let prior = SourcePosition {
                before: position.before + i,
                ..*position
            };
            let fact = self.resolve_fact(store.primary_fact_id(), &prior)?;
            self.validate_store(&store.store, &fact)?;
            let valid = match &fact {
                Fact::AtomicFact(AtomicFact::SubsetFact(f)) if i == 0 => {
                    f.left.ir() == lower.ir() && f.right.ir() == upper.ir()
                }
                Fact::AtomicFact(AtomicFact::NotEqualFact(f)) if i == 1 => {
                    f.left.ir() == a.ir() && f.right.ir() == b.ir()
                }
                _ => false,
            };
            if !valid {
                return Err(LeanCompileError::unsupported(
                    "ProperInclusion/InferenceSubject",
                ));
            }
            let proposition = self.fact_proposition(&fact, &prior)?;
            lines.push(self.emit_internal_fact(
                &fact,
                &(proposition, format!("({}).{}", compiled.1, i + 1)),
                &prior,
            )?);
        }
        Ok(lines)
    }

    pub(super) fn compile_known_dvd_zero(
        &self,
        fact: &AtomicFact,
        proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::known_divisibility::KnownZeroRemainderProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let args = atomic_fact_args_ref(fact);
        if !matches!(fact, AtomicFact::DvdFact(_) | AtomicFact::NotDvdFact(_))
            || args.len() != 2
            || args[0].ir() != proof.dividend.ir()
            || args[1].ir() != proof.divisor.ir()
        {
            return Err(LeanCompileError::unsupported("Dvd/ZeroRemainderSubject"));
        }
        let remainder = Obj::IntegerOperator(IntegerOperator::Mod(Mod {
            left: Box::new(proof.dividend.clone()),
            right: Box::new(proof.divisor.clone()),
        }));
        let target = EqualFact {
            fact_id: fact.fact_id(),
            left: remainder.clone(),
            right: Obj::Literal(Literal::Number(Number::new("0".into()))),
            line_file: None,
        };
        let term = self.compile_object_reference(&remainder, position)?;
        let equality = self.compile_equality_search(&target, &proof.zero_remainder, position)?;
        Ok(format!("(Litex.dvdOfModZero {term} {equality})"))
    }

    pub(super) fn compile_closed_number_predicate(
        &self,
        fact: &AtomicFact,
        values: &[&str],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (kind, negative) = match fact {
            AtomicFact::PrimeFact(_) => ("prime", false),
            AtomicFact::NotPrimeFact(_) => ("prime", true),
            AtomicFact::CoprimeFact(_) => ("coprime", false),
            AtomicFact::NotCoprimeFact(_) => ("coprime", true),
            _ => {
                return Err(LeanCompileError::unsupported(
                    "NumberPredicate/CalculationFamily",
                ))
            }
        };
        let args = atomic_fact_args_ref(fact);
        if args.len() != values.len() {
            return Err(LeanCompileError::unsupported(
                "NumberPredicate/CalculationArity",
            ));
        }
        let mut objects = Vec::new();
        let mut integers = Vec::new();
        let mut equalities = Vec::new();
        for (arg, recorded) in args.iter().zip(values) {
            let value = recorded
                .parse::<u64>()
                .map_err(|_| LeanCompileError::unsupported("NumberPredicate/NaturalValue"))?;
            let native = self.compile_numeric_observation(arg, position)?;
            if native.3.as_ref().and_then(EvalRational::to_i128_if_integer)
                != Some(i128::from(value))
            {
                return Err(LeanCompileError::unsupported(
                    "NumberPredicate/CalculationValue",
                ));
            }
            objects.push(self.compile_object_reference(arg, position)?);
            integers.push(format!("({value} : ℕ)"));
            equalities.push(format!(
                "(({}).trans (congrArg M.number (by norm_num : {} = (({value} : ℕ) : ℂ))))",
                native.1, native.0
            ));
        }
        let iff = format!(
            "(Litex.{kind}_iff_of_denote {} {} {})",
            objects.join(" "),
            integers.join(" "),
            equalities.join(" ")
        );
        let native_proof = if kind == "coprime" {
            "(by norm_num [Nat.Coprime])"
        } else {
            "(by norm_num)"
        };
        Ok(if negative {
            format!("((not_congr {iff}).mpr {native_proof})")
        } else {
            format!("({iff}.mpr {native_proof})")
        })
    }
}

pub(super) fn numeric_predicate_domains(fact: &AtomicFact) -> Option<Vec<StandardSet>> {
    Some(match fact {
        AtomicFact::PrimeFact(_) | AtomicFact::NotPrimeFact(_) => vec![StandardSet::N],
        AtomicFact::CoprimeFact(_) | AtomicFact::NotCoprimeFact(_) => {
            vec![StandardSet::N, StandardSet::N]
        }
        AtomicFact::DvdFact(_) | AtomicFact::NotDvdFact(_) => {
            vec![StandardSet::Z, StandardSet::ZStar]
        }
        _ => return None,
    })
}
