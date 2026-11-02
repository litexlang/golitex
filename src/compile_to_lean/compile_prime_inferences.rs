use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::InferPrimeFactResult;

impl LitexToLeanCompiler {
    pub(super) fn compile_prime_inferences(
        &self,
        rules: &[InferPrimeFactResult],
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let Fact::AtomicFact(AtomicFact::PrimeFact(prime)) = seed else {
            return Err(invalid("Seed"));
        };
        let mut lines = Vec::new();
        for (index, rule) in rules.iter().enumerate() {
            let InferPrimeFactResult::Definition(p) = rule;
            if p.source_fact_id != seed.fact_id() {
                return Err(invalid("SeedIdentity"));
            }
            let StoreFactResult::AtomicFact(lower) = &p.lower_bound.store else {
                return Err(invalid("LowerStore"));
            };
            if !matches!(&lower.fact,AtomicFact::LessEqualFact(f)
                if is_two(&f.left) && f.right.ir()==prime.value.ir())
            {
                return Err(invalid("LowerSubject"));
            }
            let StoreFactResult::ForallFact(trial) = &p.trial_divisors.store else {
                return Err(invalid("TrialStore"));
            };
            let bound = validate_trial(&trial.fact, &prime.value)?;
            let lower_fact = Fact::AtomicFact(lower.fact.clone());
            let trial_fact = Fact::ForallFact(trial.fact.clone());
            self.validate_store(&p.lower_bound.store, &lower_fact)?;
            self.validate_store(&p.trial_divisors.store, &trial_fact)?;
            let prior = SourcePosition {
                before: 2 * index,
                ..*position
            };
            let lower_complete = SourcePosition {
                before: 2 * index + 1,
                ..*position
            };
            let trial_complete = SourcePosition {
                before: 2 * index + 2,
                ..*position
            };
            let value = self.compile_object_reference(&prime.value, &prior)?;
            let proposition = format!("Litex.Le (Litex.number (M := M) (2 : ℂ)) {value}");
            let proof = format!("(Litex.primeLowerBound {value} {})", compiled.1);
            lines.push(self.emit_internal_fact(
                &lower_fact,
                &(proposition, proof),
                &lower_complete,
            )?);
            // This constructor is owned by the original prime-definition rule.
            // Its Lean theorem supplies WD; no Verify WD result is manufactured.
            let name = range_name(trial.fact.fact_id);
            let range=format!("(Litex.range (Litex.number (M := M) (2 : ℂ)) {value} (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) (Litex.primeInZ {value} {}))",compiled.1);
            lines.push(format!(
                "{} {name}{} := {range}",
                if trial_complete.is_local() {
                    "let"
                } else {
                    "noncomputable def"
                },
                if trial_complete.is_local() {
                    String::new()
                } else {
                    self.context_header(&trial_complete)?
                }
            ));
            let binder = format!("_value_i{}", bound.id.value());
            let range = if trial_complete.is_local() {
                name
            } else {
                self.context_application(&name, &trial_complete)
            };
            let statement=format!("∀ ({binder} : Litex.Obj (M := M) M.Value), Litex.In {binder} {range} → ¬ (Litex.integerDivisionValue false (Litex.denote {value}) (Litex.denote {binder}) = M.number 0)");
            let proof = format!("(Litex.primeTrialDivisors {value} {})", compiled.1);
            lines.push(self.emit_internal_fact(
                &trial_fact,
                &(statement, proof),
                &trial_complete,
            )?);
        }
        Ok(lines)
    }

    pub(super) fn compile_prime_inferred_subject(
        &self,
        object: &Obj,
        store: &StoreFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        let Some(carrier) = position.prime_trial_carrier(store) else {
            return Ok(None);
        };
        if carrier.ir() != object.ir() {
            return Ok(None);
        }
        let name = range_name(store.primary_fact_id());
        Ok(Some(if position.is_local() {
            name
        } else {
            self.context_application(&name, position)
        }))
    }
}

fn validate_trial<'a>(
    trial: &'a ForallFact,
    prime: &Obj,
) -> Result<&'a BoundName, LeanCompileError> {
    let [group] = trial.typed_parameters.groups.as_slice() else {
        return Err(invalid("TrialGroup"));
    };
    let ([bound], ParamType::Obj(Obj::SetFormer(SetFormer::Range(range)))) =
        (group.params.as_slice(), &group.param_type)
    else {
        return Err(invalid("TrialDomain"));
    };
    let parameter = Obj::Identifier(IdentifierObj::from_bound_name(bound));
    if !is_two(&range.start)
        || range.end.ir() != prime.ir()
        || !trial.dom_facts.is_empty()
        || super::compile_real_set_bounds::contains_parameter(prime, bound.id)
        || !matches!(trial.then_facts.as_slice(),[ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::NotEqualFact(f))]
            if is_exact_zero(&f.right) && matches!(&f.left,Obj::IntegerOperator(IntegerOperator::Mod(m))
                if m.left.ir()==prime.ir() && m.right.ir()==parameter.ir()))
    {
        return Err(invalid("TrialSubject"));
    }
    Ok(bound)
}

fn is_two(object: &Obj) -> bool {
    matches!(object,Obj::Literal(Literal::Number(n)) if n.normalized_value=="2")
}

fn range_name(id: FactId) -> String {
    format!("_prime_trial_range_h{}", id.value())
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("PrimeInference/{stage}"))
}
